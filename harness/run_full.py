"""Full-sweep runner: every theorem-only lean-eval problem, in parallel.

Pipeline:

1. Read the manifest, drop problems that have any non-`theorem` hole and any
   problem id in EXCLUDE.
2. For each remaining problem:
     - `lake exe lean-eval start-problem <id>` (creates workspaces/<id>)
     - reset Submission.lean / Submission/ from generated/<id>/ (pristine)
     - symlink workspaces/<id>/.lake/packages -> lean-eval/.shared-lake/packages
       (all 57 workspaces pin the same Mathlib + lake-manifest, so this is safe)
3. Submit every prove call concurrently with `alephprover prove --no-poll` —
   server-side queue handles execution.
4. Recovery loop: poll `alephprover status <request_id>` for each. As soon as
   a request hits `completed`, download `prover_result.zip`, extract Submission
   files into the workspace, run `lake build` + `#print axioms` and append a
   row to `results/results.csv`.
5. Print a summary and exit.

Logs land in `results/full-<id>.log` (per-problem submit log) and
`results/full.log` (orchestrator log).
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time
import zipfile

from . import manifest, run_eval, workspace as ws_mod


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_EVAL = REPO_ROOT / "lean-eval"
RESULTS = REPO_ROOT / "results"
DOWNLOADS = RESULTS / "downloads"
SHARED_PACKAGES = LEAN_EVAL / ".shared-lake" / "packages"

# Problems already exercised in the smoke run, regardless of pass/fail —
# the user asked to skip them.
EXCLUDE: set[str] = {
    "two_plus_two",
    "ci_regenerate_main_check",
    "list_append_singleton_length",
    "def_hole_example",
    "instance_hole_example",
    "finite_graph_ramsey_theorem",
    "oppenheim_inequality",
    "cyclotomic_integer_house_le_two",
    "gleason_theorem_finite",
    "contractibleSpace_houseWithTwoRooms",
}

POLL_INTERVAL_S = 60
POLL_TIMEOUT_S = 24 * 3600


def all_holes_theorems(problem_id: str) -> bool:
    holes_json = LEAN_EVAL / "generated" / problem_id / "holes.json"
    if not holes_json.is_file():
        return False
    data = json.loads(holes_json.read_text())
    return all(h.get("kind") == "theorem" for h in data.get("holes", []))


def setup_workspace(problem_id: str) -> pathlib.Path:
    """Make workspaces/<id> ready for an Aleph submit + a fast local build.

    Uses a shared `.lake/packages` symlink so we don't clone Mathlib per problem.
    Resets Submission files to the pristine `generated/<id>/` versions.
    """
    gen = LEAN_EVAL / "generated" / problem_id
    ws = LEAN_EVAL / "workspaces" / problem_id

    if not ws.is_dir():
        subprocess.run(
            ["lake", "exe", "lean-eval", "start-problem", problem_id],
            cwd=str(LEAN_EVAL),
            check=True,
        )

    # Symlink shared deps. If a real .lake/packages dir already exists, leave it.
    lake_dir = ws / ".lake"
    lake_dir.mkdir(exist_ok=True)
    pkgs = lake_dir / "packages"
    if pkgs.is_symlink():
        pass  # already pointing somewhere
    elif pkgs.is_dir():
        pass  # real dir from a previous run
    else:
        pkgs.symlink_to(SHARED_PACKAGES)

    # Reset Submission.lean + Submission/ to pristine
    shutil.copy2(gen / "Submission.lean", ws / "Submission.lean")
    if (gen / "Submission").is_dir():
        if (ws / "Submission").is_dir():
            shutil.rmtree(ws / "Submission")
        shutil.copytree(gen / "Submission", ws / "Submission")

    return ws


def submit_no_poll(workspace: pathlib.Path, *, hole: str, api_key: str, log_path: pathlib.Path) -> str | None:
    env = {**os.environ, "PROVER_API_KEY": api_key}
    log_f = log_path.open("w")
    try:
        proc = subprocess.run(
            ["alephprover", "prove", "Submission.lean", hole, "--no-poll", "-v"],
            cwd=str(workspace),
            env=env,
            stdout=log_f,
            stderr=subprocess.STDOUT,
            timeout=300,
        )
    finally:
        log_f.close()
    text = log_path.read_text()
    m = re.search(r"Request ID:\s*([0-9a-f-]+)", text, re.I)
    return m.group(1) if m else None


def cli_status(request_id: str, *, api_key: str) -> tuple[str, str]:
    env = {**os.environ, "PROVER_API_KEY": api_key}
    proc = subprocess.run(
        ["alephprover", "status", request_id],
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )
    text = proc.stdout + proc.stderr
    m = re.search(r"^Status:\s+(\w+)", text, re.M)
    return (m.group(1) if m else "unknown", text)


def cli_download(request_id: str, dest: pathlib.Path, *, api_key: str) -> None:
    DOWNLOADS.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "PROVER_API_KEY": api_key}
    proc = subprocess.run(
        ["alephprover", "download", request_id, "-o", str(dest)],
        env=env,
        capture_output=True,
        text=True,
        timeout=300,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"download failed: {proc.stdout}\n{proc.stderr}")


def apply_zip_to_workspace(zip_path: pathlib.Path, workspace: pathlib.Path) -> list[str]:
    written: list[str] = []
    with zipfile.ZipFile(zip_path) as zf:
        for info in zf.infolist():
            name = info.filename
            if name == "Submission.lean" or name.startswith("Submission/"):
                target = workspace / name
                target.parent.mkdir(parents=True, exist_ok=True)
                with zf.open(info) as src, target.open("wb") as dst:
                    dst.write(src.read())
                written.append(name)
    return written


def parse_message(status_text: str) -> dict:
    out = {"lemmas": "", "cost_credits": "", "stage_seconds": "", "status_word": ""}
    m = re.search(r"^Status:\s+(\w+)", status_text, re.M)
    if m:
        out["status_word"] = m.group(1)
    m = re.search(r"Lemmas:\s*([^|]+?)\s*\|\s*Cost:\s*([\d.]+)", status_text)
    if m:
        out["lemmas"] = m.group(1).strip()
        out["cost_credits"] = m.group(2)
    m = re.search(r"\[\+\]\s+prove:\s+completed\s+\((\d+)s\)", status_text)
    if m:
        out["stage_seconds"] = m.group(1)
    return out


def verify_and_record(
    problem: manifest.Problem,
    request_id: str,
    status_text: str,
    *,
    applied: bool,
) -> dict:
    ws = LEAN_EVAL / "workspaces" / problem.id
    print(f"[{problem.id}] lake build...", flush=True)
    build = ws_mod.build(ws)
    print(f"[{problem.id}]   build_ok={build.ok} used_sorry={build.used_sorry}", flush=True)

    ax_results = {}
    if build.ok and not build.used_sorry:
        for h in problem.holes:
            ax = ws_mod.axiom_check(ws, hole=h)
            ax_results[h] = ax
            print(f"[{problem.id}]   axioms {h}: ok={ax.ok} {ax.axioms}", flush=True)

    info = parse_message(status_text)
    timestamp = time.strftime("%Y-%m-%dT%H:%M:%S")
    rows = []
    for h in problem.holes:
        ax = ax_results.get(h)
        succeeded = bool(applied and build.ok and not build.used_sorry and ax is not None and ax.ok)
        row = {
            "timestamp": timestamp,
            "problem_id": problem.id,
            "title": problem.title,
            "test": problem.test,
            "hole": h,
            "request_id": request_id,
            "applied": applied,
            "build_ok": build.ok,
            "build_sorry": build.used_sorry,
            "axiom_ok": ax.ok if ax else False,
            "axioms": ";".join(ax.axioms) if ax else "",
            "succeeded": succeeded,
            "elapsed_prove_s": info.get("stage_seconds", ""),
            "elapsed_total_s": "",
            "time_budget_min": "default",
            "cost_budget": info.get("cost_credits", "default"),
        }
        run_eval.append_row(row)
        rows.append(row)

    run_eval.write_raw(
        problem.id,
        {
            "problem": dataclasses.asdict(problem),
            "request_id": request_id,
            "applied": applied,
            "build": dataclasses.asdict(build),
            "axioms": {h: dataclasses.asdict(a) for h, a in ax_results.items()},
            "succeeded": all(r["succeeded"] for r in rows) if rows else False,
        },
    )

    # Archive the proof artifact regardless of success
    proofs_dir = RESULTS / "proofs" / problem.id
    proofs_dir.mkdir(parents=True, exist_ok=True)
    if (ws / "Submission.lean").is_file():
        shutil.copy2(ws / "Submission.lean", proofs_dir / "Submission.lean")
    if (ws / "Submission").is_dir():
        if (proofs_dir / "Submission").is_dir():
            shutil.rmtree(proofs_dir / "Submission")
        shutil.copytree(ws / "Submission", proofs_dir / "Submission")

    return {"problem": problem.id, "rows": rows, "succeeded": all(r["succeeded"] for r in rows)}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="run_full")
    ap.add_argument("--limit", type=int, default=None, help="cap problems (debug)")
    args = ap.parse_args(argv)

    api_key = run_eval.load_env()
    problems = manifest.load(LEAN_EVAL / "manifests" / "problems.toml")

    if not SHARED_PACKAGES.is_dir():
        print(f"error: shared packages not found at {SHARED_PACKAGES}", file=sys.stderr)
        return 2

    targets = [p for p in problems if p.id not in EXCLUDE and all_holes_theorems(p.id)]
    if args.limit:
        targets = targets[: args.limit]

    print(f"running {len(targets)} problem(s):")
    for p in targets:
        print(f"  - {p.id}  holes={list(p.holes)}")

    # Phase 1: setup all workspaces (sequential, fast — symlink + file copies)
    for p in targets:
        ws = setup_workspace(p.id)
        print(f"[setup] {p.id}: workspace ready", flush=True)

    # Phase 2: submit all in parallel via subprocess.Popen with --no-poll.
    # Each submit is small (~10s) so we use a small thread pool to keep CPU sane.
    print(f"\n=== submitting {len(targets)} prove calls (--no-poll) ===\n", flush=True)
    request_ids: dict[str, str] = {}
    procs = []
    for p in targets:
        ws = LEAN_EVAL / "workspaces" / p.id
        log_path = RESULTS / f"full-{p.id}.log"
        env = {**os.environ, "PROVER_API_KEY": api_key}
        log_f = log_path.open("w")
        proc = subprocess.Popen(
            ["alephprover", "prove", "Submission.lean", p.holes[0], "--no-poll", "-v"],
            cwd=str(ws),
            env=env,
            stdout=log_f,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        procs.append((p, proc, log_path, log_f))

    for p, proc, log_path, log_f in procs:
        proc.wait()
        log_f.close()
        text = log_path.read_text()
        m = re.search(r"Request ID:\s*([0-9a-f-]+)", text, re.I)
        if m:
            rid = m.group(1)
            request_ids[p.id] = rid
            print(f"[submit] {p.id}: rid={rid}", flush=True)
        else:
            print(f"[submit] {p.id}: NO REQUEST ID, see {log_path}", flush=True)

    print(f"\nSubmitted {len(request_ids)}/{len(targets)} requests.\n", flush=True)

    # Persist a snapshot we can resume from
    (RESULTS / "full-requests.json").write_text(
        json.dumps({"timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"), "request_ids": request_ids}, indent=2)
    )

    # Phase 3: poll each request until completed, then verify+record
    pending = dict(request_ids)
    deadline = time.monotonic() + POLL_TIMEOUT_S
    summaries = []
    while pending:
        time.sleep(POLL_INTERVAL_S)
        if time.monotonic() > deadline:
            print(f"poll deadline exceeded; {len(pending)} still pending", flush=True)
            break
        for pid in list(pending):
            rid = pending[pid]
            try:
                status_word, text = cli_status(rid, api_key=api_key)
            except Exception as e:
                print(f"[{pid}] status query error: {e!r}", flush=True)
                continue
            if status_word in {"queued", "running"}:
                info = parse_message(text)
                print(
                    f"[{pid}] running lemmas={info['lemmas']} cost={info['cost_credits']}",
                    flush=True,
                )
                continue
            del pending[pid]
            print(f"[{pid}] final status={status_word} ({len(pending)} pending)", flush=True)
            problem = next(p for p in targets if p.id == pid)
            applied = False
            if status_word == "completed":
                try:
                    zip_path = DOWNLOADS / f"{pid}.zip"
                    cli_download(rid, zip_path, api_key=api_key)
                    apply_zip_to_workspace(zip_path, LEAN_EVAL / "workspaces" / pid)
                    applied = True
                except Exception as e:
                    print(f"[{pid}] download/apply error: {e!r}", flush=True)
            try:
                summaries.append(verify_and_record(problem, rid, text, applied=applied))
            except Exception as e:
                print(f"[{pid}] verify error: {e!r}", flush=True)

    successes = sum(1 for s in summaries if s["succeeded"])
    print(f"\n=== full sweep summary: {successes}/{len(summaries)} succeeded ===")
    for s in summaries:
        print(f"  {s['problem']:<45} {'OK' if s['succeeded'] else 'fail'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
