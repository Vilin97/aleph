"""Recover proofs from Aleph requests whose CLI poller timed out.

The `alephprover prove` CLI has a hardcoded ~28-min poll timeout that
ignores `--time-budget`. For long-running requests, the server keeps
working but the local CLI exits without applying the proof. This module
polls each request via `alephprover status` and, once complete,
extracts the modified `Submission.lean` (and `Submission/`) from the
returned `prover_result.zip` into the workspace, then runs build +
axiom check and writes a row to `results/results.csv`.

Usage:

    python -m harness.recover \
        finite_graph_ramsey_theorem=093a5d1e-... \
        oppenheim_inequality=d05df5d3-... \
        cyclotomic_integer_house_le_two=54910e96-... \
        gleason_theorem_finite=3df8d18c-... \
        contractibleSpace_houseWithTwoRooms=d4966fa0-...
"""

from __future__ import annotations

import argparse
import dataclasses
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
POLL_INTERVAL_S = 60
POLL_TIMEOUT_S = 6 * 3600  # 6 hours absolute


def cli_status(request_id: str, *, api_key: str) -> tuple[str, str]:
    """Return (status_word, full_text). status_word ∈ {queued, running, completed, failed, cancelled}."""
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


def cli_download(request_id: str, dest_zip: pathlib.Path, *, api_key: str) -> None:
    DOWNLOADS.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "PROVER_API_KEY": api_key}
    proc = subprocess.run(
        ["alephprover", "download", request_id, "-o", str(dest_zip)],
        env=env,
        capture_output=True,
        text=True,
        timeout=300,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"download failed for {request_id}:\n{proc.stdout}\n{proc.stderr}"
        )


def apply_zip_to_workspace(zip_path: pathlib.Path, workspace: pathlib.Path) -> list[str]:
    """Overwrite Submission.lean (+ Submission/ tree) in `workspace` from `zip_path`.

    Returns the list of files that were extracted/overwritten. Other files
    in the zip (Challenge.lean, Solution.lean, lakefile.toml, lake-manifest)
    are intentionally NOT touched — those belong to the trusted workspace
    layout and the submission rules forbid editing them.
    """
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
    """Pull lemmas-progress and cost from the prove stage."""
    out = {"lemmas": "", "cost_credits": "", "stage_seconds": "", "status_word": ""}
    m = re.search(r"^Status:\s+(\w+)", status_text, re.M)
    if m:
        out["status_word"] = m.group(1)
    m = re.search(r"Lemmas:\s*([^|]+?)\s*\|\s*Cost:\s*([\d.]+)\s*credits", status_text)
    if m:
        out["lemmas"] = m.group(1).strip()
        out["cost_credits"] = m.group(2)
    m = re.search(r"\[\+\]\s+prove:\s+completed\s+\((\d+)s\)", status_text)
    if m:
        out["stage_seconds"] = m.group(1)
    return out


def recover_one(
    problem: manifest.Problem,
    request_id: str,
    *,
    api_key: str,
) -> dict:
    ws = LEAN_EVAL / "workspaces" / problem.id
    if not ws.is_dir():
        raise RuntimeError(f"missing workspace {ws}")

    print(f"[{problem.id}] polling {request_id}...", flush=True)
    deadline = time.monotonic() + POLL_TIMEOUT_S
    last_text = ""
    while True:
        status_word, text = cli_status(request_id, api_key=api_key)
        last_text = text
        if status_word in {"completed", "failed", "cancelled"}:
            print(f"[{problem.id}]   final status={status_word}", flush=True)
            break
        info = parse_message(text)
        print(
            f"[{problem.id}]   status={status_word} lemmas={info['lemmas']} cost={info['cost_credits']} (sleeping {POLL_INTERVAL_S}s)",
            flush=True,
        )
        if time.monotonic() > deadline:
            print(f"[{problem.id}]   POLL DEADLINE EXCEEDED ({POLL_TIMEOUT_S/3600:.1f}h)", flush=True)
            break
        time.sleep(POLL_INTERVAL_S)

    info = parse_message(last_text)
    applied = False
    extracted_files: list[str] = []

    if info["status_word"] == "completed":
        zip_path = DOWNLOADS / f"{problem.id}.zip"
        try:
            cli_download(request_id, zip_path, api_key=api_key)
            extracted_files = apply_zip_to_workspace(zip_path, ws)
            applied = bool(extracted_files)
            print(f"[{problem.id}]   applied {len(extracted_files)} file(s): {extracted_files}", flush=True)
        except Exception as e:
            print(f"[{problem.id}]   download/apply error: {e!r}", flush=True)

    # Make sure mathlib oleans are present for build
    if not (ws / ".lake" / "packages" / "mathlib").is_dir():
        print(f"[{problem.id}]   lake update (clones mathlib)...", flush=True)
        subprocess.run(["lake", "update"], cwd=str(ws), check=False)
    print(f"[{problem.id}]   cache get...", flush=True)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=str(ws), check=False)

    print(f"[{problem.id}]   lake build...", flush=True)
    build = ws_mod.build(ws)
    print(f"[{problem.id}]   build_ok={build.ok} used_sorry={build.used_sorry}", flush=True)

    ax_results = {}
    if build.ok and not build.used_sorry:
        for h in problem.holes:
            ax = ws_mod.axiom_check(ws, hole=h)
            ax_results[h] = ax
            print(f"[{problem.id}]   axioms {h}: ok={ax.ok} {ax.axioms}", flush=True)

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
            "status_text": last_text,
            "applied_files": extracted_files,
            "build": dataclasses.asdict(build),
            "axioms": {h: dataclasses.asdict(a) for h, a in ax_results.items()},
            "succeeded": all(r["succeeded"] for r in rows) if rows else False,
        },
    )
    return {"problem": problem.id, "rows": rows, "status": info["status_word"]}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="recover")
    ap.add_argument("pairs", nargs="+", help="problem_id=request_id")
    args = ap.parse_args(argv)

    api_key = run_eval.load_env()
    problems = {p.id: p for p in manifest.load(LEAN_EVAL / "manifests" / "problems.toml")}

    targets = []
    for spec in args.pairs:
        if "=" not in spec:
            print(f"bad pair {spec!r}, expected problem_id=request_id", file=sys.stderr)
            return 2
        pid, _, rid = spec.partition("=")
        if pid not in problems:
            print(f"unknown problem id {pid!r}", file=sys.stderr)
            return 2
        targets.append((problems[pid], rid))

    summaries = []
    for p, rid in targets:
        try:
            summaries.append(recover_one(p, rid, api_key=api_key))
        except Exception as e:
            print(f"[{p.id}] recover ERROR: {e!r}", flush=True)
            summaries.append({"problem": p.id, "rows": [], "status": "error"})

    print("\n=== recovery summary ===")
    for s in summaries:
        passed = sum(1 for r in s["rows"] if r["succeeded"])
        total = len(s["rows"])
        print(f"  {s['problem']:<40} status={s['status']:<10} {passed}/{total} hole(s) succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
