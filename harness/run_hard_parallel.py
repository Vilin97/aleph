"""Submit the 5 hard problems in parallel at full budget.

Per-problem flow:
  1. Ensure `workspaces/<id>` exists (start-problem + lake update + cache get).
  2. Reset `Submission.lean` (and `Submission/`) to the pristine version from
     `generated/<id>/`, so Aleph starts from the original `:= by sorry`.
  3. `alephprover prove Submission.lean <hole>` with default budgets (no
     `--time-budget` / `--cost-budget` flags ⇒ server uses 900 min / 50 cred).
     All 5 are launched concurrently (Python subprocess.Popen).
  4. After every CLI process exits, build + axiom-check each workspace and
     append a row to `results/results.csv`.

Logs land in `results/hard-<id>.log`. Re-run is idempotent: it always resets
Submission.lean before submitting.
"""

from __future__ import annotations

import csv
import dataclasses
import os
import pathlib
import shutil
import subprocess
import sys
import time

from . import aleph, manifest, run_eval, workspace as ws_mod


HARD_IDS = [
    "finite_graph_ramsey_theorem",
    "oppenheim_inequality",
    "cyclotomic_integer_house_le_two",
    "gleason_theorem_finite",
    "contractibleSpace_houseWithTwoRooms",
]

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_EVAL = REPO_ROOT / "lean-eval"
RESULTS = REPO_ROOT / "results"


def reset_workspace(problem_id: str) -> pathlib.Path:
    gen = LEAN_EVAL / "generated" / problem_id
    ws = LEAN_EVAL / "workspaces" / problem_id

    if not ws.is_dir():
        subprocess.run(
            ["lake", "exe", "lean-eval", "start-problem", problem_id],
            cwd=str(LEAN_EVAL),
            check=True,
        )

    # Reset Submission.lean to the pristine stub
    shutil.copy2(gen / "Submission.lean", ws / "Submission.lean")
    # Reset Submission/ helper dir if present
    if (gen / "Submission").is_dir():
        if (ws / "Submission").is_dir():
            shutil.rmtree(ws / "Submission")
        shutil.copytree(gen / "Submission", ws / "Submission")

    return ws


def main() -> int:
    api_key = run_eval.load_env()
    problems = {p.id: p for p in manifest.load(LEAN_EVAL / "manifests" / "problems.toml")}

    chosen = [problems[pid] for pid in HARD_IDS]
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "raw").mkdir(exist_ok=True)

    # 1) Reset all workspaces (sequential, fast — copies a few files)
    workspaces: dict[str, pathlib.Path] = {}
    for p in chosen:
        ws = reset_workspace(p.id)
        workspaces[p.id] = ws
        print(f"[setup] {p.id}: workspace ready at {ws}", flush=True)

    # 2) Launch all 5 prove calls in parallel
    procs: dict[str, dict] = {}
    env = {**os.environ, "PROVER_API_KEY": api_key}
    t_global = time.monotonic()
    for p in chosen:
        ws = workspaces[p.id]
        # Single-hole problems
        hole = p.holes[0]
        log_path = RESULTS / f"hard-{p.id}.log"
        log_f = log_path.open("w")
        proc = subprocess.Popen(
            ["alephprover", "prove", "Submission.lean", hole, "-v"],
            cwd=str(ws),
            env=env,
            stdout=log_f,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        procs[p.id] = {
            "proc": proc,
            "log_path": log_path,
            "log_f": log_f,
            "ws": ws,
            "hole": hole,
            "started": time.monotonic(),
        }
        print(f"[launch] {p.id}: pid={proc.pid} -> {log_path}", flush=True)

    print(f"\nAll {len(procs)} prove calls launched. Waiting for completion...\n", flush=True)

    # 3) Wait for all
    pending = set(procs.keys())
    while pending:
        time.sleep(30)
        for pid in list(pending):
            entry = procs[pid]
            rc = entry["proc"].poll()
            if rc is not None:
                pending.remove(pid)
                entry["log_f"].close()
                elapsed = time.monotonic() - entry["started"]
                # Tail last lines for status
                try:
                    log_text = entry["log_path"].read_text()
                except Exception:
                    log_text = ""
                applied = "Proof applied successfully" in log_text
                # Try extract request id
                req_id = None
                for line in log_text.splitlines():
                    if "Request ID:" in line:
                        req_id = line.split("Request ID:", 1)[1].strip()
                        break
                entry.update(
                    {"rc": rc, "elapsed_s": elapsed, "applied": applied, "request_id": req_id}
                )
                print(
                    f"[done ] {pid}: rc={rc} applied={applied} request={req_id} elapsed={elapsed/60:.1f}m  ({len(pending)} pending)",
                    flush=True,
                )

    # 4) Build + axiom check each (can parallelize, but build is CPU-heavy; do sequentially)
    print("\n=== verifying each workspace ===\n", flush=True)
    rows = []
    for p in chosen:
        entry = procs[p.id]
        ws = entry["ws"]
        # Ensure deps available for build
        if not (ws / ".lake" / "packages" / "mathlib").is_dir():
            print(f"[verify] {p.id}: lake update (clones mathlib, slow)...", flush=True)
            subprocess.run(["lake", "update"], cwd=str(ws), check=False)
        print(f"[verify] {p.id}: cache get...", flush=True)
        subprocess.run(["lake", "exe", "cache", "get"], cwd=str(ws), check=False)
        print(f"[verify] {p.id}: lake build...", flush=True)
        build = ws_mod.build(ws)
        print(f"[verify] {p.id}: build_ok={build.ok} used_sorry={build.used_sorry}", flush=True)

        ax_results: dict[str, ws_mod.AxiomResult] = {}
        if build.ok and not build.used_sorry:
            for h in p.holes:
                ax = ws_mod.axiom_check(ws, hole=h)
                ax_results[h] = ax
                print(f"[verify] {p.id}:   axioms {h}: ok={ax.ok} {ax.axioms}", flush=True)

        timestamp = time.strftime("%Y-%m-%dT%H:%M:%S")
        any_failed = False
        for h in p.holes:
            ax = ax_results.get(h)
            succeeded = bool(
                entry["applied"] and build.ok and not build.used_sorry and ax is not None and ax.ok
            )
            if not succeeded:
                any_failed = True
            row = {
                "timestamp": timestamp,
                "problem_id": p.id,
                "title": p.title,
                "test": p.test,
                "hole": h,
                "request_id": entry["request_id"] or "",
                "applied": entry["applied"],
                "build_ok": build.ok,
                "build_sorry": build.used_sorry,
                "axiom_ok": ax.ok if ax else False,
                "axioms": ";".join(ax.axioms) if ax else "",
                "succeeded": succeeded,
                "elapsed_prove_s": f"{entry['elapsed_s']:.1f}",
                "elapsed_total_s": f"{(time.monotonic() - t_global):.1f}",
                "time_budget_min": "default",
                "cost_budget": "default",
            }
            run_eval.append_row(row)
            rows.append(row)

        run_eval.write_raw(
            p.id,
            {
                "problem": dataclasses.asdict(p),
                "workspace": str(ws),
                "request_id": entry["request_id"],
                "applied": entry["applied"],
                "elapsed_prove_s": entry["elapsed_s"],
                "build": dataclasses.asdict(build),
                "axioms": {h: dataclasses.asdict(a) for h, a in ax_results.items()},
                "succeeded": not any_failed,
            },
        )

    successes = sum(1 for r in rows if r["succeeded"])
    print(f"\n=== summary: {successes}/{len(rows)} holes succeeded across {len(chosen)} problems ===")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
