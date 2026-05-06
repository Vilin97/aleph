"""Drive Aleph over lean-eval problems and record results.

Usage:

    # smoke set: 3 test=true + 5 sampled test=false problems
    python -m harness.run_eval --smoke

    # one problem
    python -m harness.run_eval --problem two_plus_two

    # everything
    python -m harness.run_eval --all

Results land in `results/results.csv` (one row per hole) and per-problem raw
logs in `results/raw/<problem-id>.json`. Re-running skips problems that have
a `succeeded=true` row unless `--retry` is given.
"""

from __future__ import annotations

import argparse
import csv
import dataclasses
import json
import os
import pathlib
import random
import sys
import time
from typing import Iterable

from . import aleph, manifest, workspace as ws_mod


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_EVAL = REPO_ROOT / "lean-eval"
RESULTS_DIR = REPO_ROOT / "results"
RAW_DIR = RESULTS_DIR / "raw"
CSV_PATH = RESULTS_DIR / "results.csv"

CSV_FIELDS = [
    "timestamp",
    "problem_id",
    "title",
    "test",
    "hole",
    "request_id",
    "applied",
    "build_ok",
    "build_sorry",
    "axiom_ok",
    "axioms",
    "succeeded",
    "elapsed_prove_s",
    "elapsed_total_s",
    "time_budget_min",
    "cost_budget",
]

DEFAULT_TIME_BUDGET_MIN = 30
DEFAULT_COST_BUDGET = 5.0


def load_env() -> str:
    """Load PROVER_API_KEY from .env or env."""
    key = os.environ.get("PROVER_API_KEY")
    if key:
        return key
    env_file = REPO_ROOT / ".env"
    if env_file.is_file():
        for line in env_file.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            k, _, v = line.partition("=")
            if k.strip() == "PROVER_API_KEY":
                return v.strip().strip("'\"")
    print("error: PROVER_API_KEY not set (env or .env)", file=sys.stderr)
    sys.exit(2)


def select_smoke(problems: list[manifest.Problem], *, seed: int = 0) -> list[manifest.Problem]:
    """3 test=true + 5 randomly sampled test=false."""
    test = [p for p in problems if p.test]
    main = [p for p in problems if not p.test]
    rng = random.Random(seed)
    sampled = rng.sample(main, k=min(5, len(main)))
    # Deterministic order: test=true first, then sampled in manifest order
    sampled_set = {p.id for p in sampled}
    sampled_in_order = [p for p in problems if p.id in sampled_set]
    return test + sampled_in_order


def already_done(problem_id: str) -> bool:
    if not CSV_PATH.exists():
        return False
    with CSV_PATH.open() as f:
        for row in csv.DictReader(f):
            if row["problem_id"] == problem_id and row["succeeded"] == "True":
                return True
    return False


def append_row(row: dict) -> None:
    RESULTS_DIR.mkdir(exist_ok=True)
    new_file = not CSV_PATH.exists()
    with CSV_PATH.open("a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        if new_file:
            w.writeheader()
        # Coerce all values to strings/None for csv
        w.writerow({k: row.get(k) for k in CSV_FIELDS})


def write_raw(problem_id: str, payload: dict) -> None:
    RAW_DIR.mkdir(parents=True, exist_ok=True)
    (RAW_DIR / f"{problem_id}.json").write_text(json.dumps(payload, indent=2))


def run_one(
    problem: manifest.Problem,
    *,
    api_key: str,
    time_budget_min: int,
    cost_budget: float,
    skip_setup: bool = False,
) -> dict:
    """Run Aleph on every hole in `problem`, then build + axiom check.

    Returns a summary dict (also written to results/raw/<id>.json).
    """
    t0 = time.monotonic()
    print(f"[{problem.id}] setup workspace...", flush=True)
    if skip_setup:
        ws_dir = LEAN_EVAL / "workspaces" / problem.id
        if not ws_dir.is_dir():
            ws_dir = ws_mod.ensure_workspace(lean_eval_root=LEAN_EVAL, problem_id=problem.id)
    else:
        ws_dir = ws_mod.ensure_workspace(lean_eval_root=LEAN_EVAL, problem_id=problem.id)

    # Skip the prove call if the Submission file is already free of `sorry` —
    # avoids re-billing on workspaces that were proved in a previous run.
    sub_path = ws_dir / "Submission.lean"
    submission_text = sub_path.read_text() if sub_path.is_file() else ""
    skip_prove = "sorry" not in submission_text

    prove_results: list[aleph.ProveResult] = []
    for hole in problem.holes:
        if skip_prove:
            print(f"[{problem.id}] skip prove {hole} (Submission.lean has no `sorry`)", flush=True)
            prove_results.append(
                aleph.ProveResult(
                    problem_id=problem.id,
                    hole=hole,
                    workspace=str(ws_dir),
                    request_id=None,
                    applied=True,  # treat existing proof as "applied"
                    elapsed_s=0.0,
                    returncode=0,
                    log="(skipped — Submission.lean already sorry-free)",
                )
            )
            continue
        print(f"[{problem.id}] prove {hole} (budget={time_budget_min}m / {cost_budget}c)...", flush=True)
        pr = aleph.prove(
            workspace=ws_dir,
            file_rel="Submission.lean",
            theorem=hole,
            api_key=api_key,
            time_budget_min=time_budget_min,
            cost_budget=cost_budget,
        )
        prove_results.append(pr)
        print(
            f"[{problem.id}]   request={pr.request_id} applied={pr.applied} elapsed={pr.elapsed_s:.1f}s",
            flush=True,
        )

    print(f"[{problem.id}] lake build...", flush=True)
    build = ws_mod.build(ws_dir)
    print(f"[{problem.id}]   build_ok={build.ok} used_sorry={build.used_sorry}", flush=True)

    axioms_per_hole: dict[str, ws_mod.AxiomResult] = {}
    if build.ok and not build.used_sorry:
        for hole in problem.holes:
            ax = ws_mod.axiom_check(ws_dir, hole=hole)
            axioms_per_hole[hole] = ax
            print(f"[{problem.id}]   axioms {hole}: ok={ax.ok} {ax.axioms}", flush=True)

    elapsed_total = time.monotonic() - t0
    timestamp = time.strftime("%Y-%m-%dT%H:%M:%S")

    # One CSV row per hole
    summary_holes = []
    any_failed = False
    for pr in prove_results:
        ax = axioms_per_hole.get(pr.hole)
        succeeded = bool(
            pr.applied
            and build.ok
            and not build.used_sorry
            and ax is not None
            and ax.ok
        )
        if not succeeded:
            any_failed = True
        row = {
            "timestamp": timestamp,
            "problem_id": problem.id,
            "title": problem.title,
            "test": problem.test,
            "hole": pr.hole,
            "request_id": pr.request_id or "",
            "applied": pr.applied,
            "build_ok": build.ok,
            "build_sorry": build.used_sorry,
            "axiom_ok": ax.ok if ax else False,
            "axioms": ";".join(ax.axioms) if ax else "",
            "succeeded": succeeded,
            "elapsed_prove_s": f"{pr.elapsed_s:.1f}",
            "elapsed_total_s": f"{elapsed_total:.1f}",
            "time_budget_min": time_budget_min,
            "cost_budget": cost_budget,
        }
        append_row(row)
        summary_holes.append(row)

    payload = {
        "problem": dataclasses.asdict(problem),
        "workspace": str(ws_dir),
        "prove": [dataclasses.asdict(pr) for pr in prove_results],
        "build": dataclasses.asdict(build),
        "axioms": {h: dataclasses.asdict(a) for h, a in axioms_per_hole.items()},
        "elapsed_total_s": elapsed_total,
        "succeeded": not any_failed,
    }
    write_raw(problem.id, payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="run_eval")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--smoke", action="store_true", help="3 test=true + 5 sampled test=false")
    g.add_argument("--problem", type=str, action="append", help="run a single problem id (repeatable)")
    g.add_argument("--all", action="store_true", help="every problem in the manifest")

    ap.add_argument("--time-budget", type=int, default=DEFAULT_TIME_BUDGET_MIN)
    ap.add_argument("--cost-budget", type=float, default=DEFAULT_COST_BUDGET)
    ap.add_argument("--retry", action="store_true", help="re-run problems already marked succeeded")
    ap.add_argument("--seed", type=int, default=0, help="seed for smoke sampling")
    args = ap.parse_args(argv)

    api_key = load_env()
    problems = manifest.load(LEAN_EVAL / "manifests" / "problems.toml")

    if args.smoke:
        chosen = select_smoke(problems, seed=args.seed)
    elif args.problem:
        chosen = manifest.filter_ids(problems, args.problem)
        missing = set(args.problem) - {p.id for p in chosen}
        if missing:
            print(f"unknown problem ids: {sorted(missing)}", file=sys.stderr)
            return 2
    else:
        chosen = problems

    if not args.retry:
        before = len(chosen)
        chosen = [p for p in chosen if not already_done(p.id)]
        skipped = before - len(chosen)
        if skipped:
            print(f"skipping {skipped} already-succeeded problems (use --retry to override)")

    print(f"running {len(chosen)} problem(s):")
    for p in chosen:
        print(f"  - {p.id}  ({'test' if p.test else 'main'})  holes={list(p.holes)}")

    successes = 0
    for p in chosen:
        try:
            payload = run_one(
                p,
                api_key=api_key,
                time_budget_min=args.time_budget,
                cost_budget=args.cost_budget,
            )
            successes += int(payload["succeeded"])
        except Exception as e:
            print(f"[{p.id}] HARNESS ERROR: {e!r}", flush=True)

    print(f"\n=== summary: {successes}/{len(chosen)} succeeded ===")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
