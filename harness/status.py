"""Print a short summary of results/results.csv."""

from __future__ import annotations

import csv
import pathlib
import sys


CSV_PATH = pathlib.Path(__file__).resolve().parent.parent / "results" / "results.csv"


def main() -> int:
    if not CSV_PATH.exists():
        print("no results yet (results/results.csv missing)")
        return 0
    all_rows = list(csv.DictReader(CSV_PATH.open()))
    if not all_rows:
        print("results.csv exists but has no rows")
        return 0

    # Dedupe: latest row wins per (problem_id, hole)
    latest: dict[tuple[str, str], dict] = {}
    for r in all_rows:
        key = (r["problem_id"], r["hole"])
        prev = latest.get(key)
        if prev is None or r["timestamp"] >= prev["timestamp"]:
            latest[key] = r
    rows = list(latest.values())

    by_problem: dict[str, list[dict]] = {}
    for r in rows:
        by_problem.setdefault(r["problem_id"], []).append(r)

    n_problems = len(by_problem)
    succeeded = sum(
        1 for holes in by_problem.values() if all(h["succeeded"] == "True" for h in holes)
    )
    n_holes = len(rows)
    succeeded_holes = sum(1 for r in rows if r["succeeded"] == "True")

    print(f"problems: {succeeded}/{n_problems} succeeded")
    print(f"holes:    {succeeded_holes}/{n_holes} succeeded")
    print()
    print(f"{'problem_id':<40} {'test':<5} {'holes':<5} {'pass':<5} {'avg_s':<7} {'request_ids'}")
    print("-" * 100)
    for pid, holes in by_problem.items():
        is_test = holes[0]["test"]
        n = len(holes)
        passed = sum(1 for h in holes if h["succeeded"] == "True")
        avg_s = sum(float(h["elapsed_prove_s"] or 0) for h in holes) / max(n, 1)
        rids = ",".join((h["request_id"] or "?")[:8] for h in holes)
        print(f"{pid:<40} {is_test:<5} {n:<5} {passed:<5} {avg_s:<7.1f} {rids}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
