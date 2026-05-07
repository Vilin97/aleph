"""Retry submission for problems that hit HTTP 429 during the full sweep.

Usage: python -m harness.resubmit problem_id [problem_id ...]

Loops every RETRY_INTERVAL_S until each gets a Request ID, then writes the
ids to results/full-requests.json (additive merge).
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
import time

from . import run_eval


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_EVAL = REPO_ROOT / "lean-eval"
RESULTS = REPO_ROOT / "results"
REQUESTS_JSON = RESULTS / "full-requests.json"
RETRY_INTERVAL_S = 300


def submit_once(problem_id: str, hole: str, *, api_key: str) -> str | None:
    ws = LEAN_EVAL / "workspaces" / problem_id
    log = RESULTS / f"full-{problem_id}.log"
    env = {**os.environ, "PROVER_API_KEY": api_key}
    with log.open("w") as f:
        proc = subprocess.run(
            ["alephprover", "prove", "Submission.lean", hole, "--no-poll", "-v"],
            cwd=str(ws),
            env=env,
            stdout=f,
            stderr=subprocess.STDOUT,
            timeout=300,
        )
    text = log.read_text()
    m = re.search(r"Request ID:\s*([0-9a-f-]+)", text, re.I)
    return m.group(1) if m else None


def main(argv: list[str]) -> int:
    api_key = run_eval.load_env()
    pending = list(argv)
    if not pending:
        print("usage: resubmit problem_id [...]", file=sys.stderr)
        return 2

    # Map problem_id -> hole (single-hole only here)
    from . import manifest
    problems = {p.id: p for p in manifest.load(LEAN_EVAL / "manifests" / "problems.toml")}

    while pending:
        succeeded_now: dict[str, str] = {}
        for pid in list(pending):
            try:
                rid = submit_once(pid, problems[pid].holes[0], api_key=api_key)
            except Exception as e:
                print(f"[{pid}] error: {e!r}", flush=True)
                continue
            if rid:
                print(f"[{pid}] OK rid={rid}", flush=True)
                succeeded_now[pid] = rid
                pending.remove(pid)
            else:
                last = pathlib.Path(RESULTS / f"full-{pid}.log").read_text().splitlines()[-3:]
                print(f"[{pid}] no rid yet ({last[-1] if last else ''})", flush=True)

        if succeeded_now:
            existing = json.loads(REQUESTS_JSON.read_text()) if REQUESTS_JSON.is_file() else {"request_ids": {}}
            existing["request_ids"].update(succeeded_now)
            existing["timestamp_resubmit"] = time.strftime("%Y-%m-%dT%H:%M:%S")
            REQUESTS_JSON.write_text(json.dumps(existing, indent=2))

        if pending:
            print(f"sleeping {RETRY_INTERVAL_S}s, {len(pending)} still pending: {pending}", flush=True)
            time.sleep(RETRY_INTERVAL_S)

    print("all resubmits accepted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
