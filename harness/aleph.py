"""Thin wrapper around the `alephprover` CLI.

Aleph prove flow: zip project, upload, poll, apply diff via `git apply`. The
project root is whichever ancestor of FILE_PATH contains a `lakefile.toml` or
`lakefile.lean`.
"""

from __future__ import annotations

import dataclasses
import os
import pathlib
import re
import subprocess
import time


REQUEST_ID_RE = re.compile(r"Request ID:\s*([0-9a-f-]+)", re.I)
APPLIED_RE = re.compile(r"Proof applied successfully", re.I)
FAILED_HINTS = ("Proof failed", "failed", "error", "Error", "Cancelled", "cancelled")


@dataclasses.dataclass
class ProveResult:
    problem_id: str
    hole: str
    workspace: str
    request_id: str | None
    applied: bool
    elapsed_s: float
    returncode: int
    log: str


def prove(
    *,
    workspace: pathlib.Path,
    file_rel: str,
    theorem: str,
    api_key: str,
    time_budget_min: int = 5,
    cost_budget: float = 1.0,
    timeout_s: float = 1800.0,
    extra_args: list[str] | None = None,
) -> ProveResult:
    """Invoke `alephprover prove` and return a structured result.

    Workspace is the directory holding lakefile.toml. The CLI walks up to
    find it, but we cd in explicitly so that `git apply` runs against the
    enclosing git tree.
    """
    cmd = [
        "alephprover",
        "prove",
        file_rel,
        theorem,
        "--time-budget",
        str(time_budget_min),
        "--cost-budget",
        str(cost_budget),
        "-v",
    ]
    if extra_args:
        cmd.extend(extra_args)

    env = os.environ.copy()
    env["PROVER_API_KEY"] = api_key

    start = time.monotonic()
    proc = subprocess.run(
        cmd,
        cwd=str(workspace),
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    elapsed = time.monotonic() - start

    log = proc.stdout + ("\n--- stderr ---\n" + proc.stderr if proc.stderr else "")
    request_id = None
    m = REQUEST_ID_RE.search(log)
    if m:
        request_id = m.group(1)
    applied = bool(APPLIED_RE.search(log))

    return ProveResult(
        problem_id=workspace.name,
        hole=theorem,
        workspace=str(workspace),
        request_id=request_id,
        applied=applied,
        elapsed_s=elapsed,
        returncode=proc.returncode,
        log=log,
    )
