"""Per-problem workspace setup, build, and axiom verification."""

from __future__ import annotations

import dataclasses
import pathlib
import re
import subprocess
import textwrap


SORRY_RE = re.compile(r"declaration uses `sorry`")
BUILD_OK_RE = re.compile(r"Build completed successfully")


@dataclasses.dataclass
class BuildResult:
    ok: bool
    used_sorry: bool
    log: str
    returncode: int


@dataclasses.dataclass
class AxiomResult:
    hole: str
    ok: bool  # True if no `sorry` in axioms list
    axioms: list[str]
    log: str


def ensure_workspace(
    *,
    lean_eval_root: pathlib.Path,
    problem_id: str,
) -> pathlib.Path:
    """Run `lake exe lean-eval start-problem <id>` if workspace doesn't exist.

    Returns the absolute path to the workspace.
    """
    ws = lean_eval_root / "workspaces" / problem_id
    if not ws.is_dir():
        subprocess.run(
            ["lake", "exe", "lean-eval", "start-problem", problem_id],
            cwd=str(lean_eval_root),
            check=True,
        )
    # lake update + cache get bring in mathlib oleans (idempotent)
    subprocess.run(["lake", "update"], cwd=str(ws), check=False)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=str(ws), check=False)
    return ws


def build(workspace: pathlib.Path, *, timeout_s: float = 1800.0) -> BuildResult:
    proc = subprocess.run(
        ["lake", "build"],
        cwd=str(workspace),
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    log = proc.stdout + proc.stderr
    return BuildResult(
        ok=proc.returncode == 0 and bool(BUILD_OK_RE.search(log)),
        used_sorry=bool(SORRY_RE.search(log)),
        log=log,
        returncode=proc.returncode,
    )


def axiom_check(
    workspace: pathlib.Path, *, hole: str, timeout_s: float = 600.0
) -> AxiomResult:
    """Run `#print axioms Submission.<hole>` in the workspace.

    Returns ok=True iff `sorry` (and any axiom name containing 'sorry') is
    NOT present in the axioms list. Other axioms (Classical.choice etc.) are
    allowed; we just record them.
    """
    snippet = textwrap.dedent(
        f"""\
        import Submission
        #print axioms Submission.{hole}
        """
    )
    tmp = workspace / ".axiom_check.lean"
    tmp.write_text(snippet)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp.name)],
            cwd=str(workspace),
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
    finally:
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass

    log = proc.stdout + proc.stderr
    axioms = _parse_axioms(log)
    has_sorry = any("sorry" in a.lower() for a in axioms) or "uses 'sorry'" in log
    return AxiomResult(hole=hole, ok=not has_sorry, axioms=axioms, log=log)


def _parse_axioms(text: str) -> list[str]:
    """Best-effort parse of `#print axioms` output.

    Lean prints either:
      `'<name>' does not depend on any axioms`
    or:
      `'<name>' depends on axioms: [a, b, c]`
    """
    for line in text.splitlines():
        line = line.strip()
        if "does not depend on any axioms" in line:
            return []
        if "depends on axioms:" in line:
            after = line.split("depends on axioms:", 1)[1].strip()
            after = after.strip("[]")
            return [a.strip() for a in after.split(",") if a.strip()]
    return []
