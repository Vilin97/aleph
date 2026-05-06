"""Read lean-eval's manifests/problems.toml."""

from __future__ import annotations

import dataclasses
import pathlib
import tomllib
from typing import Iterable


@dataclasses.dataclass(frozen=True)
class Problem:
    id: str
    title: str
    test: bool
    module: str
    holes: tuple[str, ...]
    submitter: str
    notes: str | None = None
    source: str | None = None
    informal_solution: str | None = None


def load(manifest_path: pathlib.Path) -> list[Problem]:
    with manifest_path.open("rb") as f:
        data = tomllib.load(f)
    out: list[Problem] = []
    for entry in data.get("problem", []):
        out.append(
            Problem(
                id=entry["id"],
                title=entry["title"],
                test=bool(entry["test"]),
                module=entry["module"],
                holes=tuple(entry["holes"]),
                submitter=entry["submitter"],
                notes=entry.get("notes"),
                source=entry.get("source"),
                informal_solution=entry.get("informal_solution"),
            )
        )
    return out


def filter_ids(problems: Iterable[Problem], ids: Iterable[str]) -> list[Problem]:
    wanted = set(ids)
    return [p for p in problems if p.id in wanted]
