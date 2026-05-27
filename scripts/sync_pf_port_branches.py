#!/usr/bin/env python3
"""Reset each pf/port/* branch to upstream/master + PF changes from pf/golf-all."""

from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# (branch, paths relative to repo root, optional Mathlib.lean import line)
BRANCHES: list[tuple[str, list[str], str | None]] = [
    ("pf/port/list-count", ["Mathlib/Data/List/Count.lean"], None),
    ("pf/port/quiver-cyclic", ["Mathlib/Combinatorics/Quiver/Cyclic.lean"],
     "public import Mathlib.Combinatorics.Quiver.Cyclic"),
    ("pf/port/matrix-spectrum", [
        "Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean",
        "Mathlib/LinearAlgebra/Matrix/Spectrum/PerronFrobenius.lean",
    ], "public import Mathlib.LinearAlgebra.Matrix.Spectrum.PerronFrobenius"),
    ("pf/port/aux", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Aux.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Aux"),
    ("pf/port/cstar-classes", ["Mathlib/Analysis/CStarAlgebra/PerronFrobenius.lean"],
     "public import Mathlib.Analysis.CStarAlgebra.PerronFrobenius"),
    ("pf/port/quiver-path", ["Mathlib/Combinatorics/Quiver/Path/PerronFrobenius.lean"],
     "public import Mathlib.Combinatorics.Quiver.Path.PerronFrobenius"),
    ("pf/port/lemmas", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Lemmas.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Lemmas"),
    ("pf/port/collatz-wielandt", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt"),
    ("pf/port/primitive", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Primitive.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Primitive"),
    ("pf/port/uniqueness", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Uniqueness.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Uniqueness"),
    ("pf/port/irreducible", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Irreducible.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible"),
    ("pf/port/dominance", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Dominance.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance"),
    ("pf/port/dominance-part2", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/DominancePart2.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.DominancePart2"),
    ("pf/port/multiplicity", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Multiplicity.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Multiplicity"),
    ("pf/port/aperiodic", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Aperiodic.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Aperiodic"),
    ("pf/port/stochastic", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Stochastic.lean"],
     "public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Stochastic"),
]


def run(cmd: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(cmd))
    return subprocess.run(cmd, cwd=ROOT, check=check, text=True, capture_output=True)


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    r = run(["git", *args], check=check)
    if r.stdout:
        print(r.stdout)
    if r.stderr:
        print(r.stderr)
    return r


def insert_import(base_lean: str, import_line: str) -> str:
    lines = base_lean.splitlines()
    if import_line in lines:
        return base_lean if base_lean.endswith("\n") else base_lean + "\n"
    out: list[str] = []
    inserted = False
    for line in lines:
        if not inserted and line.startswith("public import Mathlib.") and line > import_line:
            out.append(import_line)
            inserted = True
        out.append(line)
    if not inserted:
        out.append(import_line)
    return "\n".join(out) + "\n"


def sync_branch(branch: str, rel_paths: list[str], import_line: str | None) -> None:
    git("checkout", "-B", branch, "upstream/master")
    for rel_path in rel_paths:
        target = ROOT / rel_path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(git("show", f"pf/golf-all:{rel_path}").stdout)
    if import_line is not None:
        base_lean = git("show", "upstream/master:Mathlib.lean").stdout
        (ROOT / "Mathlib.lean").write_text(insert_import(base_lean, import_line))
        git("add", *rel_paths, "Mathlib.lean")
    else:
        git("add", *rel_paths)
    label = rel_paths[0] if len(rel_paths) == 1 else ", ".join(rel_paths)
    git("commit", "-m", f"feat(PerronFrobenius): port {label}")
    print(f"synced {branch}")


def main() -> None:
    git("fetch", "upstream", "master")
    git("checkout", "pf/golf-all")
    for branch, rel_paths, imp in BRANCHES:
        sync_branch(branch, rel_paths, imp)
    git("checkout", "pf/golf-all")
    print("done")


if __name__ == "__main__":
    main()
