#!/usr/bin/env python3
"""Reset each pf/port/* branch to upstream/master + PF changes from pf/golf-all."""

from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRANCHES: list[tuple[str, list[str], bool]] = [
    ("pf/port/list-count", ["Mathlib/Data/List/Count.lean"], False),
    ("pf/port/quiver-cyclic", ["Mathlib/Combinatorics/Quiver/Cyclic.lean"], True),
    ("pf/port/matrix-spectrum", [
        "Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean",
        "Mathlib/LinearAlgebra/Matrix/Spectrum/PerronFrobenius.lean",
    ], True),
    ("pf/port/aux", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Aux.lean"], True),
    ("pf/port/cstar-classes", ["Mathlib/Analysis/CStarAlgebra/PerronFrobenius.lean"], True),
    ("pf/port/quiver-path", ["Mathlib/Combinatorics/Quiver/Path/PerronFrobenius.lean"], True),
    ("pf/port/lemmas", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Lemmas.lean"], True),
    ("pf/port/collatz-wielandt", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt.lean"], True),
    ("pf/port/primitive", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Primitive.lean"], True),
    ("pf/port/uniqueness", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Uniqueness.lean"], True),
    ("pf/port/irreducible", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Irreducible.lean"], True),
    ("pf/port/dominance", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Dominance.lean"], True),
    ("pf/port/dominance-part2", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/DominancePart2.lean"], True),
    ("pf/port/multiplicity", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Multiplicity.lean"], True),
    ("pf/port/aperiodic", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Aperiodic.lean"], True),
    ("pf/port/stochastic", ["Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Stochastic.lean"], True),
]

AGGREGATORS = [
    "Mathlib.lean",
    "Mathlib/Tactic.lean",
    "Counterexamples.lean",
    "Archive.lean",
]



def run(cmd: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(cmd))
    return subprocess.run(cmd, cwd=ROOT, check=check, text=True, capture_output=True)


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    r = run(["git", *args], check=False)
    if r.stdout:
        print(r.stdout)
    if r.stderr:
        print(r.stderr)
    if check and r.returncode != 0:
        raise subprocess.CalledProcessError(r.returncode, r.args, r.stdout, r.stderr)
    return r


def golf_all_file(rel_path: str) -> str:
    r = run(["git", "show", f"pf/golf-all:{rel_path}"], check=True)
    return r.stdout


def run_mk_all(*, check: bool = False) -> None:
    r = run(["lake", "exe", "mk_all"] + (["--check"] if check else []), check=False)
    if r.stdout:
        print(r.stdout)
    if r.stderr:
        print(r.stderr)
    if check:
        if r.returncode != 0:
            raise RuntimeError("mk_all --check failed")
        return
    if r.returncode > 125:
        raise RuntimeError(f"lake exe mk_all failed with exit code {r.returncode}")


def sync_branch(branch: str, rel_paths: list[str], regen_aggregators: bool) -> None:
    git("checkout", "-B", branch, "upstream/master")
    for rel_path in rel_paths:
        target = ROOT / rel_path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(golf_all_file(rel_path))
    git("add", *rel_paths)
    if regen_aggregators:
        run_mk_all()
        existing = [p for p in AGGREGATORS if (ROOT / p).exists()]
        if existing:
            git("add", *existing)
    label = rel_paths[0] if len(rel_paths) == 1 else ", ".join(rel_paths)
    git("commit", "-m", f"feat(PerronFrobenius): port {label}")
    run_mk_all(check=True)
    print(f"synced {branch}")


def main() -> None:
    git("fetch", "upstream", "master")
    git("checkout", "pf/golf-all")
    run(["lake", "exe", "cache", "get"], check=False)
    run_mk_all()
    for branch, rel_paths, regen in BRANCHES:
        sync_branch(branch, rel_paths, regen)
    git("checkout", "pf/golf-all")
    print("done")


if __name__ == "__main__":
    main()
