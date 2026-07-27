/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Photonics.Matrix.EigenvalueResidual
public import Photonics.Matrix.NormComparison
public import Photonics.Matrix.UnitaryDistance
public import Photonics.Normed.Telescope

/-!
# Photonics: formal verification of programmable photonic circuits

A staging library for the formalization described in the photonic chip verification roadmap.
Everything here builds on Mathlib and is intended either to be upstreamed to Mathlib or to
migrate to a standalone photonics verification repository; keeping it in one directory tree is
what makes both moves cheap.

This root file is maintained by hand: `Photonics` is excluded from `scripts/mk_all.lean`, which
would otherwise regenerate it without the module-system `import` prefixes that its contents
require.

Current contents (Tier A of the roadmap: norms and metrics):

* `Photonics.Matrix.NormComparison` — the Frobenius and `ℓ²` operator (spectral) norms as plain
  functions, the inequalities relating them and the entries, the Schur test, and unitary
  invariance.
* `Photonics.Matrix.UnitaryDistance` — distance between matrices up to a global phase, fidelity,
  and the unitary group as a normed group.
* `Photonics.Matrix.EigenvalueResidual` — a posteriori eigenvalue bounds from a residual.
* `Photonics.Normed.Telescope` — error propagation through a product of contractions.
-/
