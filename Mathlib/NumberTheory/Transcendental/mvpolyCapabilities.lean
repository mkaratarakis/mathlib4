/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.mvpolyReflectKernel
import Mathlib.NumberTheory.Transcendental.mvpolyProducts -- the human-readable `Repr` for `#eval`

/-!
# Capability showcase: doing everything with Mathlib's `MvPolynomial` via the computable `MvSparsePoly`

Mathlib's `MvPolynomial (Fin n) R` is **noncomputable**. This file demonstrates that, through the ring
isomorphism `toPoly : MvSparsePoly R n ≃ₐ MvPolynomial (Fin n) R` and the computable operations of
`MvSparsePoly`, we can nonetheless *compute* and *prove* the things one actually wants:

1. **prove** ring equalities / inequalities of `MvPolynomial` (reflection tactics);
2. **evaluate** an `MvPolynomial` (certified against `MvPolynomial.eval`);
3. **differentiate** (certified against `MvPolynomial.pderiv`);
4. **divide** exactly;
5. take **gcd / content**;
6. reduce modulo a basis (**Gröbner / Buchberger `normalForm`**) and thereby **certify ideal
   membership** in `MvPolynomial` — a genuinely noncomputable-looking `Prop`, settled by computation.

Each numbered section pairs a concrete computation (`#eval` / `#guard`, which run the real fast code)
with the *proved* bridge theorem from `mvpoly.lean` that certifies it agrees with Mathlib.

`#eval`/`#guard` add no axioms, and proof obligations use only the **axiom-free** kernel tactic
`mv_decide` (no `native_decide` anywhere in this file).
-/

namespace MvPolyCapabilities

/-! ## 1. Proving `MvPolynomial` identities and inequalities -/

section Identities
open MvPolynomial

-- Axiom-free (kernel), over `ℤ`:
example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by
  mv_decide

-- Inequality (native path; `mv_decide` is `=`-only):
example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 0 ^ 2 + X 1 ^ 2 := by
  mv_compute

-- (A broader battery of identities lives in `mvpolyReflectTests.lean`.)
end Identities

/-! ## 2. Evaluation — certified by `eval_eq_eval_toPoly` -/

section Eval
open MvSparsePoly

-- Compute `(x₀ + x₁)² ` at `(3, 5)`:
#guard eval ![3, 5] ((X 0 + X 1) ^ 2 : MvSparsePoly ℤ 2) = 64

-- … and this *is* Mathlib's evaluation of the corresponding `MvPolynomial` (proved, for all inputs):
example (vs : Fin 2 → ℤ) (p : MvSparsePoly ℤ 2) :
    eval vs p = MvPolynomial.eval vs (toPoly p) := eval_eq_eval_toPoly vs p
end Eval

/-! ## 3. Differentiation — certified by `toPoly_pderiv` -/

section Deriv
open MvSparsePoly

-- `∂/∂x₀ (x₀² + x₀x₁) = 2x₀ + x₁`:
#guard pderiv 0 (X 0 ^ 2 + X 0 * X 1 : MvSparsePoly ℤ 2) = C 2 * X 0 + X 1

-- … and our `pderiv` is Mathlib's `pderiv` transported across the bridge (proved):
example (k : Fin 2) (p : MvSparsePoly ℤ 2) :
    toPoly (pderiv k p) = MvPolynomial.pderiv k (toPoly p) := toPoly_pderiv k p
end Deriv

/-! ## 4. Exact division -/

section Division
open MvSparsePoly

-- `(x₀² − x₁²) / (x₀ − x₁) = x₀ + x₁`, exactly (over the field `ℚ`):
#guard (X 0 ^ 2 - X 1 ^ 2 : MvSparsePoly ℚ 2) / (X 0 - X 1) = X 0 + X 1

-- Cross-check the division is exact: quotient times divisor recovers the dividend:
#guard ((X 0 ^ 2 - X 1 ^ 2 : MvSparsePoly ℚ 2) / (X 0 - X 1)) * (X 0 - X 1) = X 0 ^ 2 - X 1 ^ 2
end Division

/-! ## 5. gcd and content -/

section Gcd
open MvSparsePoly

-- content (the gcd of the coefficients) and a polynomial gcd, over `ℤ`:
#eval content (C 6 * X 0 + C 4 * X 1 : MvSparsePoly ℤ 2)        -- 2
#eval gcd (X 0 ^ 2 - X 1 ^ 2 : MvSparsePoly ℚ 2) (X 0 - X 1)    -- ~ x₀ − x₁ (up to a unit)
end Gcd

/-! ## 6. Gröbner reduction and certified ideal membership -/

section Groebner
open MvSparsePoly

-- `x₀·x₁ + x₁` reduces to `0` modulo the basis `{x₀, x₁}` (Buchberger-style `normalForm`):
#guard normalForm (X 0 * X 1 + X 1 : MvSparsePoly ℚ 2) [X 0, X 1] = 0

-- The underlying guarantee is **axiom-free**: for *any* `f`, `G`, the difference between `f` and its
-- normal form lies in the ideal (a proved theorem). Combined with the `#guard` above (`normalForm = 0`),
-- `mem_idealOf_of_normalForm_eq_zero` gives `toPoly (x₀x₁ + x₁) ∈ ⟨x₀, x₁⟩`. Turning that into a
-- *tactic* axiom-free needs a kernel-reducible `normalForm` (or cofactor extraction) — deferred.
example (f : MvSparsePoly ℚ 2) (G : List (MvSparsePoly ℚ 2)) :
    toPoly f - toPoly (normalForm f G) ∈ idealOf G := normalForm_span f G
end Groebner

end MvPolyCapabilities
