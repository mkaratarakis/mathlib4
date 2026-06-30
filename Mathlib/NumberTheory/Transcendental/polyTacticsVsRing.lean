/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.polyReflectKernel
import Mathlib.NumberTheory.Transcendental.mvpolyReflectKernel
import Mathlib.NumberTheory.Transcendental.polyTactics

/-!
# Where `ring` fails but our tactics work

`ring` proves only identities true in **every** commutative ring (the ring axioms); it normalizes
both sides and compares, but it does **not** reduce coefficients using the *specific* ring's
arithmetic. Our reflection tactics actually **compute** in the ring, so they decide goals `ring`
cannot:

1. **characteristic-specific identities** over `ZMod p` ("freshman's dream" / Frobenius) — *false*
   over `ℤ`, so unreachable by `ring`;
2. **inequalities** (`≠`) — `ring` does not prove these at all;
3. **divisibility** (`p ∣ q`) and **ideal membership** (`p ∈ Ideal.span {…}`) — not equational goals,
   so wholly outside `ring`'s scope; `poly_dvd`/`mv_mem` decide them by kernel-reducible division.

All proofs here are **axiom-free** (`mv_decide`/`poly_decide`/`mv_compute`/`poly_compute`, kernel
`decide +kernel`, no `native_decide`). (`ring`'s failures were confirmed separately: e.g. on the
first identity `ring` reduces the goal to `1 + X*3 + X^2*3 + X^3 = 1 + X^3` and stops — it never uses
`3 ≡ 0 (mod 3)`.)
-/

namespace PolyTacticsVsRing

/-! ## 1. Finite-field identities — `ring` can't (not universal); `decide` can't (noncomputable)

A caveat in the interest of honesty: the *Frobenius pattern* `(X+1)ᵖ = Xᵖ+1` **is** reachable in
Mathlib without us, via the lemma `add_pow_char` (`(x+y)ᵖ = xᵖ+yᵖ` in characteristic `p`). So that
single pattern is *not* a unique selling point. The real point is the **general** case: an *arbitrary*
ground identity over `ZMod p`, which is not any named pattern, has no `ring`/lemma route — only
computation decides it. The examples below are deliberately **not** Frobenius-shaped. -/

section ModP
open Polynomial

-- `(X²+X+1)² = X⁴+2X³+2X+1` over `𝔽₃` (the `3·X²` coefficient vanishes). No lemma fits; `ring` leaves
-- a `…·3` term; `poly_decide` computes it, axiom-free:
example : ((X ^ 2 + X + 1) ^ 2 : Polynomial (ZMod 3)) = X ^ 4 + 2 * X ^ 3 + 2 * X + 1 := by
  poly_decide

-- `(X+1)⁴ = X⁴+X³+X+1` over `𝔽₃` (4 is not a power of 3, so Frobenius does not apply):
example : ((X + 1) ^ 4 : Polynomial (ZMod 3)) = X ^ 4 + X ^ 3 + X + 1 := by poly_decide

-- An arbitrary product over `𝔽₅`:
example : ((2 * X + 1) * (X + 2) : Polynomial (ZMod 5)) = 2 * X ^ 2 + 2 := by poly_decide

-- For contrast: the Frobenius special case, which Mathlib's `add_pow_char` already handles —
-- here proved instead by our general decision procedure:
example : ((X + 1) ^ 3 : Polynomial (ZMod 3)) = X ^ 3 + 1 := by poly_decide

end ModP

section ModPMV
open MvPolynomial

-- Non-Frobenius multivariate identity over `𝔽₃`:
example : ((X 0 + X 1) ^ 4 : MvPolynomial (Fin 2) (ZMod 3))
    = X 0 ^ 4 + X 0 ^ 3 * X 1 + X 0 * X 1 ^ 3 + X 1 ^ 4 := by mv_decide

-- Multivariate Frobenius (cross terms vanish mod p) — provable by `add_pow_char` too, here by us:
example : ((X 0 + X 1) ^ 3 : MvPolynomial (Fin 2) (ZMod 3)) = X 0 ^ 3 + X 1 ^ 3 := by mv_decide

end ModPMV

/-! ## 2. Inequalities — `ring` proves no `≠` goal at all -/

section Inequalities
open Polynomial

example : ((X + 1) ^ 2 : Polynomial ℤ) ≠ X ^ 2 + 1 := by poly_compute
example : ((X + 1) ^ 3 : Polynomial ℤ) ≠ X ^ 3 + 1 := by poly_compute

end Inequalities

section InequalitiesMV
open MvPolynomial

example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 0 ^ 2 + X 1 ^ 2 := by mv_compute
-- over `𝔽₃` the *cube* collapses but the *square* genuinely differs — our tactic knows which:
example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) (ZMod 3)) ≠ X 0 ^ 2 + X 1 ^ 2 := by mv_compute

end InequalitiesMV

/-! ## 3. Divisibility and ideal membership — entirely outside `ring`

`ring` only proves equalities of ring expressions. Divisibility and ideal membership are not
equational goals at all, so `ring` cannot even be applied. Both decide here, **axiom-free**, by
kernel-reducible (multi)division. -/

section Dvd
open Polynomial

-- `X − 1 ∣ X³ − 1` and the cyclotomic factor `X² + X + 1 ∣ X³ − 1` (monic divisors over `ℤ`):
example : (X - 1 : Polynomial ℤ) ∣ (X ^ 3 - 1) := by poly_dvd
example : (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X ^ 3 - 1) := by poly_dvd

end Dvd

section Ideal
open MvPolynomial

-- Ideal membership in `⟨x, y⟩`, reduced to `0` by multidivisor division:
example : (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ∈ Ideal.span {X 0, X 1} := by mv_mem
example : (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) ∈ Ideal.span {X 0, X 1} := by mv_mem

end Ideal

end PolyTacticsVsRing
