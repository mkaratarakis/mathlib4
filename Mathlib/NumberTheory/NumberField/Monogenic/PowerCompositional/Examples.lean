/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Main

/-!
# Families of monogenic power compositional polynomials

This file proves the applications in Section 4 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*, Finite Fields Appl. **107** (2025), 102642
that do not rest on a computer search, together with the examples of Section 1 that they
subsume.

## Main results

* `RingOfIntegers.adjoin_eq_top_expand_X_sub_C_iff`: **Proposition 4.1** --- for
  `f = X - A`, the polynomial `X ^ k - A` is monogenic if and only if `A` is squarefree and
  `p ^ 2 ∤ A ^ p - A` for every prime `p ∣ k`.  The second condition says that `p` is not a
  Wieferich prime to the base `A`.

* `RingOfIntegers.adjoin_eq_top_expand_jones_iff` and
  `RingOfIntegers.adjoin_eq_top_expand_jones_iff_of_dvd_radical`: **Proposition 4.5** ---
  for the Kaur–Kumar family `f = X ^ d + A (B X + 1) ^ m`, monogenity of `f(X ^ k)` reduces
  to squarefreeness of `A` and of `D d m A B`, plus one condition per prime divisor of `k`;
  and when `rad k ∣ rad A` the latter conditions disappear.

* `RingOfIntegers.adjoin_eq_top_expand_iff_of_splits`: **Proposition 4.2** --- when `f`
  splits completely modulo every prime divisor of `k`, condition (2) of Theorem 1.1 becomes
  the finite check `p ^ 2 ∤ f(r ^ p)` for `r = 0, …, p - 1`.

* `RingOfIntegers.example_1_6`: **Example 1.6**, the necessity of condition (3).

* `RingOfIntegers.example_1_7` and `RingOfIntegers.example_1_9`: **Examples 1.7 and 1.9**,
  both instances of the `rad k ∣ rad A` form: `X ^ 3 + 6 (X + 1) ^ 2` with `k = 2 ^ u 3 ^ v`
  and `X ^ 2 + 2 (X + 1)` with `k = 2 ^ u` are monogenic for every such `k`.

## Implementation notes

Proposition 4.5 is where two formalisations meet: Theorem 1.14 of this paper reduces
monogenity of `f(X ^ k)` to monogenity of `f`, and `NumberField.KaurKumar.monogenic_iff` —
the main theorem of S. Kaur and S. Kumar, *On a conjecture of Lenny Jones about certain
monogenic polynomials* — evaluates the latter.  The bridge between the two phrasings is
`RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top`, applied at the canonical root
of `f`.

Condition (2) of Propositions 4.1 and 4.5 is stated as `¬ IsIndexDivisor p (f(X ^ p))`.  For
Proposition 4.1 it is then computed explicitly, giving the Wieferich condition.  The paper
writes condition (2) of Proposition 4.5 as coprimality of
`(-A(Bx+1) ^ m) ^ p + A(Bx ^ p + 1) ^ m) / p` with `f` modulo `p`; that polynomial differs
from the one produced by Theorem 1.11 by a multiple of `f`, so the two conditions agree,
but the identification is not carried out here.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
* [S. Kaur, S. Kumar, *On a conjecture of Lenny Jones about certain monogenic
  polynomials*][kaurkumar2023]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField NumberField.KaurKumar

namespace RingOfIntegers

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Proposition 4.1: the family `X - A` -/

/-- For `f = X - A`, the prime `p` is an index divisor of `f(X ^ p) = X ^ p - A` exactly when
`p ^ 2 ∣ A ^ p - A`, that is, when `p` is a Wieferich prime to the base `A`.

By Theorem 1.11 the index divisor condition is the failure of coprimality of `f` with
`T = (f(X ^ p) - f ^ p) / p` mod `p`.  Since `f` is linear, that coprimality is decided by
the value of `T` at `A`, and `p * T(A) = A ^ p - A`. -/
theorem isIndexDivisor_expand_X_sub_C_iff (A : ℤ) :
    IsIndexDivisor p (expand ℤ p (X - C A)) ↔ (p : ℤ) ^ 2 ∣ A ^ p - A := by
  have hfm : (X - C A : ℤ[X]).Monic := monic_X_sub_C A
  obtain ⟨T, hT⟩ := exists_expand_eq_pow_add_C_mul (p := p) (X - C A)
  -- evaluating the Frobenius identity at `A`
  have hval : A ^ p - A = (p : ℤ) * T.eval A := by
    have h := congrArg (Polynomial.eval A) hT
    rw [expand_eval, eval_add, eval_mul, eval_pow, eval_C, eval_sub, eval_X, eval_C,
      eval_sub, eval_X, eval_C, sub_self, zero_pow hp.out.ne_zero, zero_add] at h
    exact h
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hT]
  have hmapf : (X - C A : ℤ[X]).map (Int.castRingHom (ZMod p)) = X - C ((A : ZMod p)) := by
    simp [Polynomial.map_sub]
  rw [hmapf]
  -- coprimality with a linear polynomial is nonvanishing at its root
  rw [(irreducible_X_sub_C ((A : ZMod p))).coprime_iff_not_dvd, not_not,
    dvd_iff_isRoot, IsRoot.def]
  -- and the value there is the reduction of `T(A)`
  have hev : (T.map (Int.castRingHom (ZMod p))).eval ((A : ZMod p)) =
      ((T.eval A : ℤ) : ZMod p) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod p)) A
  rw [hev, ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- `p ^ 2 ∣ p * T(A)` iff `p ∣ T(A)`
  constructor
  · intro h
    rw [hval, sq]
    exact mul_dvd_mul_left _ (by exact_mod_cast h)
  · intro h
    rw [hval, sq] at h
    have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
    exact_mod_cast (mul_dvd_mul_iff_left hp0).mp h

/-- **Proposition 4.1** of Kaur–Kumar–Remete.  For `k ≥ 2` with `X ^ k - A` irreducible, the
polynomial `X ^ k - A` is monogenic if and only if `p ^ 2 ∤ A ^ p - A` for every prime
`p ∣ k`, and `A` is squarefree.

The polynomial `X - A` is monogenic for trivial reasons, so condition (1) of Theorem 1.1 is
vacuous here. -/
theorem adjoin_eq_top_expand_X_sub_C_iff {A : ℤ} {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k (X - C A))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤) (hmω : minpoly ℤ ω = expand ℤ k (X - C A)) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔
      (∀ q : ℕ, q.Prime → q ∣ k → ¬ (q : ℤ) ^ 2 ∣ A ^ q - A) ∧ Squarefree A := by
  have hfm : (X - C A : ℤ[X]).Monic := monic_X_sub_C A
  have hc0 : (X - C A : ℤ[X]).coeff 0 = -A := by simp
  have hdeg : (X - C A : ℤ[X]).natDegree ≤ 1 := (natDegree_X_sub_C A).le
  have hneg : ∀ z : ℤ, Squarefree (-z) ↔ Squarefree z := fun z => by
    rw [← Int.squarefree_natAbs, ← Int.squarefree_natAbs (n := z), Int.natAbs_neg]
  rw [adjoin_eq_top_expand_iff hfm hk hirr hω hmω]
  constructor
  · rintro ⟨-, h2, h3⟩
    refine ⟨fun q hq hqk hdvd => ?_, ?_⟩
    · haveI : Fact q.Prime := ⟨hq⟩
      exact h2 q hq hqk ((isIndexDivisor_expand_X_sub_C_iff A).mpr hdvd)
    · rwa [hc0, hneg] at h3
  · rintro ⟨h1, h2⟩
    refine ⟨fun q hq => ?_, fun q hq hqk hIdx => ?_, ?_⟩
    · haveI : Fact q.Prime := ⟨hq⟩
      exact not_isIndexDivisor_of_natDegree_le_one hfm hdeg
    · haveI : Fact q.Prime := ⟨hq⟩
      exact h1 q hq hqk ((isIndexDivisor_expand_X_sub_C_iff A).mp hIdx)
    · rw [hc0, hneg]
      exact h2

/-! ### Proposition 4.5: the Kaur–Kumar family `X ^ d + A (B X + 1) ^ m` -/

section Jones

variable {A B : ℤ} {d m : ℕ}

theorem natDegree_linear_pow_le (B : ℤ) (m : ℕ) :
    ((C B * X + 1 : ℤ[X]) ^ m).natDegree ≤ m := by
  refine le_trans natDegree_pow_le ?_
  have h1 : (C B * X + 1 : ℤ[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (natDegree_C_mul_le B X) natDegree_X_le
    · simp
  calc m * (C B * X + 1 : ℤ[X]).natDegree ≤ m * 1 := Nat.mul_le_mul_left m h1
  _ = m := mul_one m

theorem jonesPoly_monic (hmd : m < d) :
    (X ^ d + C A * (C B * X + 1) ^ m : ℤ[X]).Monic :=
  monic_of_eq_pow_add (h := (C B * X + 1) ^ m)
    (lt_of_le_of_lt (natDegree_linear_pow_le B m) hmd) rfl

theorem jonesPoly_coeff_zero_unit : IsUnit (((C B * X + 1 : ℤ[X]) ^ m).coeff 0) := by
  rw [coeff_zero_eq_eval_zero, eval_pow, eval_add, eval_mul, eval_C, eval_X, eval_one,
    mul_zero, zero_add, one_pow]
  exact isUnit_one

/-- **Proposition 4.5** of Kaur–Kumar–Remete.  For `f = X ^ d + A (B X + 1) ^ m` with
`0 < m < d` and `gcd(d, m B) = 1`, and `k ≥ 2` with `f(X ^ k)` irreducible, the polynomial
`f(X ^ k)` is monogenic if and only if both `A` and `D d m A B` are squarefree and no prime
`p ∣ k` is an index divisor of `f(X ^ p)`.

The first condition is monogenity of `f` itself, by the theorem of Kaur and Kumar
(`NumberField.KaurKumar.monogenic_iff`); the reduction to it is Theorem 1.14. -/
theorem adjoin_eq_top_expand_jones_iff (hm : 0 < m) (hmd : m < d)
    (hgcd : IsCoprime (d : ℤ) ((m : ℤ) * B)) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k (X ^ d + C A * (C B * X + 1) ^ m))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ k (X ^ d + C A * (C B * X + 1) ^ m)) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔
      (Squarefree A ∧ Squarefree (D d m A B)) ∧
      (∀ q : ℕ, q.Prime → q ∣ k →
        ¬ IsIndexDivisor q (expand ℤ q (X ^ d + C A * (C B * X + 1) ^ m))) := by
  have hfm : (X ^ d + C A * (C B * X + 1) ^ m).Monic := jonesPoly_monic hmd
  have hf1 : Irreducible (ratMap (X ^ d + C A * (C B * X + 1) ^ m)) := by
    have h := irreducible_ratMap_expand_of_dvd (f := (X ^ d + C A * (C B * X + 1) ^ m))
      (k := k) (t := 1) (by omega) (one_dvd k) hirr
    rwa [expand_one] at h
  haveI : Fact (Irreducible (ratMap (X ^ d + C A * (C B * X + 1) ^ m))) := ⟨hf1⟩
  -- monogenity of `f` is the Kaur–Kumar criterion
  have hmono : (∀ q : ℕ, q.Prime →
      ¬ IsIndexDivisor q (X ^ d + C A * (C B * X + 1) ^ m)) ↔
      (Squarefree A ∧ Squarefree (D d m A B)) := by
    have h1 := forall_not_isIndexDivisor_iff_adjoin_eq_top
      (θ := rootOfMonic (X ^ d + C A * (C B * X + 1) ^ m) hfm) (adjoin_rootOfMonic _ hfm)
    rw [minpoly_rootOfMonic] at h1
    rw [h1]
    exact NumberField.KaurKumar.monogenic_iff hm hmd hgcd (minpoly_rootOfMonic _ hfm)
      (adjoin_rootOfMonic _ hfm)
  rw [adjoin_eq_top_expand_iff_of_eq_pow_add (by omega)
    (lt_of_le_of_lt (natDegree_linear_pow_le B m) hmd) jonesPoly_coeff_zero_unit rfl hk hirr
    hω hmω, hmono]

/-- **Proposition 4.5**, the `rad k ∣ rad A` case.  When every prime divisor of `k` divides
`A`, monogenity of `f(X ^ k)` is squarefreeness of `A` and of `D d m A B` — no condition on
`k` beyond that remains. -/
theorem adjoin_eq_top_expand_jones_iff_of_dvd_radical (hm : 0 < m) (hmd : m < d)
    (hgcd : IsCoprime (d : ℤ) ((m : ℤ) * B)) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k (X ^ d + C A * (C B * X + 1) ^ m))))
    (hrad : ∀ q : ℕ, q.Prime → q ∣ k → (q : ℤ) ∣ A)
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ k (X ^ d + C A * (C B * X + 1) ^ m)) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔ Squarefree A ∧ Squarefree (D d m A B) := by
  have hfm : (X ^ d + C A * (C B * X + 1) ^ m).Monic := jonesPoly_monic hmd
  have hf1 : Irreducible (ratMap (X ^ d + C A * (C B * X + 1) ^ m)) := by
    have h := irreducible_ratMap_expand_of_dvd (f := (X ^ d + C A * (C B * X + 1) ^ m))
      (k := k) (t := 1) (by omega) (one_dvd k) hirr
    rwa [expand_one] at h
  haveI : Fact (Irreducible (ratMap (X ^ d + C A * (C B * X + 1) ^ m))) := ⟨hf1⟩
  have hmono : (∀ q : ℕ, q.Prime →
      ¬ IsIndexDivisor q (X ^ d + C A * (C B * X + 1) ^ m)) ↔
      (Squarefree A ∧ Squarefree (D d m A B)) := by
    have h1 := forall_not_isIndexDivisor_iff_adjoin_eq_top
      (θ := rootOfMonic (X ^ d + C A * (C B * X + 1) ^ m) hfm) (adjoin_rootOfMonic _ hfm)
    rw [minpoly_rootOfMonic] at h1
    rw [h1]
    exact NumberField.KaurKumar.monogenic_iff hm hmd hgcd (minpoly_rootOfMonic _ hfm)
      (adjoin_rootOfMonic _ hfm)
  rw [adjoin_eq_top_expand_iff_of_dvd_radical (by omega)
    (lt_of_le_of_lt (natDegree_linear_pow_le B m) hmd) jonesPoly_coeff_zero_unit rfl hk hirr
    hrad hω hmω, hmono]

end Jones

/-! ### Proposition 4.2: polynomials that split completely -/

/-- If `p ^ 2` divides `f(r ^ p)` for some integer `r`, then `p` is an index divisor of
`f(X ^ p)`.

Writing `f(X ^ p) = f ^ p + p * T`, the hypothesis forces `p ∣ f(r)` and hence `p ∣ T(r)`,
so `X - r` divides both reductions and they are not coprime. -/
theorem isIndexDivisor_expand_of_sq_dvd_eval {f : ℤ[X]} (hfm : f.Monic) {r : ℤ}
    (hr : (p : ℤ) ^ 2 ∣ f.eval (r ^ p)) : IsIndexDivisor p (expand ℤ p f) := by
  obtain ⟨T, hT⟩ := exists_expand_eq_pow_add_C_mul (p := p) f
  have hval : f.eval (r ^ p) = (f.eval r) ^ p + (p : ℤ) * T.eval r := by
    have h := congrArg (Polynomial.eval r) hT
    rwa [expand_eval, eval_add, eval_mul, eval_pow, eval_C] at h
  -- `p` divides `f(r)`
  have hpf : (p : ℤ) ∣ f.eval r := by
    have hp1 : (p : ℤ) ∣ (f.eval r) ^ p := by
      have : (p : ℤ) ∣ f.eval (r ^ p) := (dvd_pow_self _ two_ne_zero).trans hr
      rw [hval] at this
      exact (dvd_add_right (Dvd.intro _ rfl)).mp (by rwa [add_comm] at this)
    exact (Int.Prime.dvd_pow' hp.out hp1)
  -- hence `p` divides `T(r)`
  have hpT : (p : ℤ) ∣ T.eval r := by
    have hsq : (p : ℤ) ^ 2 ∣ (f.eval r) ^ p := by
      refine dvd_trans (pow_dvd_pow (p : ℤ) hp.out.two_le) (pow_dvd_pow_of_dvd hpf p)
    have h2 : (p : ℤ) ^ 2 ∣ (p : ℤ) * T.eval r := by
      have := dvd_sub hr hsq
      rwa [hval, add_sub_cancel_left] at this
    rw [sq] at h2
    exact (mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hp.out.ne_zero)).mp h2
  -- so `X - r` divides both reductions
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hT]
  intro hcop
  have hev : ∀ g : ℤ[X], (g.map (Int.castRingHom (ZMod p))).eval ((r : ZMod p)) =
      ((g.eval r : ℤ) : ZMod p) := fun g => by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod p)) r
  have hfr : (f.map (Int.castRingHom (ZMod p))).eval ((r : ZMod p)) = 0 := by
    rw [hev, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpf
  have hTr : (T.map (Int.castRingHom (ZMod p))).eval ((r : ZMod p)) = 0 := by
    rw [hev, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpT
  refine (irreducible_X_sub_C ((r : ZMod p))).not_isUnit (hcop.isUnit_of_dvd' ?_ ?_)
  · exact dvd_iff_isRoot.mpr hfr
  · exact dvd_iff_isRoot.mpr hTr

/-- Conversely, if `f` splits completely mod `p` and `p ^ 2 ∤ f(r ^ p)` for every
`r = 0, …, p - 1`, then `p` is not an index divisor of `f(X ^ p)`.

Splitting is what makes a common factor of the two reductions produce an actual residue
`r`: the gcd of the reductions is a nonunit dividing a split polynomial, hence has a root. -/
theorem not_isIndexDivisor_expand_of_splits {f : ℤ[X]} (hfm : f.Monic)
    (hsplit : Splits (f.map (Int.castRingHom (ZMod p))))
    (hr : ∀ r : ℕ, r < p → ¬ (p : ℤ) ^ 2 ∣ f.eval ((r : ℤ) ^ p)) :
    ¬ IsIndexDivisor p (expand ℤ p f) := by
  obtain ⟨T, hT⟩ := exists_expand_eq_pow_add_C_mul (p := p) f
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hT, not_not]
  by_contra hcop
  set F := f.map (Int.castRingHom (ZMod p)) with hF
  set G := T.map (Int.castRingHom (ZMod p)) with hG
  have hF0 : F ≠ 0 := (hfm.map _).ne_zero
  set d := EuclideanDomain.gcd F G with hd
  have hdunit : ¬ IsUnit d := fun h => hcop (EuclideanDomain.gcd_isUnit_iff.mp h)
  have hdsplit : Polynomial.Splits d :=
    Polynomial.Splits.of_dvd hsplit hF0 (EuclideanDomain.gcd_dvd_left F G)
  have hdeg : d.degree ≠ 0 := fun h => hdunit (isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨a, ha⟩ := hdsplit.exists_eval_eq_zero hdeg
  -- `a` is a common root of the two reductions
  have hFa : F.eval a = 0 := by
    obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_left F G
    rw [hc, eval_mul, ha, zero_mul]
  have hGa : G.eval a = 0 := by
    obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_right F G
    rw [hc, eval_mul, ha, zero_mul]
  -- lift it to a residue `r < p`
  obtain ⟨r, hrlt, hcast⟩ : ∃ r : ℕ, r < p ∧ ((r : ℤ) : ZMod p) = a :=
    ⟨a.val, ZMod.val_lt a, by rw [Int.cast_natCast]; exact ZMod.natCast_rightInverse a⟩
  refine hr r hrlt ?_
  have hev : ∀ g : ℤ[X], (g.map (Int.castRingHom (ZMod p))).eval a =
      ((g.eval (r : ℤ) : ℤ) : ZMod p) := fun g => by
    rw [Polynomial.eval_map, ← hcast]
    exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod p)) ((r : ℤ))
  have hpf : (p : ℤ) ∣ f.eval (r : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hev]; exact hFa
  have hpT : (p : ℤ) ∣ T.eval (r : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hev]; exact hGa
  have hval : f.eval ((r : ℤ) ^ p) =
      (f.eval (r : ℤ)) ^ p + (p : ℤ) * T.eval (r : ℤ) := by
    have h := congrArg (Polynomial.eval ((r : ℤ))) hT
    rwa [expand_eval, eval_add, eval_mul, eval_pow, eval_C] at h
  rw [hval]
  refine dvd_add ?_ ?_
  · exact dvd_trans (pow_dvd_pow (p : ℤ) hp.out.two_le) (pow_dvd_pow_of_dvd hpf p)
  · rw [sq]; exact mul_dvd_mul_left _ hpT

/-- **Proposition 4.2** of Kaur–Kumar–Remete.  If `f` splits completely modulo every prime
divisor of `k`, and `f(X ^ k)` is irreducible with `k ≥ 2`, then `f(X ^ k)` is monogenic if
and only if

1. `f` is monogenic,
2. `p ^ 2 ∤ f(r ^ p)` for every prime `p ∣ k` and every `r = 0, …, p - 1`, and
3. `f(0)` is squarefree.

This makes condition (2) of Theorem 1.1 a finite check for split families. -/
theorem adjoin_eq_top_expand_iff_of_splits {f : ℤ[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k f)))
    (hsplit : ∀ q : ℕ, q.Prime → q ∣ k → Splits (f.map (Int.castRingHom (ZMod q))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤) (hmω : minpoly ℤ ω = expand ℤ k f) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔
      (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q f) ∧
      (∀ q : ℕ, q.Prime → q ∣ k → ∀ r : ℕ, r < q → ¬ (q : ℤ) ^ 2 ∣ f.eval ((r : ℤ) ^ q)) ∧
      Squarefree (f.coeff 0) := by
  rw [adjoin_eq_top_expand_iff hfm hk hirr hω hmω]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  refine forall_congr' fun q => imp_congr_right fun hq => imp_congr_right fun hqk => ?_
  haveI : Fact q.Prime := ⟨hq⟩
  exact ⟨fun hnot r hrq hdvd => hnot (isIndexDivisor_expand_of_sq_dvd_eval hfm hdvd),
    fun h => not_isIndexDivisor_expand_of_splits hfm (hsplit q hq hqk) h⟩

/-! ### Examples 1.6, 1.7 and 1.9 -/

/-- **Example 1.6** of Kaur–Kumar–Remete: `f = X ^ 2 + X + 20`.  Although `f` is monogenic
and `3` does not divide the index of `f(X ^ 3)`, no `f(X ^ k)` with `k ≥ 2` is monogenic,
because `2 ^ 2` divides `f(0) = 20`.  This is the necessity of condition (3) of
Theorem 1.1. -/
theorem example_1_6 {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k (X ^ 2 + X + C 20))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ k (X ^ 2 + X + C 20)) :
    ¬ (Algebra.adjoin ℤ {ω} = ⊤) := by
  have hfm : (X ^ 2 + X + C 20 : ℤ[X]).Monic := by
    rw [show (X ^ 2 + X + C 20 : ℤ[X]) = X ^ 2 + (X + C 20) by ring]
    refine monic_X_pow_add (lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_))
    · rw [degree_X]; exact_mod_cast one_lt_two
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast two_pos)
  rw [adjoin_eq_top_expand_iff hfm hk hirr hω hmω]
  rintro ⟨-, -, h3⟩
  rw [show (X ^ 2 + X + C 20 : ℤ[X]).coeff 0 = 20 by simp] at h3
  have h2 := h3 2 ⟨5, by norm_num⟩
  rw [Int.isUnit_iff] at h2
  omega



private theorem squarefree_two_int : Squarefree (2 : ℤ) :=
  Int.prime_two.irreducible.squarefree

private theorem squarefree_three_int : Squarefree (3 : ℤ) :=
  Int.prime_three.irreducible.squarefree

private theorem squarefree_six_int : Squarefree (6 : ℤ) := by
  rw [show (6 : ℤ) = 2 * 3 by norm_num, squarefree_mul_iff]
  exact ⟨(Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).isRelPrime, squarefree_two_int,
    squarefree_three_int⟩

/-- **Example 1.9** of Kaur–Kumar–Remete: `f = X ^ 2 + 2 (X + 1)` and `k = 2 ^ u`.  Here
`rad k = 2 = rad A`, so `f(X ^ k)` is monogenic for every `u ≥ 1`. -/
theorem example_1_9 {u : ℕ} (hu : 0 < u)
    (hirr : Irreducible (ratMap (expand ℤ (2 ^ u) (X ^ 2 + C 2 * (C 1 * X + 1) ^ 1))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ (2 ^ u) (X ^ 2 + C 2 * (C 1 * X + 1) ^ 1)) :
    Algebra.adjoin ℤ {ω} = ⊤ := by
  have hk : 2 ≤ 2 ^ u := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu
  rw [adjoin_eq_top_expand_jones_iff_of_dvd_radical (A := 2) (B := 1) (d := 2) (m := 1)
    (by norm_num) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num) hk hirr ?_ hω hmω]
  · refine ⟨squarefree_two_int, ?_⟩
    rw [show D 2 1 2 1 = 2 by norm_num [D]]
    exact squarefree_two_int
  · intro q hq hqk
    have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqk)
    rw [this]
    norm_num

/-- **Example 1.7** of Kaur–Kumar–Remete: `f = X ^ 3 + 6 (X + 1) ^ 2` and `k = 2 ^ u 3 ^ v`.
Here `rad k ∣ 6 = rad A`, so `f(X ^ k)` is monogenic for all `u, v`. -/
theorem example_1_7 {k : ℕ} (hk : 2 ≤ k)
    (hrad : ∀ q : ℕ, q.Prime → q ∣ k → q = 2 ∨ q = 3)
    (hirr : Irreducible (ratMap (expand ℤ k (X ^ 3 + C 6 * (C 1 * X + 1) ^ 2))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ k (X ^ 3 + C 6 * (C 1 * X + 1) ^ 2)) :
    Algebra.adjoin ℤ {ω} = ⊤ := by
  rw [adjoin_eq_top_expand_jones_iff_of_dvd_radical (A := 6) (B := 1) (d := 3) (m := 2)
    (by norm_num) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num) hk hirr ?_ hω hmω]
  · refine ⟨squarefree_six_int, ?_⟩
    rw [show D 3 2 6 1 = 3 by norm_num [D]]
    exact squarefree_three_int
  · intro q hq hqk
    rcases hrad q hq hqk with rfl | rfl <;> norm_num

end RingOfIntegers
