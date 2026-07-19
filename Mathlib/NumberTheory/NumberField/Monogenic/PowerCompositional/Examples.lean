/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.NumberTheory.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
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

* `RingOfIntegers.isIndexDivisor_expand_of_dvd_X_pow_sub_one`: for a divisor of
  `X ^ n - 1`, every prime `p ∤ n` at which `f` has a root divides the index of `f(X ^ p)`.
  This settles Problem 1 of the paper for such `f`, and locates its difficulty: the
  mechanism is that `r ^ n ≡ 1 mod p` forces `(r ^ p) ^ n ≡ 1 mod p ^ 2`, so the answer is
  "all of them", whereas for `f = X - A` the same condition reads `p ^ 2 ∣ A ^ p - A` and
  the set of such `p` is the set of Wieferich primes to the base `A`.

* `RingOfIntegers.adjoin_eq_top_expand_simplestCubic_iff_of_reducible`: **Proposition 4.3**
  for the simplest cubics `X ^ 3 - m X ^ 2 - (m + 3) X - 1`, with the paper's own hypothesis
  that `f` is reducible modulo every odd prime divisor of `k`.  Two ingredients replace the
  paper's Galois-theoretic and computational steps:
  `RingOfIntegers.simplestCubic_eq_prod`, which writes the other two roots explicitly as
  `-1 / (a + 1)` and `-(a + 1) / a` so that reducible implies split with no Galois group in
  sight, and `RingOfIntegers.not_isIndexDivisor_two_simplestCubic`, which disposes of `p = 2`
  by explicit Bezout identities over `𝔽₂` in the four classes of `m` mod `4`.

* `RingOfIntegers.not_isIndexDivisor_expand_cyclotomic`: **Problem 1 has an empty answer for
  cyclotomic `f`**, which is the kind of example the paper asks for.  Supporting this,
  `RingOfIntegers.forall_not_isIndexDivisor_cyclotomic` records that no prime is an index
  divisor of a cyclotomic polynomial — cyclotomic fields are monogenic — and
  `RingOfIntegers.dvd_of_irreducible_expand_cyclotomic` that irreducibility of `Φ n (X ^ p)`
  forces `p ∣ n`.

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

/-! ### Problem 1: divisors of `X ^ n - 1` always produce index divisors -/

/-- **Roots of unity force index divisors.**  If `f` divides `X ^ n - 1` with `p ∤ n`, and
`f` has a root `r` modulo `p`, then `p` divides the index of `f(X ^ p)`.

This is the obstruction underlying Problem 1 of Kaur–Kumar–Remete.  A root `r` of `f` mod
`p` satisfies `r ^ n ≡ 1 mod p`, hence `(r ^ p) ^ n ≡ 1 mod p ^ 2` — raising to the `p`-th
power doubles the precision.  Separability of `X ^ n - 1` mod `p`, which is where `p ∤ n`
enters, transfers this from `X ^ n - 1` to the factor `f`, so `p ^ 2 ∣ f(r ^ p)` and
`RingOfIntegers.isIndexDivisor_expand_of_sq_dvd_eval` applies.

So for every divisor of `X ^ n - 1` the answer to Problem 1 is "every prime that has a root
and does not divide `n`" — the difficulty of the problem lies entirely in the polynomials
whose roots are not roots of unity. -/
theorem isIndexDivisor_expand_of_dvd_X_pow_sub_one {f g : ℤ[X]} (hfm : f.Monic) {n : ℕ}
    (hn : ¬ (p : ℕ) ∣ n) (hfg : (X : ℤ[X]) ^ n - 1 = f * g) {r : ℤ}
    (hr : (p : ℤ) ∣ f.eval r) : IsIndexDivisor p (expand ℤ p f) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  have hev : ∀ x : ℤ, x ^ n - 1 = f.eval x * g.eval x := fun x => by
    have h := congrArg (Polynomial.eval x) hfg
    simpa using h
  refine isIndexDivisor_expand_of_sq_dvd_eval (r := r) hfm ?_
  -- `p ∣ r ^ n - 1`, hence `p ^ 2 ∣ (r ^ p) ^ n - 1`
  have h1 : (p : ℤ) ∣ r ^ n - 1 := by rw [hev]; exact Dvd.dvd.mul_right hr _
  have h2 : (p : ℤ) ^ 2 ∣ (r ^ p) ^ n - 1 := by
    have h := dvd_sub_pow_of_dvd_sub (p := p) (a := r ^ n) (b := 1) (by simpa using h1) 1
    rw [pow_one, one_pow] at h
    push_cast at h
    rw [← pow_mul, mul_comm n p] at h
    rwa [← pow_mul]
  -- `p` does not divide `r`
  have hpr : ¬ (p : ℤ) ∣ r := by
    intro hdvd
    have : (p : ℤ) ∣ (1 : ℤ) := by
      have hrn : (p : ℤ) ∣ r ^ n := dvd_pow hdvd hn0
      simpa using dvd_sub hrn h1
    exact hpZ.not_unit (isUnit_of_dvd_one this)
  -- `r` is a simple root of `X ^ n - 1` mod `p`, so `p ∤ g(r)`
  have hgr : ¬ (p : ℤ) ∣ g.eval r := by
    intro hg
    have hder := congrArg (Polynomial.eval r) (congrArg derivative hfg)
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul,
      eval_add, eval_mul, eval_mul, eval_mul, eval_pow, eval_X, eval_C] at hder
    have hdvd : (p : ℤ) ∣ (n : ℤ) * r ^ (n - 1) := by
      rw [hder]
      exact dvd_add (Dvd.dvd.mul_left hg _) (Dvd.dvd.mul_right hr _)
    rcases hpZ.dvd_mul.mp hdvd with hpn | hprn
    · exact hn (by exact_mod_cast hpn)
    · exact hpr (hpZ.dvd_of_dvd_pow hprn)
  -- `g(r ^ p) ≡ g(r) mod p`, since `r ^ p ≡ r mod p`
  have hfermat : (p : ℤ) ∣ r ^ p - r := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hgrp : ¬ (p : ℤ) ∣ g.eval (r ^ p) := by
    intro hdvd
    refine hgr ?_
    have hsub : (p : ℤ) ∣ g.eval (r ^ p) - g.eval r :=
      dvd_trans hfermat (sub_dvd_eval_sub (r ^ p) r g)
    simpa using dvd_sub hdvd hsub
  -- conclude from `p ^ 2 ∣ f(r ^ p) * g(r ^ p)`
  have hcop : IsCoprime ((p : ℤ) ^ 2) (g.eval (r ^ p)) :=
    (hpZ.coprime_iff_not_dvd.mpr hgrp).pow_left
  exact hcop.dvd_of_dvd_mul_right (by rw [← hev]; exact h2)


/-! ### Proposition 4.3: the simplest cubics -/

/-! ### Proposition 4.3 at `p = 2` -/

private theorem cast_even (d : ℤ) : (((2*d : ℤ)) : ZMod 2) = 0 := by
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from by decide]
  ring

private theorem cast_odd (d : ℤ) : (((2*d + 1 : ℤ)) : ZMod 2) = 1 := by
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from by decide]
  ring

private theorem two_zmod_two : ((2 : (ZMod 2)[X])) = 0 := CharTwo.two_eq_zero

private theorem three_zmod_two : ((3 : (ZMod 2)[X])) = 1 := by
  rw [show (3 : (ZMod 2)[X]) = 2 + 1 by norm_num, two_zmod_two, zero_add]

private theorem four_zmod_two : ((4 : (ZMod 2)[X])) = 0 := by
  rw [show (4 : (ZMod 2)[X]) = 2 * 2 by norm_num, two_zmod_two, zero_mul]

private theorem five_zmod_two : ((5 : (ZMod 2)[X])) = 1 := by
  rw [show (5 : (ZMod 2)[X]) = 4 + 1 by norm_num, four_zmod_two, zero_add]

private theorem six_zmod_two : ((6 : (ZMod 2)[X])) = 0 := by
  rw [show (6 : (ZMod 2)[X]) = 2 * 3 by norm_num, two_zmod_two, zero_mul]

private theorem map_C_zmod (q : ℕ) (z : ℤ) :
    ((C z : ℤ[X]).map (Int.castRingHom (ZMod q))) = C ((z : ZMod q)) := by
  rw [Polynomial.map_C]; rfl

/-- Proposition 4.3 at `p = 2`, for `m ≡ 0` mod `4`: the reduction of `f` mod `2` is
irreducible and coprime to `(f(X ^ 2) - f ^ 2) / 2`, so `2` is not an index divisor. -/
private theorem not_isIndexDivisor_two_simplestCubic_0 (j : ℤ) :
    ¬ IsIndexDivisor 2 (expand ℤ 2 (X ^ 3 - C (4*j) * X ^ 2 - C (4*j + 3) * X - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ℤ[X] := X ^ 3 - C (4*j) * X ^ 2 - C (4*j + 3) * X - 1 with hf
  set T : ℤ[X] := C (4*j) * X ^ 5 + C (-8*j^2+2*j+3) * X ^ 4
      + C (-16*j^2-12*j+1) * X ^ 3 + C (-8*j^2-18*j-6) * X ^ 2 + C (-(4*j+3)) * X - 1 with hT
  have hfm : f.Monic := by rw [hf]; monicity!
  have hid : expand ℤ 2 f = f ^ 2 + C 2 * T := by
    simp only [hf, hT, map_sub, map_mul, map_pow, map_one, map_add, map_neg, map_ofNat,
      expand_C, expand_X]
    ring
  have ea : (((4*j : ℤ)) : ZMod 2) = 0 := by
    rw [show ((4*j : ℤ)) = 2*(2*j) from by ring, cast_even]
  have eb : (((4*j + 3 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((4*j + 3 : ℤ)) = 2*(2*j+1) + 1 from by ring, cast_odd]
  have e0 : (((4*j : ℤ)) : ZMod 2) = 0 := by
    rw [show ((4*j : ℤ)) = 2*(2*j) from by ring, cast_even]
  have e1 : (((-8*j^2+2*j+3 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-8*j^2+2*j+3 : ℤ)) = 2*(-4*j^2+j+1) + 1 from by ring, cast_odd]
  have e2 : (((-16*j^2-12*j+1 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-16*j^2-12*j+1 : ℤ)) = 2*(-8*j^2-6*j) + 1 from by ring, cast_odd]
  have e3 : (((-8*j^2-18*j-6 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((-8*j^2-18*j-6 : ℤ)) = 2*(-4*j^2-9*j-3) from by ring, cast_even]
  have e4 : (((-(4*j+3) : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-(4*j+3) : ℤ)) = 2*(-2*j-2) + 1 from by ring, cast_odd]
  have hfmap : f.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
    rw [hf, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_C_zmod, map_C_zmod, ea, eb]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero]
  have hTmap : T.map (Int.castRingHom (ZMod 2)) = X ^ 4 + X ^ 3 + X + 1 := by
    rw [hT]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, map_C_zmod, e0, e1, e2, e3, e4]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero,
      zero_add]
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hid, not_not, hfmap, hTmap]
  refine ⟨X ^ 2, X + 1, ?_⟩
  ring_nf
  simp [two_zmod_two]

/-- Proposition 4.3 at `p = 2`, for `m ≡ 1` mod `4`: the reduction of `f` mod `2` is
irreducible and coprime to `(f(X ^ 2) - f ^ 2) / 2`, so `2` is not an index divisor. -/
private theorem not_isIndexDivisor_two_simplestCubic_1 (j : ℤ) :
    ¬ IsIndexDivisor 2 (expand ℤ 2 (X ^ 3 - C (4*j + 1) * X ^ 2 - C (4*j + 4) * X - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ℤ[X] := X ^ 3 - C (4*j + 1) * X ^ 2 - C (4*j + 4) * X - 1 with hf
  set T : ℤ[X] := C (4*j+1) * X ^ 5 + C (-8*j^2-2*j+3) * X ^ 4
      + C (-16*j^2-20*j-3) * X ^ 3 + C (-8*j^2-22*j-11) * X ^ 2 + C (-(4*j+4)) * X - 1 with hT
  have hfm : f.Monic := by rw [hf]; monicity!
  have hid : expand ℤ 2 f = f ^ 2 + C 2 * T := by
    simp only [hf, hT, map_sub, map_mul, map_pow, map_one, map_add, map_neg, map_ofNat,
      expand_C, expand_X]
    ring
  have ea : (((4*j + 1 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((4*j + 1 : ℤ)) = 2*(2*j) + 1 from by ring, cast_odd]
  have eb : (((4*j + 4 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((4*j + 4 : ℤ)) = 2*(2*j+2) from by ring, cast_even]
  have e0 : (((4*j+1 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((4*j+1 : ℤ)) = 2*(2*j) + 1 from by ring, cast_odd]
  have e1 : (((-8*j^2-2*j+3 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-8*j^2-2*j+3 : ℤ)) = 2*(-4*j^2-j+1) + 1 from by ring, cast_odd]
  have e2 : (((-16*j^2-20*j-3 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-16*j^2-20*j-3 : ℤ)) = 2*(-8*j^2-10*j-2) + 1 from by ring, cast_odd]
  have e3 : (((-8*j^2-22*j-11 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-8*j^2-22*j-11 : ℤ)) = 2*(-4*j^2-11*j-6) + 1 from by ring, cast_odd]
  have e4 : (((-(4*j+4) : ℤ)) : ZMod 2) = 0 := by
    rw [show ((-(4*j+4) : ℤ)) = 2*(-2*j-2) from by ring, cast_even]
  have hfmap : f.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X ^ 2 + 1 := by
    rw [hf, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_C_zmod, map_C_zmod, ea, eb]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero]
  have hTmap : T.map (Int.castRingHom (ZMod 2)) = X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1 := by
    rw [hT]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, map_C_zmod, e0, e1, e2, e3, e4]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero]
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hid, not_not, hfmap, hTmap]
  refine ⟨X ^ 3 + X ^ 2 + X, X + 1, ?_⟩
  ring_nf
  simp [two_zmod_two, four_zmod_two]

/-- Proposition 4.3 at `p = 2`, for `m ≡ 2` mod `4`: the reduction of `f` mod `2` is
irreducible and coprime to `(f(X ^ 2) - f ^ 2) / 2`, so `2` is not an index divisor. -/
private theorem not_isIndexDivisor_two_simplestCubic_2 (j : ℤ) :
    ¬ IsIndexDivisor 2 (expand ℤ 2 (X ^ 3 - C (4*j + 2) * X ^ 2 - C (4*j + 5) * X - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ℤ[X] := X ^ 3 - C (4*j + 2) * X ^ 2 - C (4*j + 5) * X - 1 with hf
  set T : ℤ[X] := C (4*j+2) * X ^ 5 + C (-8*j^2-6*j+2) * X ^ 4
      + C (-16*j^2-28*j-9) * X ^ 3 + C (-8*j^2-26*j-17) * X ^ 2 + C (-(4*j+5)) * X - 1 with hT
  have hfm : f.Monic := by rw [hf]; monicity!
  have hid : expand ℤ 2 f = f ^ 2 + C 2 * T := by
    simp only [hf, hT, map_sub, map_mul, map_pow, map_one, map_add, map_neg, map_ofNat,
      expand_C, expand_X]
    ring
  have ea : (((4*j + 2 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((4*j + 2 : ℤ)) = 2*(2*j+1) from by ring, cast_even]
  have eb : (((4*j + 5 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((4*j + 5 : ℤ)) = 2*(2*j+2) + 1 from by ring, cast_odd]
  have e0 : (((4*j+2 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((4*j+2 : ℤ)) = 2*(2*j+1) from by ring, cast_even]
  have e1 : (((-8*j^2-6*j+2 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((-8*j^2-6*j+2 : ℤ)) = 2*(-4*j^2-3*j+1) from by ring, cast_even]
  have e2 : (((-16*j^2-28*j-9 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-16*j^2-28*j-9 : ℤ)) = 2*(-8*j^2-14*j-5) + 1 from by ring, cast_odd]
  have e3 : (((-8*j^2-26*j-17 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-8*j^2-26*j-17 : ℤ)) = 2*(-4*j^2-13*j-9) + 1 from by ring, cast_odd]
  have e4 : (((-(4*j+5) : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-(4*j+5) : ℤ)) = 2*(-2*j-3) + 1 from by ring, cast_odd]
  have hfmap : f.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
    rw [hf, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_C_zmod, map_C_zmod, ea, eb]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero]
  have hTmap : T.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X ^ 2 + X + 1 := by
    rw [hT]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, map_C_zmod, e0, e1, e2, e3, e4]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero,
      zero_add]
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hid, not_not, hfmap, hTmap]
  refine ⟨X ^ 2, X ^ 2 + X + 1, ?_⟩
  ring_nf
  simp [two_zmod_two, four_zmod_two]

/-- Proposition 4.3 at `p = 2`, for `m ≡ 3` mod `4`: the reduction of `f` mod `2` is
irreducible and coprime to `(f(X ^ 2) - f ^ 2) / 2`, so `2` is not an index divisor. -/
private theorem not_isIndexDivisor_two_simplestCubic_3 (j : ℤ) :
    ¬ IsIndexDivisor 2 (expand ℤ 2 (X ^ 3 - C (4*j + 3) * X ^ 2 - C (4*j + 6) * X - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ℤ[X] := X ^ 3 - C (4*j + 3) * X ^ 2 - C (4*j + 6) * X - 1 with hf
  set T : ℤ[X] := C (4*j+3) * X ^ 5 + C (-8*j^2-10*j) * X ^ 4
      + C (-16*j^2-36*j-17) * X ^ 3 + C (-8*j^2-30*j-24) * X ^ 2 + C (-(4*j+6)) * X - 1 with hT
  have hfm : f.Monic := by rw [hf]; monicity!
  have hid : expand ℤ 2 f = f ^ 2 + C 2 * T := by
    simp only [hf, hT, map_sub, map_mul, map_pow, map_one, map_add, map_neg, map_ofNat,
      expand_C, expand_X]
    ring
  have ea : (((4*j + 3 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((4*j + 3 : ℤ)) = 2*(2*j+1) + 1 from by ring, cast_odd]
  have eb : (((4*j + 6 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((4*j + 6 : ℤ)) = 2*(2*j+3) from by ring, cast_even]
  have e0 : (((4*j+3 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((4*j+3 : ℤ)) = 2*(2*j+1) + 1 from by ring, cast_odd]
  have e1 : (((-8*j^2-10*j : ℤ)) : ZMod 2) = 0 := by
    rw [show ((-8*j^2-10*j : ℤ)) = 2*(-4*j^2-5*j) from by ring, cast_even]
  have e2 : (((-16*j^2-36*j-17 : ℤ)) : ZMod 2) = 1 := by
    rw [show ((-16*j^2-36*j-17 : ℤ)) = 2*(-8*j^2-18*j-9) + 1 from by ring, cast_odd]
  have e3 : (((-8*j^2-30*j-24 : ℤ)) : ZMod 2) = 0 := by
    rw [show ((-8*j^2-30*j-24 : ℤ)) = 2*(-4*j^2-15*j-12) from by ring, cast_even]
  have e4 : (((-(4*j+6) : ℤ)) : ZMod 2) = 0 := by
    rw [show ((-(4*j+6) : ℤ)) = 2*(-2*j-3) from by ring, cast_even]
  have hfmap : f.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X ^ 2 + 1 := by
    rw [hf, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_C_zmod, map_C_zmod, ea, eb]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero]
  have hTmap : T.map (Int.castRingHom (ZMod 2)) = X ^ 5 + X ^ 3 + 1 := by
    rw [hT]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, map_C_zmod, e0, e1, e2, e3, e4]
    simp only [map_zero, C_1, zero_mul, one_mul, sub_eq_add_neg, CharTwo.neg_eq, add_zero]
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hid, not_not, hfmap, hTmap]
  refine ⟨X ^ 4 + X ^ 3 + X ^ 2, X ^ 2 + 1, ?_⟩
  ring_nf
  simp [two_zmod_two, four_zmod_two]

/-- **Proposition 4.3 at `p = 2`.**  For every `m`, the prime `2` is not an index divisor of
`f(X ^ 2)`, where `f = X ^ 3 - m X ^ 2 - (m + 3) X - 1`.

The reduction of `f` mod `2` is `X ^ 3 + X + 1` or `X ^ 3 + X ^ 2 + 1` according to the parity
of `m`, and in each of the four classes of `m` mod `4` an explicit Bezout identity shows that
it is coprime to `(f(X ^ 2) - f ^ 2) / 2`; the class of `m` mod `4`, not just mod `2`, is what
matters because the coefficients of that quotient involve `m (m + 1) / 2`. -/
theorem not_isIndexDivisor_two_simplestCubic (m : ℤ) :
    ¬ IsIndexDivisor 2 (expand ℤ 2 (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1)) := by
  obtain ⟨j, r, hr0, hr4, rfl⟩ : ∃ j r : ℤ, 0 ≤ r ∧ r < 4 ∧ m = 4 * j + r :=
    ⟨m / 4, m % 4, Int.emod_nonneg m (by norm_num), Int.emod_lt_of_pos m (by norm_num), by omega⟩
  interval_cases r
  · rw [show (4*j + 0 : ℤ) = 4*j from by ring]
    exact not_isIndexDivisor_two_simplestCubic_0 j
  · rw [show (4*j + 1 + 3 : ℤ) = 4*j + 4 from by ring]
    exact not_isIndexDivisor_two_simplestCubic_1 j
  · rw [show (4*j + 2 + 3 : ℤ) = 4*j + 5 from by ring]
    exact not_isIndexDivisor_two_simplestCubic_2 j
  · rw [show (4*j + 3 + 3 : ℤ) = 4*j + 6 from by ring]
    exact not_isIndexDivisor_two_simplestCubic_3 j

/-! ### The simplest cubics split wherever they are reducible -/

/-- **Shanks' simplest cubic cycles its roots.**  If `a` is a root of
`X ^ 3 - m X ^ 2 - (m + 3) X - 1` over a field, then so are `-1 / (a + 1)` and
`-(a + 1) / a`, and the polynomial is the product of the three corresponding linear factors.

This is the cyclic structure of the simplest cubics — the map `a ↦ -1 / (a + 1)` has order
three — and it is what replaces the Galois-theoretic input of the paper: no Galois group is
needed, the two other roots are written down. -/
theorem simplestCubic_eq_prod {K : Type*} [Field K] (m : K) {a : K}
    (ha : a ^ 3 - m * a ^ 2 - (m + 3) * a - 1 = 0) :
    (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : K[X])
      = (X - C a) * (X - C (-1 / (a + 1))) * (X - C (-(a + 1) / a)) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have ha1 : a + 1 ≠ 0 := by
    intro h
    have hval : a = -1 := by linear_combination h
    subst hval
    exact one_ne_zero (by linear_combination ha : (1 : K) = 0)
  set b := -1 / (a + 1) with hb
  set c := -(a + 1) / a with hc
  have hs1 : a + b + c = m := by rw [hb, hc]; field_simp; linear_combination ha
  have hs2 : a * b + b * c + c * a = -(m + 3) := by
    rw [hb, hc]; field_simp; linear_combination -ha
  have hs3 : a * b * c = 1 := by rw [hb, hc]; field_simp
  rw [show (X - C a) * (X - C b) * (X - C c)
      = X ^ 3 - (C a + C b + C c) * X ^ 2 + (C a * C b + C b * C c + C c * C a) * X
        - C a * C b * C c from by ring]
  simp only [← C_add, ← C_mul]
  rw [hs1, hs2, hs3, C_neg, C_1]
  ring

/-- The simplest cubic splits over any field in which it has a root. -/
theorem simplestCubic_splits_of_root {K : Type*} [Field K] (m : K) {a : K}
    (ha : a ^ 3 - m * a ^ 2 - (m + 3) * a - 1 = 0) :
    Splits (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : K[X]) := by
  rw [simplestCubic_eq_prod m ha]
  exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)

/-- **Reducible implies split, for the simplest cubics.**  Over any field, if
`X ^ 3 - m X ^ 2 - (m + 3) X - 1` is not irreducible then it splits completely.

A cubic that is not irreducible has a root, and by `simplestCubic_splits_of_root` one root
produces the other two. -/
theorem simplestCubic_splits_of_not_irreducible {K : Type*} [Field K] (m : K)
    (h : ¬ Irreducible (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : K[X])) :
    Splits (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : K[X]) := by
  have hm : (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : K[X]).Monic := by monicity!
  have hd : (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : K[X]).natDegree = 3 := by
    compute_degree!
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hm (by omega)
    (by omega)] at h
  obtain ⟨a, hmem⟩ := Multiset.exists_mem_of_ne_zero h
  rw [mem_roots hm.ne_zero, IsRoot.def] at hmem
  refine simplestCubic_splits_of_root (a := a) m ?_
  have := hmem
  simp only [eval_sub, eval_pow, eval_mul, eval_C, eval_X, eval_one] at this
  linear_combination this


/-- **Proposition 4.3** of Kaur–Kumar–Remete for the simplest cubics
`f = X ^ 3 - m X ^ 2 - (m + 3) X - 1`.

Since `f(0) = -1` is a unit, condition (3) of Theorem 1.1 is automatic, so monogenity of
`f(X ^ k)` reduces to monogenity of `f` together with one finite congruence check per odd
prime divisor of `k`.  The prime `2` needs no condition at all: it is never an index divisor
of `f(X ^ 2)`, by `RingOfIntegers.not_isIndexDivisor_two_simplestCubic`.

The splitting of `f` modulo the odd primes dividing `k` is a hypothesis here.  The paper
derives it from the Galois group of `f` being cyclic of order three, so that reducibility
mod `p` already forces complete splitting; that step is not formalised.  Note that `f` is
irreducible modulo `2` for every `m` — its reduction is `X ^ 3 + X + 1` or `X ^ 3 + X ^ 2 + 1`
— which is why the hypothesis excludes `q = 2` and that prime is handled separately. -/
theorem adjoin_eq_top_expand_simplestCubic_iff (m : ℤ) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1))))
    (hsplit : ∀ q : ℕ, q.Prime → q ∣ k → q ≠ 2 →
      Splits (((X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X])).map (Int.castRingHom (ZMod q))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ k (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1)) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔
      (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1)) ∧
      (∀ q : ℕ, q.Prime → q ∣ k → q ≠ 2 → ∀ r : ℕ, r < q →
        ¬ (q : ℤ) ^ 2 ∣ ((r : ℤ) ^ q) ^ 3 - m * ((r : ℤ) ^ q) ^ 2
          - (m + 3) * ((r : ℤ) ^ q) - 1) := by
  have hfm : (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X]).Monic := by monicity!
  have hc0 : (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X]).coeff 0 = -1 := by simp
  have hsf : Squarefree ((X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X]).coeff 0) := by
    rw [hc0]; exact (isUnit_one.neg).squarefree
  have heval : ∀ x : ℤ, (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X]).eval x
      = x ^ 3 - m * x ^ 2 - (m + 3) * x - 1 := by
    intro x; simp
  rw [adjoin_eq_top_expand_iff hfm hk hirr hω hmω, and_iff_left hsf]
  refine and_congr_right fun _ => ⟨fun h q hq hqk hq2 r hrq hdvd => ?_, fun h q hq hqk => ?_⟩
  · haveI : Fact q.Prime := ⟨hq⟩
    exact h q hq hqk (isIndexDivisor_expand_of_sq_dvd_eval hfm (by rw [heval]; exact hdvd))
  · haveI : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q = 2
    · subst hq2
      exact not_isIndexDivisor_two_simplestCubic m
    · exact not_isIndexDivisor_expand_of_splits hfm (hsplit q hq hqk hq2)
        fun r hrq => by rw [heval]; exact h q hq hqk hq2 r hrq

/-- **Proposition 4.3** of Kaur–Kumar–Remete, with the paper's own hypothesis: `f` is
*reducible* modulo every odd prime divisor of `k`.

For the simplest cubics reducible implies split (`simplestCubic_splits_of_not_irreducible`),
so no Galois theory and no splitting hypothesis is needed; and the prime `2` is handled by
`not_isIndexDivisor_two_simplestCubic`.  This is the full statement of the paper's
Proposition 4.3, with condition (ii) in the undivided form `q ^ 2 ∤ f(r ^ q)`. -/
theorem adjoin_eq_top_expand_simplestCubic_iff_of_reducible (m : ℤ) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1))))
    (hred : ∀ q : ℕ, q.Prime → q ∣ k → q ≠ 2 →
      ¬ Irreducible (((X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X])).map
        (Int.castRingHom (ZMod q))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ k (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1)) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔
      (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q (X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1)) ∧
      (∀ q : ℕ, q.Prime → q ∣ k → q ≠ 2 → ∀ r : ℕ, r < q →
        ¬ (q : ℤ) ^ 2 ∣ ((r : ℤ) ^ q) ^ 3 - m * ((r : ℤ) ^ q) ^ 2
          - (m + 3) * ((r : ℤ) ^ q) - 1) := by
  refine adjoin_eq_top_expand_simplestCubic_iff m hk hirr (fun q hq hqk hq2 => ?_) hω hmω
  haveI : Fact q.Prime := ⟨hq⟩
  have hmap : ((X ^ 3 - C m * X ^ 2 - C (m + 3) * X - 1 : ℤ[X])).map (Int.castRingHom (ZMod q))
      = X ^ 3 - C ((m : ZMod q)) * X ^ 2 - C (((m : ZMod q) + 3)) * X - 1 := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_C_zmod, map_C_zmod]
    push_cast
    ring
  rw [hmap]
  exact simplestCubic_splits_of_not_irreducible _ (by rw [← hmap]; exact hred q hq hqk hq2)


/-- **Problem 1 for divisors of `X ^ n - 1`, without the root hypothesis.**  If `f` is a
monic divisor of `X ^ n - 1` of positive degree and `p ∤ n`, then `p` divides the index of
`f(X ^ p)`.  No assumption that `f` has a root modulo `p` is needed.

`isIndexDivisor_expand_of_dvd_X_pow_sub_one` exploits a factor of `f` of degree one, via
the congruence `r ^ n ≡ 1 mod p ⇒ (r ^ p) ^ n ≡ 1 mod p ^ 2`.  The argument here works with
an arbitrary irreducible factor `π` of `f mod p` instead.  Writing
`X ^ p - 1 = (X - 1) ^ p + p V` and evaluating at `1` gives `V(1) = 0`, so `X - 1` divides
`V` and hence `X ^ n - 1` divides `V(X ^ n)`.  Expanding `X ^ (n p) - 1` in the two
available ways gives `T g ^ p + T' f ^ p + p T T' = V(X ^ n)`, where
`f(X ^ p) = f ^ p + p T` and `g(X ^ p) = g ^ p + p T'`.  Modulo `π` — which divides `f`,
hence `V(X ^ n)` — this leaves `π ∣ T ḡ ^ p`, and `π ∤ ḡ` because `X ^ n - 1` is separable
mod `p`.  So `π ∣ T̄`, and `f` and `T` are not coprime mod `p`. -/
theorem isIndexDivisor_expand_of_dvd_X_pow_sub_one_of_natDegree_pos {f g : ℤ[X]}
    (hfm : f.Monic) {n : ℕ} (hn : ¬ (p : ℕ) ∣ n) (hfg : (X : ℤ[X]) ^ n - 1 = f * g)
    (hdeg : 0 < f.natDegree) :
    IsIndexDivisor p (expand ℤ p f) := by
  obtain ⟨T, hT⟩ := exists_expand_eq_pow_add_C_mul (p := p) f
  obtain ⟨T', hT'⟩ := exists_expand_eq_pow_add_C_mul (p := p) g
  obtain ⟨V, hV⟩ := exists_expand_eq_pow_add_C_mul (p := p) (X - 1 : ℤ[X])
  have hpne : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hexp1 : expand ℤ p (X - 1 : ℤ[X]) = X ^ p - 1 := by
    rw [map_sub, expand_X, map_one]
  have hXp : (X : ℤ[X]) ^ p - 1 = ((X : ℤ[X]) - 1) ^ p + C (p : ℤ) * V := by
    rw [← hexp1, hV]
  -- `V(1) = 0`, hence `X - 1 ∣ V`
  have hV1 : V.eval 1 = 0 := by
    have h := congrArg (Polynomial.eval (1 : ℤ)) hXp
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_add, eval_mul, eval_C, one_pow,
      sub_self, zero_pow hp.out.ne_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hpne
  have hXV : (X - 1 : ℤ[X]) ∣ V := by
    have h := dvd_iff_isRoot.mpr (show V.IsRoot 1 from hV1)
    rwa [map_one] at h
  -- hence `X ^ n - 1 ∣ V(X ^ n)`
  have hUdvd : (X : ℤ[X]) ^ n - 1 ∣ expand ℤ n V := by
    have h := map_dvd (expand ℤ n) hXV
    rwa [map_sub, expand_X, map_one] at h
  -- the two expansions of `X ^ (n p) - 1`
  have hboth : expand ℤ p ((X : ℤ[X]) ^ n - 1) = expand ℤ n ((X : ℤ[X]) ^ p - 1) := by
    rw [map_sub, map_sub, map_pow, map_pow, expand_X, expand_X, map_one, map_one,
      ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hL : expand ℤ p ((X : ℤ[X]) ^ n - 1)
      = (f ^ p + C (p : ℤ) * T) * (g ^ p + C (p : ℤ) * T') := by
    rw [hfg, map_mul, hT, hT']
  have hR : expand ℤ n ((X : ℤ[X]) ^ p - 1)
      = ((X : ℤ[X]) ^ n - 1) ^ p + C (p : ℤ) * expand ℤ n V := by
    rw [hXp, map_add, map_pow, map_mul, map_sub, expand_X, map_one, expand_C]
  have hkey : T * g ^ p + T' * f ^ p + C (p : ℤ) * (T * T') = expand ℤ n V := by
    have heq : (f ^ p + C (p : ℤ) * T) * (g ^ p + C (p : ℤ) * T')
        = (f * g) ^ p + C (p : ℤ) * expand ℤ n V := by
      rw [← hL, hboth, hR, hfg]
    rw [mul_pow] at heq
    have hCp : (C (p : ℤ) : ℤ[X]) ≠ 0 := fun h => hpne (by simpa using congrArg (coeff · 0) h)
    apply mul_left_cancel₀ hCp
    linear_combination heq
  -- reduce modulo `p`
  have hzero : ((C (p : ℤ) : ℤ[X])).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_C]
    simp
  have hmap : T.map (Int.castRingHom (ZMod p)) * (g.map (Int.castRingHom (ZMod p))) ^ p
      + (T'.map (Int.castRingHom (ZMod p))) * (f.map (Int.castRingHom (ZMod p))) ^ p
      = (expand ℤ n V).map (Int.castRingHom (ZMod p)) := by
    have h := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hkey
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, hzero, zero_mul,
      add_zero] at h
    exact h
  -- an irreducible factor of `f` mod `p`
  have hfbar0 : f.map (Int.castRingHom (ZMod p)) ≠ 0 := (hfm.map _).ne_zero
  have hfbardeg : 0 < (f.map (Int.castRingHom (ZMod p))).natDegree := by
    rwa [hfm.natDegree_map]
  have hfbarnu : ¬ IsUnit (f.map (Int.castRingHom (ZMod p))) := by
    intro hu
    rw [natDegree_eq_zero_of_isUnit hu] at hfbardeg
    exact absurd hfbardeg (by omega)
  obtain ⟨π, hπirr, hπf⟩ := WfDvdMonoid.exists_irreducible_factor hfbarnu hfbar0
  -- `π` divides `V(X ^ n)` mod `p`, since `f` does
  have hfU : f ∣ expand ℤ n V := (Dvd.intro g hfg.symm).trans hUdvd
  have hπU : π ∣ (expand ℤ n V).map (Int.castRingHom (ZMod p)) :=
    hπf.trans (Polynomial.map_dvd _ hfU)
  -- `π` does not divide `g` mod `p`, by separability of `X ^ n - 1`
  have hsep : ((X : (ZMod p)[X]) ^ n - 1).Separable := by
    have h := separable_X_pow_sub_C' p n (1 : ZMod p) hn one_ne_zero
    rwa [map_one] at h
  have hfgmap : f.map (Int.castRingHom (ZMod p)) * g.map (Int.castRingHom (ZMod p))
      = (X : (ZMod p)[X]) ^ n - 1 := by
    have h := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hfg
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      Polynomial.map_mul] at h
    exact h.symm
  have hcopfg : IsCoprime (f.map (Int.castRingHom (ZMod p)))
      (g.map (Int.castRingHom (ZMod p))) := (hfgmap ▸ hsep).isCoprime
  have hπg : ¬ π ∣ g.map (Int.castRingHom (ZMod p)) := fun h =>
    hπirr.not_isUnit (hcopfg.isUnit_of_dvd' hπf h)
  -- therefore `π ∣ T` mod `p`
  have hπT : π ∣ T.map (Int.castRingHom (ZMod p)) := by
    have h1 : π ∣ T.map (Int.castRingHom (ZMod p)) *
        (g.map (Int.castRingHom (ZMod p))) ^ p := by
      have hrw : T.map (Int.castRingHom (ZMod p)) * (g.map (Int.castRingHom (ZMod p))) ^ p
          = (expand ℤ n V).map (Int.castRingHom (ZMod p))
            - (T'.map (Int.castRingHom (ZMod p))) *
              (f.map (Int.castRingHom (ZMod p))) ^ p := by
        linear_combination hmap
      rw [hrw]
      exact dvd_sub hπU ((dvd_pow hπf hp.out.ne_zero).mul_left _)
    rcases hπirr.prime.dvd_mul.mp h1 with h | h
    · exact h
    · exact absurd (hπirr.prime.dvd_of_dvd_pow h) hπg
  rw [isIndexDivisor_expand_iff_not_isCoprime hfm hT]
  exact fun hcop => hπirr.not_isUnit (hcop.isUnit_of_dvd' hπf hπT)

/-! ### Problem 1 for cyclotomic polynomials: the answer is empty -/

/-- If `ℤ[θ]` is the integral closure of `ℤ` in `K`, then `θ`, viewed in `𝓞 K`, generates
it. -/
theorem adjoin_eq_top_of_isIntegralClosure {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
    (h : IsIntegralClosure (Algebra.adjoin ℤ ({(θ : K)} : Set K)) ℤ K) :
    Algebra.adjoin ℤ ({θ} : Set (𝓞 K)) = ⊤ := by
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  refine Algebra.eq_top_iff.mpr fun x => ?_
  obtain ⟨y, hy⟩ := h.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe x)
  have hxmem : (algebraMap (𝓞 K) K x) ∈ Algebra.adjoin ℤ ({(θ : K)} : Set K) := by
    rw [← hy]; exact y.2
  have himg : Algebra.adjoin ℤ ({(θ : K)} : Set K) =
      (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K) := by
    rw [← Algebra.adjoin_image]
    congr 1
    simp
  rw [himg] at hxmem
  obtain ⟨x', hx'mem, hx'eq⟩ := hxmem
  rwa [← hinj hx'eq]

/-- **No prime is an index divisor of a cyclotomic polynomial**: cyclotomic fields are
monogenic, `ℤ[ζ] = 𝓞 ℚ(ζ)`, which in the vocabulary of Uchida's criterion says exactly
this. -/
theorem forall_not_isIndexDivisor_cyclotomic {m : ℕ} (hm : 0 < m) :
    ∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q (cyclotomic m ℤ) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero ((m : ℕ) : ℚ) := ⟨by exact_mod_cast hm.ne'⟩
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension _ _
  haveI := IsCyclotomicExtension.numberField {m} ℚ (CyclotomicField m ℚ)
  set ζ := IsCyclotomicExtension.zeta m ℚ (CyclotomicField m ℚ) with hζdef
  have hζ : IsPrimitiveRoot ζ m := IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hm
  set θ : 𝓞 (CyclotomicField m ℚ) := ⟨ζ, hint⟩ with hθ
  have hcoe : (θ : CyclotomicField m ℚ) = ζ := rfl
  have hmin : minpoly ℤ θ = cyclotomic m ℤ := by
    rw [← RingOfIntegers.minpoly_coe, hcoe]
    exact (cyclotomic_eq_minpoly hζ hm).symm
  have hgen : Algebra.adjoin ℚ {(θ : CyclotomicField m ℚ)} = ⊤ := by
    rw [hcoe]; exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop : Algebra.adjoin ℤ ({θ} : Set (𝓞 (CyclotomicField m ℚ))) = ⊤ :=
    adjoin_eq_top_of_isIntegralClosure
      (by rw [hcoe]; exact IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ)
  have hall := (forall_not_isIndexDivisor_iff_adjoin_eq_top hgen).mpr htop
  rwa [hmin] at hall

/-- If `Φ n (X ^ p)` is irreducible then `p ∣ n`, since otherwise
`Φ n (X ^ p) = Φ (n p) * Φ n`. -/
theorem dvd_of_irreducible_expand_cyclotomic {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible (ratMap (expand ℤ p (cyclotomic n ℤ)))) : p ∣ n := by
  by_contra hdvd
  rw [cyclotomic_expand_eq_cyclotomic_mul hp.out hdvd ℤ] at hirr
  have hmap : ratMap (cyclotomic (n * p) ℤ * cyclotomic n ℤ) =
      cyclotomic (n * p) ℚ * cyclotomic n ℚ := by
    simp [ratMap, Polynomial.map_mul, map_cyclotomic]
  rw [hmap] at hirr
  have hdeg1 : (cyclotomic (n * p) ℚ).natDegree = (n * p).totient := natDegree_cyclotomic _ _
  have hdeg2 : (cyclotomic n ℚ).natDegree = n.totient := natDegree_cyclotomic _ _
  have hpos1 : 0 < (n * p).totient := Nat.totient_pos.mpr (Nat.mul_pos hn hp.out.pos)
  have hpos2 : 0 < n.totient := Nat.totient_pos.mpr hn
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  · exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)

/-- **Problem 1 of Kaur–Kumar–Remete has an empty answer for cyclotomic polynomials.**  For
`f = Φ n` and any prime `p` such that `f(X ^ p)` is irreducible, `p` does not divide the
index of `f(X ^ p)`.

The paper asks for one family of `f` for which the set of primes in Problem 1 can be
determined; for cyclotomic `f` it is empty, and the reason is a dichotomy.  If `p ∤ n` then
`Φ n (X ^ p) = Φ (n p) * Φ n` is reducible, so `p` is excluded by the irreducibility
requirement — and these are exactly the primes that
`RingOfIntegers.isIndexDivisor_expand_of_dvd_X_pow_sub_one` shows *do* divide the index.  If
`p ∣ n` then `Φ n (X ^ p) = Φ (n p)`, whose root generates a cyclotomic field, and cyclotomic
fields are monogenic, so no prime at all divides the index.

The two cases together are what makes the problem tractable here and hard in general: where
the index divisors are computable the power compositional polynomial falls apart, and where
it stays irreducible the ring of integers is already known. -/
theorem not_isIndexDivisor_expand_cyclotomic {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible (ratMap (expand ℤ p (cyclotomic n ℤ)))) :
    ¬ IsIndexDivisor p (expand ℤ p (cyclotomic n ℤ)) := by
  rw [cyclotomic_expand_eq_cyclotomic hp.out (dvd_of_irreducible_expand_cyclotomic hn hirr) ℤ]
  exact forall_not_isIndexDivisor_cyclotomic (Nat.mul_pos hn hp.out.pos) p hp.out

/-- The same statement in terms of rings of integers: whenever `Φ n (X ^ p)` is irreducible,
a root of it generates the full ring of integers. -/
theorem adjoin_eq_top_expand_cyclotomic {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible (ratMap (expand ℤ p (cyclotomic n ℤ))))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmω : minpoly ℤ ω = expand ℤ p (cyclotomic n ℤ)) :
    Algebra.adjoin ℤ {ω} = ⊤ := by
  rw [← forall_not_isIndexDivisor_iff_adjoin_eq_top hω, hmω,
    cyclotomic_expand_eq_cyclotomic hp.out (dvd_of_irreducible_expand_cyclotomic hn hirr) ℤ]
  exact forall_not_isIndexDivisor_cyclotomic (Nat.mul_pos hn hp.out.pos)

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
