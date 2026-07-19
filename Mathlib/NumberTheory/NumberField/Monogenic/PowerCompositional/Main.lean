/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Expand
public import Mathlib.NumberTheory.NumberField.Monogenic.Witness

/-!
# Monogenity of power compositional polynomials

This file proves Theorem 1.1 and Corollary 1.4 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*, Finite Fields Appl. **107** (2025), 102642:
for `k ≥ 2` with `f(X ^ k)` irreducible, the polynomial `f(X ^ k)` is monogenic if and only if

1. `f` is monogenic,
2. `p` does not divide the index of `f(X ^ p)` for every prime `p ∣ k`, and
3. `f(0)` is squarefree.

The three conditions are stated through `Polynomial.IsIndexDivisor`, which by Uchida's
criterion (`RingOfIntegers.dvd_exponent_iff_isIndexDivisor`) says exactly that a prime
divides the index of a root of the given polynomial.  Phrasing them this way keeps the
statement free of the auxiliary number fields in which those roots live: only the root of
`f(X ^ k)` itself, about which the conclusion speaks, appears as an algebraic integer.

## Main results

* `Polynomial.irreducible_ratMap_expand_of_dvd`: irreducibility of `f(X ^ k)` over `ℚ`
  descends to `f(X ^ t)` for every divisor `t` of `k`.

* `RingOfIntegers.isIndexDivisor_expand_iff_of_dvd` and
  `RingOfIntegers.isIndexDivisor_expand_iff_of_not_dvd`: the prime-by-prime form of
  Theorem 1.1, splitting on whether `p` divides `k`.  For `p ∤ k` this is Proposition 2.10;
  for `p ∣ k` it combines Proposition 2.10 with Corollary 2.5, which contracts the exact
  power `p ^ u` of `p` in `k` down to `p`.

* `RingOfIntegers.adjoin_eq_top_expand_iff`: **Theorem 1.1**.

* `RingOfIntegers.dvd_coeff_zero_of_isIndexDivisor_expand`: **Corollary 1.4** --- under
  conditions (1) and (2), every prime dividing the index of `f(X ^ k)` divides `f(0)`.

## Implementation notes

The conditions of Theorem 1.1 are conditions on infinitely many primes, and for a prime
`p ∣ k` condition (2) refers to a root of `f(X ^ p)` in a further number field.  Rather than
quantifying over number fields — which cannot be done uniformly in a single universe — the
statement uses `Polynomial.IsIndexDivisor`, and roots are produced only inside the proofs,
by the `AdjoinRoot` witness of `Monogenic/Witness.lean`.  This is where irreducibility is
consumed: `Polynomial.irreducible_ratMap_expand_of_dvd` supplies it for every `f(X ^ t)`
with `t ∣ k`, which is exactly the set of polynomials the proof needs roots of.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
* [K. Uchida, *When is `ℤ[θ]` the ring of integers?*][Uchida1977]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField NumberField.KaurKumar

namespace Polynomial

/-- Irreducibility over `ℚ` descends along `X ↦ X ^ t`: if `f(X ^ k)` is irreducible and
`t ∣ k`, then `f(X ^ t)` is irreducible.

A factorisation of `f(X ^ t)` would give one of `f(X ^ k) = (f(X ^ t))(X ^ (k / t))`. -/
theorem irreducible_ratMap_expand_of_dvd {f : ℤ[X]} {k t : ℕ} (hk0 : 0 < k) (ht : t ∣ k)
    (hirr : Irreducible (ratMap (expand ℤ k f))) :
    Irreducible (ratMap (expand ℤ t f)) := by
  obtain ⟨s, hs⟩ := ht
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; omega
  refine Polynomial.of_irreducible_expand (R := ℚ) hs0 ?_
  have heq : expand ℚ s (ratMap (expand ℤ t f)) = ratMap (expand ℤ k f) := by
    rw [hs]
    simp only [ratMap, Polynomial.map_expand, expand_expand]
    rw [mul_comm]
  rw [heq]
  exact hirr

end Polynomial

namespace RingOfIntegers

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Uchida's criterion at the canonical root -/

/-- Uchida's criterion for the root of a monic irreducible `g` in `ℚ[X] / (g)`. -/
theorem isIndexDivisor_iff_dvd_exponent_rootOfMonic {g : ℤ[X]} (hg : g.Monic)
    [Fact (Irreducible (ratMap g))] :
    IsIndexDivisor p g ↔ p ∣ exponent (rootOfMonic g hg) := by
  rw [dvd_exponent_iff_isIndexDivisor (adjoin_rootOfMonic g hg), minpoly_rootOfMonic]

/-! ### The results of Section 2, as statements about polynomials -/

/-- **Lemma 2.6**, as a statement about polynomials: an index divisor of `f` is an index
divisor of `f(X ^ ℓ)`. -/
theorem isIndexDivisor_expand_of_isIndexDivisor {f : ℤ[X]} (hfm : f.Monic) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hf : Irreducible (ratMap f)) (hfl : Irreducible (ratMap (expand ℤ ℓ f)))
    (h : IsIndexDivisor p f) : IsIndexDivisor p (expand ℤ ℓ f) := by
  haveI : Fact (Irreducible (ratMap f)) := ⟨hf⟩
  haveI : Fact (Irreducible (ratMap (expand ℤ ℓ f))) := ⟨hfl⟩
  rw [isIndexDivisor_iff_dvd_exponent_rootOfMonic (hfm.expand hℓ)]
  exact dvd_exponent_expand_of_dvd_exponent hℓ (adjoin_rootOfMonic f hfm)
    (minpoly_rootOfMonic f hfm) (minpoly_rootOfMonic _ (hfm.expand hℓ))
    ((isIndexDivisor_iff_dvd_exponent_rootOfMonic hfm).mp h)

/-- **Corollary 2.5**, as a statement about polynomials: the index divisor `p` cannot
distinguish `f(X ^ p)` from `f(X ^ (p ^ u))`. -/
theorem isIndexDivisor_expand_pow_iff {f : ℤ[X]} (hfm : f.Monic) {u : ℕ} (hu : 0 < u)
    (h1 : Irreducible (ratMap (expand ℤ p f))) (h2 : Irreducible (ratMap (expand ℤ (p ^ u) f))) :
    IsIndexDivisor p (expand ℤ p f) ↔ IsIndexDivisor p (expand ℤ (p ^ u) f) := by
  haveI : Fact (Irreducible (ratMap (expand ℤ p f))) := ⟨h1⟩
  haveI : Fact (Irreducible (ratMap (expand ℤ (p ^ u) f))) := ⟨h2⟩
  rw [isIndexDivisor_iff_dvd_exponent_rootOfMonic (hfm.expand hp.out.pos),
    isIndexDivisor_iff_dvd_exponent_rootOfMonic (hfm.expand (pow_pos hp.out.pos u))]
  exact dvd_exponent_expand_pow_iff hu (adjoin_rootOfMonic _ (hfm.expand hp.out.pos))
    (adjoin_rootOfMonic _ (hfm.expand (pow_pos hp.out.pos u)))
    (minpoly_rootOfMonic _ (hfm.expand hp.out.pos))
    (minpoly_rootOfMonic _ (hfm.expand (pow_pos hp.out.pos u)))

/-- **Proposition 2.3**, as a statement about polynomials: if `p ^ 2 ∣ f(0)` and `ℓ ≥ 2`,
then `p` is an index divisor of `f(X ^ ℓ)`. -/
theorem isIndexDivisor_expand_of_sq_dvd_coeff_zero {f : ℤ[X]} (hfm : f.Monic) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hfl : Irreducible (ratMap (expand ℤ ℓ f)))
    (hp2 : (p : ℤ) ^ 2 ∣ f.coeff 0) : IsIndexDivisor p (expand ℤ ℓ f) := by
  haveI : Fact (Irreducible (ratMap (expand ℤ ℓ f))) := ⟨hfl⟩
  rw [isIndexDivisor_iff_dvd_exponent_rootOfMonic (hfm.expand (by omega))]
  exact dvd_exponent_of_sq_dvd_coeff_zero hfm hℓ hp2 (minpoly_rootOfMonic _ (hfm.expand (by omega)))

/-- **Proposition 2.10**, as a statement about polynomials. -/
theorem isIndexDivisor_expand_iff {f : ℤ[X]} (hfm : f.Monic) {ℓ : ℕ} (hℓ2 : 2 ≤ ℓ)
    (hℓ : ¬ p ∣ ℓ) (hf : Irreducible (ratMap f)) (hfl : Irreducible (ratMap (expand ℤ ℓ f))) :
    IsIndexDivisor p (expand ℤ ℓ f) ↔ IsIndexDivisor p f ∨ (p : ℤ) ^ 2 ∣ f.coeff 0 := by
  haveI : Fact (Irreducible (ratMap f)) := ⟨hf⟩
  haveI : Fact (Irreducible (ratMap (expand ℤ ℓ f))) := ⟨hfl⟩
  rw [isIndexDivisor_iff_dvd_exponent_rootOfMonic (hfm.expand (by omega)),
    isIndexDivisor_iff_dvd_exponent_rootOfMonic hfm]
  exact dvd_exponent_expand_iff hℓ2 hℓ (adjoin_rootOfMonic f hfm)
    (adjoin_rootOfMonic _ (hfm.expand (by omega))) (minpoly_rootOfMonic f hfm)
    (minpoly_rootOfMonic _ (hfm.expand (by omega)))

/-! ### Theorem 1.1, prime by prime -/

/-- The prime-by-prime form of Theorem 1.1 at a prime **not** dividing `k`: this is
Proposition 2.10 applied to `ℓ = k`. -/
theorem isIndexDivisor_expand_iff_of_not_dvd {f : ℤ[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k f))) (hpk : ¬ p ∣ k) :
    IsIndexDivisor p (expand ℤ k f) ↔ IsIndexDivisor p f ∨ (p : ℤ) ^ 2 ∣ f.coeff 0 := by
  have hf : Irreducible (ratMap f) := by
    have h := irreducible_ratMap_expand_of_dvd (f := f) (k := k) (t := 1) (by omega)
      (one_dvd k) hirr
    rwa [expand_one] at h
  exact isIndexDivisor_expand_iff hfm hk hpk hf hirr

/-- The prime-by-prime form of Theorem 1.1 at a prime dividing `k`.

Writing `k = p ^ u * m` with `p ∤ m`, Corollary 2.5 contracts `p ^ u` to `p` and
Proposition 2.10 strips off `m`. -/
theorem isIndexDivisor_expand_iff_of_dvd {f : ℤ[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k f))) (hpk : p ∣ k) :
    IsIndexDivisor p (expand ℤ k f) ↔
      IsIndexDivisor p (expand ℤ p f) ∨ (p : ℤ) ^ 2 ∣ f.coeff 0 := by
  have hk0 : 0 < k := by omega
  obtain ⟨u, m, hm, hkeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := k) (by omega) p hp.out.ne_one
  have hppos : 0 < p := hp.out.pos
  have hu : 0 < u := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · rw [pow_zero, one_mul] at hkeq; exact absurd (hkeq ▸ hpk) hm
    · exact h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [mul_zero] at hkeq; omega
    · exact h
  -- the polynomial `f(X ^ (p ^ u))`, whose index divisors are those of `f(X ^ p)`
  have hpu : p ^ u ∣ k := ⟨m, hkeq⟩
  have hirrp : Irreducible (ratMap (expand ℤ p f)) :=
    irreducible_ratMap_expand_of_dvd hk0 hpk hirr
  have hirrpu : Irreducible (ratMap (expand ℤ (p ^ u) f)) :=
    irreducible_ratMap_expand_of_dvd hk0 hpu hirr
  have hcontract : IsIndexDivisor p (expand ℤ (p ^ u) f) ↔ IsIndexDivisor p (expand ℤ p f) :=
    (isIndexDivisor_expand_pow_iff hfm hu hirrp hirrpu).symm
  rcases eq_or_lt_of_le (show 1 ≤ m from hm0) with hm1 | hm2
  · -- `k = p ^ u`
    have hkpu : k = p ^ u := by rw [hkeq, ← hm1, mul_one]
    subst hkpu
    refine ⟨fun h => Or.inl (hcontract.mp h), ?_⟩
    rintro (h | h)
    · exact hcontract.mpr h
    · exact isIndexDivisor_expand_of_sq_dvd_coeff_zero hfm hk hirr h
  · -- `k = p ^ u * m` with `m ≥ 2`: strip `m` by Proposition 2.10
    have hexp : expand ℤ m (expand ℤ (p ^ u) f) = expand ℤ k f := by
      rw [expand_expand, hkeq, mul_comm]
    have hcoeff : (expand ℤ (p ^ u) f).coeff 0 = f.coeff 0 := by
      rw [coeff_expand (pow_pos hppos u), if_pos (dvd_zero _), Nat.zero_div]
    have hirrm : Irreducible (ratMap (expand ℤ m (expand ℤ (p ^ u) f))) := by rw [hexp]; exact hirr
    have h210 := isIndexDivisor_expand_iff (f := expand ℤ (p ^ u) f)
      (hfm.expand (pow_pos hppos u)) hm2 hm hirrpu hirrm
    rw [hexp, hcoeff] at h210
    rw [h210, hcontract]

/-! ### Theorem 1.1 and Corollary 1.4 -/

/-- **Theorem 1.1** of Kaur–Kumar–Remete.  Let `f : ℤ[X]` be monic, let `k ≥ 2` be such that
`f(X ^ k)` is irreducible, and let `ω` be a root of `f(X ^ k)` generating a number field
`L` over `ℚ`.  Then `ℤ[ω] = 𝓞 L` if and only if

1. no prime is an index divisor of `f`, that is, `f` is monogenic;
2. no prime `p ∣ k` is an index divisor of `f(X ^ p)`; and
3. `f(0)` is squarefree.

By `RingOfIntegers.dvd_exponent_iff_isIndexDivisor`, conditions (1) and (2) say exactly
that `f` is monogenic and that `p` does not divide the index of `f(X ^ p)`, which is how
the paper states them.

In particular the monogenity of `f(X ^ k)` depends on `k` only through its prime divisors:
the exponents in the factorisation of `k` do not appear. -/
theorem adjoin_eq_top_expand_iff {f : ℤ[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k f)))
    {L : Type*} [Field L] [NumberField L] {ω : 𝓞 L}
    (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤) (hmω : minpoly ℤ ω = expand ℤ k f) :
    Algebra.adjoin ℤ {ω} = ⊤ ↔
      (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q f) ∧
      (∀ q : ℕ, q.Prime → q ∣ k → ¬ IsIndexDivisor q (expand ℤ q f)) ∧
      Squarefree (f.coeff 0) := by
  have hf : Irreducible (ratMap f) := by
    have h := irreducible_ratMap_expand_of_dvd (f := f) (k := k) (t := 1) (by omega)
      (one_dvd k) hirr
    rwa [expand_one] at h
  -- Uchida's criterion turns the index into a property of `f(X ^ k)`.
  have key : ∀ q : ℕ, q.Prime → (q ∣ exponent ω ↔ IsIndexDivisor q (expand ℤ k f)) := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    rw [dvd_exponent_iff_isIndexDivisor hω, hmω]
  rw [adjoin_eq_top_iff_forall_prime_not_dvd_exponent]
  constructor
  · intro h
    refine ⟨fun q hq hIdx => ?_, fun q hq hqk hIdx => ?_, ?_⟩
    · haveI : Fact q.Prime := ⟨hq⟩
      exact h q hq ((key q hq).mpr
        (isIndexDivisor_expand_of_isIndexDivisor hfm (by omega) hf hirr hIdx))
    · haveI : Fact q.Prime := ⟨hq⟩
      exact h q hq ((key q hq).mpr
        ((isIndexDivisor_expand_iff_of_dvd hfm hk hirr hqk).mpr (Or.inl hIdx)))
    · refine Int.squarefree_iff_forall_prime_sq_not_dvd.mpr fun q hq hq2 => ?_
      haveI : Fact q.Prime := ⟨hq⟩
      exact h q hq ((key q hq).mpr (isIndexDivisor_expand_of_sq_dvd_coeff_zero hfm hk hirr hq2))
  · rintro ⟨h1, h2, h3⟩ q hq hdvd
    haveI : Fact q.Prime := ⟨hq⟩
    rw [key q hq] at hdvd
    by_cases hqk : q ∣ k
    · rcases (isIndexDivisor_expand_iff_of_dvd hfm hk hirr hqk).mp hdvd with hA | hB
      · exact h2 q hq hqk hA
      · exact Int.squarefree_iff_forall_prime_sq_not_dvd.mp h3 q hq hB
    · rcases (isIndexDivisor_expand_iff_of_not_dvd hfm hk hirr hqk).mp hdvd with hA | hB
      · exact h1 q hq hA
      · exact Int.squarefree_iff_forall_prime_sq_not_dvd.mp h3 q hq hB

/-- **Theorem 1.1** for the canonical root of `f(X ^ k)` in `ℚ[X] / (f(X ^ k))`.

This form carries no hypothetical algebraic integer, and shows in passing that the
hypotheses of `RingOfIntegers.adjoin_eq_top_expand_iff` are satisfiable: for every monic `f`
with `f(X ^ k)` irreducible there is a number field and a generator to which it applies. -/
theorem adjoin_eq_top_rootOfMonic_expand_iff {f : ℤ[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    [Fact (Irreducible (ratMap (expand ℤ k f)))] :
    Algebra.adjoin ℤ {rootOfMonic (expand ℤ k f) (hfm.expand (by omega))} = ⊤ ↔
      (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q f) ∧
      (∀ q : ℕ, q.Prime → q ∣ k → ¬ IsIndexDivisor q (expand ℤ q f)) ∧
      Squarefree (f.coeff 0) :=
  adjoin_eq_top_expand_iff hfm hk Fact.out (adjoin_rootOfMonic _ _) (minpoly_rootOfMonic _ _)

/-- **Corollary 1.4** of Kaur–Kumar–Remete.  If `f` is monogenic and no prime `p ∣ k` is an
index divisor of `f(X ^ p)`, then every prime dividing the index of `f(X ^ k)` divides
`f(0)`.

So under conditions (1) and (2) of Theorem 1.1 the index of `f(X ^ k)` is supported on the
prime divisors of `f(0)`; condition (3) is what rules the remaining primes out. -/
theorem dvd_coeff_zero_of_isIndexDivisor_expand {f : ℤ[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hirr : Irreducible (ratMap (expand ℤ k f)))
    (h1 : ∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q f)
    (h2 : ∀ q : ℕ, q.Prime → q ∣ k → ¬ IsIndexDivisor q (expand ℤ q f))
    (hIdx : IsIndexDivisor p (expand ℤ k f)) :
    (p : ℤ) ∣ f.coeff 0 := by
  have hsq : (p : ℤ) ^ 2 ∣ f.coeff 0 := by
    by_cases hpk : p ∣ k
    · exact ((isIndexDivisor_expand_iff_of_dvd hfm hk hirr hpk).mp hIdx).resolve_left
        (h2 p hp.out hpk)
    · exact ((isIndexDivisor_expand_iff_of_not_dvd hfm hk hirr hpk).mp hIdx).resolve_left
        (h1 p hp.out)
  exact dvd_trans (dvd_pow_self _ two_ne_zero) hsq

end RingOfIntegers
