/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Exponent
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Common index divisors and the Dedekind–Engstrom criterion

Let `K` be a number field.  For `θ : 𝓞 K` the *index* of `θ` is `[𝓞 K : ℤ[θ]]`
(`RingOfIntegers.index`), and the *index of the field* `i(K)` (`NumberField.fieldIndex`) is the
greatest common divisor of the indices of all `θ` with `K = ℚ(θ)`.  A prime `p` dividing `i(K)`
is a *common index divisor*: no generator of `K` gives an order that is maximal at `p`.

This file proves the criterion of Dedekind and Hensel (in the form popularised by Engstrom)
deciding which primes divide `i(K)` from the factorization of `p` in `𝓞 K` alone:

> `p ∣ i(K)` if and only if for some `f` the number of prime ideals above `p` of residue
> degree `f` exceeds the number of monic irreducible polynomials of degree `f` over `𝔽_p`.

In particular, whether `p` divides `i(K)` depends only on the residue degrees of the primes
above `p` (and not on the ramification indices or on any finer invariant).

## Main definitions

* `RingOfIntegers.index θ`: the index `[𝓞 K : ℤ[θ]]` (`0` if infinite).
* `NumberField.fieldIndex K`: the index `i(K)` of the number field `K`.

## Main results

* `RingOfIntegers.prime_dvd_index_iff_dvd_exponent`: for a generator `θ` of `K` and a prime `p`,
  `p ∣ [𝓞 K : ℤ[θ]]` if and only if `p` divides `RingOfIntegers.exponent θ`.
* `NumberField.dvd_fieldIndex_iff`: `d ∣ i(K)` if and only if `d` divides the index of every
  generator of `K`.
* `NumberField.ncard_primesOver_inertiaDeg_le`: if `p` does not divide the exponent of `θ`, there
  are at most as many primes above `p` of residue degree `f` as monic irreducible polynomials of
  degree `f` over `𝔽_p` (Dedekind, via the Kummer–Dedekind correspondence).
* `NumberField.exists_not_dvd_exponent`: conversely, if this inequality holds for every `f`, some
  generator `θ` of `K` has `p ∤ exponent θ` (Hensel's construction).
* `NumberField.prime_dvd_fieldIndex_iff`: the Dedekind–Engstrom criterion for `p ∣ i(K)`.
* `NumberField.prime_dvd_fieldIndex_iff_of_ncard_eq`: whether `p ∣ i(K)` depends only on the number
  of primes above `p` of each residue degree.
* `NumberField.lt_finrank_of_prime_dvd_fieldIndex`: Zylinski's bound, `p ∣ i(K) → p < [K : ℚ]`.

## References

* R. Dedekind, *Über den Zusammenhang zwischen der Theorie der Ideale und der Theorie der höheren
  Kongruenzen*, Abh. Kgl. Ges. Wiss. Göttingen **23** (1878), 1–23.
* H. T. Engstrom, *Prime ideal divisors of the discriminant of an algebraic number field*,
  Trans. Amer. Math. Soc. **32** (1930), 223–237.
* W. Narkiewicz, *Elementary and Analytic Theory of Algebraic Numbers*, 3rd ed., Springer, 2004.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal
open scoped IntermediateField

/-! ### Monic irreducible polynomials of a given degree -/

namespace Polynomial

/-- Over a finite ring there are finitely many polynomials of a given degree. -/
theorem finite_setOf_natDegree_eq (F : Type*) [CommRing F] [Finite F] (f : ℕ) :
    {g : F[X] | g.natDegree = f}.Finite := by
  refine Set.Finite.of_finite_image (f := fun (g : F[X]) (i : Fin (f + 1)) ↦ g.coeff i)
    (Set.toFinite _) ?_
  intro g₁ hg₁ g₂ hg₂ h
  ext n
  by_cases hn : n ≤ f
  · exact congr_fun h ⟨n, Nat.lt_succ_of_le hn⟩
  · push Not at hn
    rw [coeff_eq_zero_of_natDegree_lt (by rwa [show g₁.natDegree = f from hg₁]),
      coeff_eq_zero_of_natDegree_lt (by rwa [show g₂.natDegree = f from hg₂])]

/-- Over a finite ring there are finitely many monic irreducible polynomials of degree `f`. -/
theorem finite_setOf_monic_irreducible_natDegree_eq (F : Type*) [CommRing F] [Finite F] (f : ℕ) :
    {g : F[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}.Finite :=
  (finite_setOf_natDegree_eq F f).subset fun _ hg ↦ hg.2.2

/-- A geometric estimate: `p + (p + p ^ 2 + ⋯ + p ^ (f - 1)) ≤ p ^ f` for `p ≥ 2` and `f ≥ 1`. -/
theorem sum_Ico_pow_add_le_pow {p : ℕ} (hp : 2 ≤ p) {f : ℕ} (hf : 1 ≤ f) :
    ∑ d ∈ Finset.Ico 1 f, p ^ d + p ≤ p ^ f := by
  induction f, hf using Nat.le_induction with
  | base => simp
  | succ f hf ih =>
    rw [Finset.sum_Ico_succ_top hf, pow_succ]
    have : p ^ f + p ^ f ≤ p ^ f * p := by nlinarith [pow_pos (by omega : 0 < p) f]
    omega

/-- There are at least `p / f` monic irreducible polynomials of degree `f ≥ 1` over `𝔽_p`:
the field with `p ^ f` elements has at least `p` elements of degree exactly `f` over `𝔽_p`, and
each monic irreducible polynomial of degree `f` has at most `f` of them as roots. -/
theorem prime_le_mul_ncard_monic_irreducible (p : ℕ) [hp : Fact p.Prime] {f : ℕ} (hf : f ≠ 0) :
    p ≤ f * {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}.ncard := by
  classical
  set L := GaloisField p f
  letI := Fintype.ofFinite L
  have hcard : Fintype.card L = p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p f hf]
  have hfin : Module.finrank (ZMod p) L = f := GaloisField.finrank p hf
  have hint : ∀ x : L, IsIntegral (ZMod p) x := fun x ↦ .of_finite (ZMod p) x
  set D := Finset.univ.filter fun x : L ↦ (minpoly (ZMod p) x).natDegree = f
  -- elements of smaller degree `d` satisfy `x ^ p ^ d = x`
  have hDc : (Finset.univ.filter fun x : L ↦ ¬ (minpoly (ZMod p) x).natDegree = f) ⊆
      (Finset.Ico 1 f).biUnion fun d ↦ (X ^ p ^ d - X : L[X]).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    set d := (minpoly (ZMod p) x).natDegree
    have hd1 : 1 ≤ d := minpoly.natDegree_pos (hint x)
    have hdf : d < f := lt_of_le_of_ne (hfin ▸ minpoly.natDegree_le x) hx
    rw [Finset.mem_biUnion]
    refine ⟨d, Finset.mem_Ico.mpr ⟨hd1, hdf⟩, ?_⟩
    have hpd : 1 < p ^ d := Nat.one_lt_pow (by omega) hp.out.one_lt
    rw [Multiset.mem_toFinset, mem_roots (FiniteField.X_pow_card_sub_X_ne_zero L hpd), IsRoot.def,
      eval_sub, eval_pow, eval_X, sub_eq_zero]
    letI := Fintype.ofFinite (ZMod p)⟮x⟯
    have hK : Fintype.card (ZMod p)⟮x⟯ = p ^ d := by
      rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
        IntermediateField.adjoin.finrank (hint x)]
    have := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : (ZMod p)⟮x⟯)
    rw [hK] at this
    exact congr_arg Subtype.val this
  have hDc_card : (Finset.univ.filter fun x : L ↦ ¬ (minpoly (ZMod p) x).natDegree = f).card ≤
      ∑ d ∈ Finset.Ico 1 f, p ^ d := by
    refine (Finset.card_le_card hDc).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun d hd ↦ ?_))
    have hpd : 1 < p ^ d :=
      Nat.one_lt_pow (by have := (Finset.mem_Ico.mp hd).1; omega) hp.out.one_lt
    exact (Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (FiniteField.X_pow_card_sub_X_natDegree_eq L hpd).le)
  have hD : p ≤ D.card := by
    change p ≤ (Finset.univ.filter fun x : L ↦ (minpoly (ZMod p) x).natDegree = f).card
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : L ↦ (minpoly (ZMod p) x).natDegree = f)
    rw [Finset.card_univ, hcard] at h1
    have h2 := sum_Ico_pow_add_le_pow hp.out.two_le (Nat.one_le_iff_ne_zero.mpr hf)
    omega
  -- each monic irreducible polynomial of degree `f` has at most `f` roots
  have himg : D.card ≤ f * (D.image (minpoly (ZMod p))).card := by
    refine Finset.card_le_mul_card_image D f fun g hg ↦ ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    have hxf : (minpoly (ZMod p) x).natDegree = f := (Finset.mem_filter.mp hx).2
    calc (D.filter fun y ↦ minpoly (ZMod p) y = minpoly (ZMod p) x).card
        ≤ ((minpoly (ZMod p) x).aroots L).toFinset.card := by
          refine Finset.card_le_card fun y hy ↦ ?_
          rw [Finset.mem_filter] at hy
          rw [Multiset.mem_toFinset, mem_aroots, ← hy.2]
          exact ⟨(minpoly.monic (hint y)).ne_zero, minpoly.aeval _ _⟩
      _ ≤ f := by
          refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
          rw [natDegree_map, hxf]
  have hsub : (D.image (minpoly (ZMod p)) : Set (ZMod p)[X]) ⊆
      {g | g.Monic ∧ Irreducible g ∧ g.natDegree = f} := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨minpoly.monic (hint x), minpoly.irreducible (hint x), (Finset.mem_filter.mp hx).2⟩
  have := Set.ncard_le_ncard hsub (finite_setOf_monic_irreducible_natDegree_eq (ZMod p) f)
  rw [Set.ncard_coe_finset] at this
  calc p ≤ D.card := hD
    _ ≤ f * (D.image _).card := himg
    _ ≤ _ := Nat.mul_le_mul_left f this

end Polynomial

/-! ### The index of an algebraic integer -/

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The index `[𝓞 K : ℤ[θ]]` of the order `ℤ[θ]` in `𝓞 K`, as the index of an additive subgroup.
It is `0` when the index is infinite, that is when `θ` does not generate `K` over `ℚ`. -/
def index (θ : 𝓞 K) : ℕ :=
  (Subalgebra.toSubmodule (Algebra.adjoin ℤ {θ})).toAddSubgroup.index

variable {θ : 𝓞 K}

omit [NumberField K] in
/-- The exponent of `θ` lies in the conductor of `θ`. -/
theorem natCast_exponent_mem_conductor : (exponent θ : 𝓞 K) ∈ conductor ℤ θ := by
  have h : ((exponent θ : ℕ) : ℤ) ∈ (conductor ℤ θ).under ℤ := by
    rw [← Int.ideal_span_absNorm_eq_self ((conductor ℤ θ).under ℤ)]
    exact Ideal.subset_span rfl
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at h
  exact h

omit [NumberField K] in
/-- Every positive integer in the conductor of `θ` is a multiple of the exponent of `θ`. -/
theorem exponent_dvd_of_natCast_mem_conductor {d : ℕ} (hd : (d : 𝓞 K) ∈ conductor ℤ θ) :
    exponent θ ∣ d := by
  have h : ((d : ℕ) : ℤ) ∈ (conductor ℤ θ).under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hd
  rw [← Int.ideal_span_absNorm_eq_self ((conductor ℤ θ).under ℤ),
    Ideal.mem_span_singleton] at h
  exact Int.natCast_dvd_natCast.mp h

/-- For a generator `θ` of `K` and a prime `p`, `p` divides the index `[𝓞 K : ℤ[θ]]` if and only
if `p` divides the exponent of `θ`. -/
theorem prime_dvd_index_iff_dvd_exponent (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) {p : ℕ}
    [hp : Fact p.Prime] : p ∣ index θ ↔ p ∣ exponent θ := by
  set H := (Subalgebra.toSubmodule (Algebra.adjoin ℤ {θ})).toAddSubgroup
  constructor
  · intro hdvd
    by_contra hne
    -- the quotient `𝓞 K ⧸ ℤ[θ]` is finite since it is killed by `exponent θ ≠ 0`
    have he0 : exponent θ ≠ 0 := exponent_ne_zero hθ
    have hle : (Ideal.span {(exponent θ : 𝓞 K)}).toAddSubgroup ≤ H := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [mul_comm]
      exact (mem_conductor_iff.mp natCast_exponent_mem_conductor) y
    have hfin : H.index ≠ 0 := by
      refine fun h0 ↦ ?_
      have h1 := AddSubgroup.index_dvd_of_le hle
      rw [h0, zero_dvd_iff] at h1
      have h2 : Ideal.absNorm (Ideal.span {(exponent θ : 𝓞 K)}) ≠ 0 := by
        rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)),
          Algebra.norm_algebraMap]
        simp [he0]
      exact h2 (by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact h1)
    have : Finite (𝓞 K ⧸ H) := Nat.finite_of_card_ne_zero hfin
    obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hpx : (p : 𝓞 K) * x ∈ Algebra.adjoin ℤ {θ} := by
      have := addOrderOf_nsmul_eq_zero (x : 𝓞 K ⧸ H)
      rw [hq, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, nsmul_eq_mul] at this
      exact this
    have hex : (exponent θ : 𝓞 K) * x ∈ Algebra.adjoin ℤ {θ} :=
      (mem_conductor_iff.mp natCast_exponent_mem_conductor) x
    have hcop : IsCoprime (p : ℤ) (exponent θ : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr <| by
        rw [Int.gcd_natCast_natCast]
        exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hne
    obtain ⟨a, b, hab⟩ := hcop
    have hx : x ∈ Algebra.adjoin ℤ {θ} := by
      have : x = a • ((p : 𝓞 K) * x) + b • ((exponent θ : 𝓞 K) * x) := by
        rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul]
        exact_mod_cast (by rw [hab, Int.cast_one, one_mul] : x = ((a * p + b * exponent θ : ℤ) :
          𝓞 K) * x)
      rw [this]
      exact add_mem (Subalgebra.smul_mem _ hpx a) (Subalgebra.smul_mem _ hex b)
    have h0 : ((x : 𝓞 K) : 𝓞 K ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff x).mpr hx
    rw [h0, addOrderOf_zero] at hq
    exact hp.out.one_lt.ne hq
  · intro hdvd
    by_contra hne
    have hN : (index θ : 𝓞 K) ∈ conductor ℤ θ := by
      refine mem_conductor_iff.mpr fun b ↦ ?_
      have := AddSubgroup.nsmul_index_mem H b
      rwa [nsmul_eq_mul] at this
    exact hne (hdvd.trans (exponent_dvd_of_natCast_mem_conductor hN))

end RingOfIntegers

/-! ### The index of a number field -/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The index `i(K)` of the number field `K`: the greatest common divisor of the indices
`[𝓞 K : ℤ[θ]]` over all `θ : 𝓞 K` with `K = ℚ(θ)`.  It is defined as the nonnegative generator of
the ideal of `ℤ` spanned by these indices; `NumberField.dvd_fieldIndex_iff` is its universal
property. -/
def fieldIndex : ℕ :=
  (Submodule.IsPrincipal.generator (Ideal.span
    {n : ℤ | ∃ θ : 𝓞 K, Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧ n = RingOfIntegers.index θ})).natAbs

/-- `d` divides the index `i(K)` if and only if it divides the index of every generator of `K`. -/
theorem dvd_fieldIndex_iff (d : ℕ) :
    d ∣ fieldIndex K ↔
      ∀ θ : 𝓞 K, Algebra.adjoin ℚ {(θ : K)} = ⊤ → d ∣ RingOfIntegers.index θ := by
  set I := Ideal.span
    {n : ℤ | ∃ θ : 𝓞 K, Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧ n = RingOfIntegers.index θ}
  rw [fieldIndex, ← Int.natCast_dvd, ← Ideal.span_singleton_le_span_singleton,
    Ideal.span_singleton_generator, Ideal.span_le]
  constructor
  · intro h θ hθ
    have := h ⟨θ, hθ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at this
    exact Int.natCast_dvd_natCast.mp this
  · rintro h _ ⟨θ, hθ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact Int.natCast_dvd_natCast.mpr (h θ hθ)

/-- A prime `p` divides `i(K)` if and only if it divides the exponent of every generator. -/
theorem prime_dvd_fieldIndex_iff_forall_dvd_exponent (p : ℕ) [Fact p.Prime] :
    p ∣ fieldIndex K ↔
      ∀ θ : 𝓞 K, Algebra.adjoin ℚ {(θ : K)} = ⊤ → p ∣ RingOfIntegers.exponent θ := by
  rw [dvd_fieldIndex_iff]
  exact forall₂_congr fun θ hθ ↦ RingOfIntegers.prime_dvd_index_iff_dvd_exponent hθ

variable {K}

/-! ### Dedekind's direction: a `p`-maximal order bounds the number of primes of each degree -/

/-- **Dedekind.** If `p` does not divide the exponent of `θ`, then for every `f` there are at most
as many prime ideals above `p` of residue degree `f` as monic irreducible polynomials of degree
`f` over `𝔽_p`: the Kummer–Dedekind correspondence sends distinct primes to distinct monic
irreducible factors of the minimal polynomial of `θ` modulo `p`, preserving degrees. -/
theorem ncard_primesOver_inertiaDeg_le {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (f : ℕ) :
    {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard ≤
      {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}.ncard := by
  classical
  set e := Ideal.primesOverSpanEquivMonicFactorsMod hp
  let F : Ideal (𝓞 K) → (ZMod p)[X] := fun P ↦
    if h : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) then (e ⟨P, h⟩ : (ZMod p)[X]) else 0
  refine Set.ncard_le_ncard_of_injOn F ?_ ?_
    (finite_setOf_monic_irreducible_natDegree_eq (ZMod p) f)
  · rintro P ⟨hP, rfl⟩
    have hQ := (e ⟨P, hP⟩).prop
    simp only [F, dif_pos hP]
    replace hQ := Multiset.mem_toFinset.mp hQ
    have hne : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
      ((minpoly.monic θ.isIntegral).map _).ne_zero
    refine ⟨?_, UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hQ, ?_⟩
    · rw [← UniqueFactorizationMonoid.normalize_normalized_factor _ hQ]
      exact Polynomial.monic_normalize
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hQ).ne_zero
    · have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp (e ⟨P, hP⟩).prop
      rw [Subtype.coe_eta, Equiv.symm_apply_apply] at this
      exact this.symm
  · intro P hP Q hQ h
    simp only [F, dif_pos hP.1, dif_pos hQ.1] at h
    exact congr_arg Subtype.val (e.injective (Subtype.ext h))

/-! ### Hensel's direction: constructing a `p`-maximal generator -/

section Hensel

variable {p : ℕ} [hp : Fact p.Prime]

/-- Reducing an integer polynomial modulo `p` commutes with evaluation followed by a ring
homomorphism into an `𝔽_p`-algebra. -/
theorem ringHom_aeval_eq_aeval_map_intCast {R S : Type*} [CommRing R] [CommRing S]
    [Algebra (ZMod p) S] (φ : R →+* S) (x : R) (H : ℤ[X]) :
    φ (aeval x H) = aeval (φ x) (H.map (Int.castRingHom (ZMod p))) := by
  rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  exact Subsingleton.elim _ _

/-- An integer polynomial that vanishes modulo `p` takes values in `p R`. -/
theorem aeval_mem_span_of_map_eq_zero {R : Type*} [CommRing R] (x : R) {Z : ℤ[X]}
    (hZ : Z.map (Int.castRingHom (ZMod p)) = 0) : aeval x Z ∈ Ideal.span {(p : R)} := by
  obtain ⟨W, rfl⟩ : C (p : ℤ) ∣ Z := (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ by
    have := congr_arg (coeff · i) hZ
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  rw [map_mul, aeval_C, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- In a Dedekind domain, an element of `P \ P ^ 2` has `m`-th power outside `P ^ (m + 1)`. -/
theorem pow_notMem_pow_succ {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
    [P.IsPrime] (hP : P ≠ ⊥) {x : R} (hx : x ∈ P) (hx2 : x ∉ P ^ 2) (m : ℕ) :
    x ^ m ∉ P ^ (m + 1) := by
  intro h
  obtain ⟨J, hJ⟩ : P ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hJP : ¬ J ≤ P := by
    intro hJ'
    apply hx2
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
    exact Ideal.mul_mono_right hJ'
  apply hJP
  have h1 : P ^ (m + 1) ∣ Ideal.span {x} ^ m := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [hJ, mul_pow, pow_succ] at h1
  have hP' : P ^ m ≠ 0 := pow_ne_zero m (by simpa using hP)
  exact Ideal.IsPrime.le_of_pow_le (Ideal.dvd_iff_le.mp ((mul_dvd_mul_iff_left hP').mp h1))

/-- **The local computation.**  Let `P` be a nonzero prime of a Dedekind domain with `p ∈ P ^ e`,
and suppose that the residue of `θ` modulo `P` has minimal polynomial `σ` over `𝔽_p`, in the sense
that `H(θ) ∈ P ↔ σ ∣ H mod p`.  If some lift `G` of `σ` has `G(θ) ∈ P \ P ^ 2`, then for every
`m ≤ e`, `H(θ) ∈ P ^ m ↔ σ ^ m ∣ H mod p`. -/
theorem aeval_mem_pow_iff {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
    [P.IsPrime] (hP : P ≠ ⊥) {θ : R} {G : ℤ[X]} {σ : (ZMod p)[X]}
    (hGσ : G.map (Int.castRingHom (ZMod p)) = σ) (hG : aeval θ G ∈ P) (hG2 : aeval θ G ∉ P ^ 2)
    (hroot : ∀ H : ℤ[X], aeval θ H ∈ P ↔ σ ∣ H.map (Int.castRingHom (ZMod p)))
    {e : ℕ} (hpe : (p : R) ∈ P ^ e) :
    ∀ m ≤ e, ∀ H : ℤ[X], aeval θ H ∈ P ^ m ↔ σ ^ m ∣ H.map (Int.castRingHom (ZMod p)) := by
  have hspan : ∀ m ≤ e, Ideal.span {(p : R)} ≤ P ^ m := fun m hm ↦
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_le_pow_right hm hpe)
  have key : ∀ (m : ℕ) (H : ℤ[X]) (w : (ZMod p)[X]),
      H.map (Int.castRingHom (ZMod p)) = σ ^ m * w → ∃ W : ℤ[X],
        W.map (Int.castRingHom (ZMod p)) = w ∧
          aeval θ H - aeval θ G ^ m * aeval θ W ∈ Ideal.span {(p : R)} := by
    intro m H w hw
    obtain ⟨W, rfl⟩ := map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) w
    refine ⟨W, rfl, ?_⟩
    have := aeval_mem_span_of_map_eq_zero (p := p) θ (Z := H - G ^ m * W) (by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, hGσ, hw, sub_self])
    simpa [map_sub, map_mul, map_pow] using this
  intro m
  induction m with
  | zero => intro _ H; simp
  | succ m ih =>
    intro hm H
    constructor
    · intro hH
      obtain ⟨w, hw⟩ := (ih (by omega) H).mp (Ideal.pow_le_pow_right (Nat.le_succ m) hH)
      obtain ⟨W, hW, hmem⟩ := key m H w hw
      have h1 : aeval θ W * aeval θ G ^ m ∈ P ^ (m + 1) := by
        have := Ideal.sub_mem _ hH (hspan (m + 1) hm hmem)
        rw [sub_sub_cancel, mul_comm] at this
        exact this
      rcases Ideal.IsPrime.mul_mem_pow P h1 with h | h
      · rw [hw, pow_succ]
        exact mul_dvd_mul_left _ (hW ▸ (hroot W).mp h)
      · exact absurd h (pow_notMem_pow_succ hP hG hG2 m)
    · rintro ⟨w, hw⟩
      obtain ⟨W, -, hmem⟩ := key (m + 1) H w hw
      have := Ideal.add_mem _ (hspan (m + 1) hm hmem)
        (Ideal.mul_mem_right (aeval θ W) _ (Ideal.pow_mem_pow hG (m + 1)))
      rwa [sub_add_cancel] at this

/-- If `G(θ) ∈ P` for a lift `G` of a monic irreducible `σ ∈ 𝔽_p[X]`, then `σ` is the minimal
polynomial of `θ` modulo `P`: `H(θ) ∈ P ↔ σ ∣ H mod p`. -/
theorem aeval_mem_iff_dvd {R : Type*} [CommRing R] {P : Ideal R} [P.IsMaximal]
    (hpP : (p : R) ∈ P) {θ : R} {G : ℤ[X]} {σ : (ZMod p)[X]} (hσ : Irreducible σ)
    (hσm : σ.Monic) (hGσ : G.map (Int.castRingHom (ZMod p)) = σ) (hG : aeval θ G ∈ P)
    (H : ℤ[X]) : aeval θ H ∈ P ↔ σ ∣ H.map (Int.castRingHom (ZMod p)) := by
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (R ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hpP)
  letI := ZMod.algebra (R ⧸ P) p
  have hroot : aeval (Ideal.Quotient.mk P θ) σ = 0 := by
    rw [← hGσ, ← ringHom_aeval_eq_aeval_map_intCast (p := p), Ideal.Quotient.eq_zero_iff_mem]
    exact hG
  rw [← Ideal.Quotient.eq_zero_iff_mem, ringHom_aeval_eq_aeval_map_intCast (p := p),
    minpoly.eq_of_irreducible_of_monic hσ hroot hσm, minpoly.dvd_iff]

/-- The ring `𝔽_p[X] / (g)` has `p ^ deg g` elements for monic `g`. -/
theorem natCard_adjoinRoot {g : (ZMod p)[X]} (hg : g.Monic) :
    Nat.card (AdjoinRoot g) = p ^ g.natDegree := by
  rw [Nat.card_congr (AdjoinRoot.powerBasis' hg).basis.equivFun.toEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

variable {K : Type*} [Field K] [NumberField K]

omit hp in
theorem span_natCast_ne_bot_of_prime (hp' : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simp [hp'.ne_zero]

omit hp [NumberField K] in
/-- A prime of `𝓞 K` above `p` contains `p`. -/
theorem natCast_mem_of_mem_primesOver {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) : (p : 𝓞 K) ∈ P := by
  haveI : P.LiesOver (span {(p : ℤ)}) := hP.2
  have : (p : ℤ) ∈ P.under ℤ := by
    rw [← Ideal.over_def P (span {(p : ℤ)})]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at this
  exact this

/-- The residue field of a prime `P` above `p` has `p ^ f` elements, `f` its residue degree. -/
theorem natCard_quotient_of_mem_primesOver {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    Nat.card (𝓞 K ⧸ P) = p ^ P.inertiaDeg ℤ := by
  haveI : P.LiesOver (span {(p : ℤ)}) := hP.2
  haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
  haveI := Int.ideal_span_isMaximal_of_prime p
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp.out),
    Ideal.inertiaDeg'_eq_inertiaDeg, Int.natAbs_natCast]

/-- If `σ ∈ 𝔽_p[X]` is monic irreducible of degree the residue degree of a prime `P` above `p`,
then every lift `G` of `σ` has a simple root modulo `P`: some `a` has `G(a) ∈ P` and `G'(a) ∉ P`. -/
theorem exists_aeval_mem_derivative_notMem {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) {σ : (ZMod p)[X]} (hσ : Irreducible σ)
    (hσm : σ.Monic) (hdeg : σ.natDegree = P.inertiaDeg ℤ) {G : ℤ[X]}
    (hGσ : G.map (Int.castRingHom (ZMod p)) = σ) :
    ∃ a : 𝓞 K, aeval a G ∈ P ∧ aeval a (derivative G) ∉ P := by
  haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
  have hpP := natCast_mem_of_mem_primesOver hP
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (𝓞 K ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hpP)
  letI := ZMod.algebra (𝓞 K ⧸ P) p
  haveI : Fact (Irreducible σ) := ⟨hσ⟩
  -- a root of `σ` in the residue field, from the uniqueness of finite fields
  have hcard : Nat.card (AdjoinRoot σ) = Nat.card (𝓞 K ⧸ P) := by
    rw [natCard_adjoinRoot hσm, natCard_quotient_of_mem_primesOver hP, hdeg]
  have h1 : Finite (AdjoinRoot σ) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_adjoinRoot hσm]; exact pow_ne_zero _ hp.out.ne_zero)
  have h2 : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [natCard_quotient_of_mem_primesOver hP]; exact pow_ne_zero _ hp.out.ne_zero)
  letI := Fintype.ofFinite (AdjoinRoot σ)
  letI := Fintype.ofFinite (𝓞 K ⧸ P)
  let φ := FiniteField.algEquivOfCardEq p (K := AdjoinRoot σ) (K' := 𝓞 K ⧸ P)
    (by rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card])
  have hx : aeval (φ (AdjoinRoot.root σ)) σ = 0 := by
    rw [aeval_algEquiv, AlgHom.comp_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.root σ))
  refine ⟨a, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ringHom_aeval_eq_aeval_map_intCast (p := p), hGσ, ha,
      hx]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ringHom_aeval_eq_aeval_map_intCast (p := p),
      ← derivative_map, hGσ, ha]
    exact (PerfectField.separable_of_irreducible hσ).aeval_derivative_ne_zero hx

/-- **Hensel's choice of a local generator.**  If `σ ∈ 𝔽_p[X]` is monic irreducible of degree the
residue degree of a prime `P` above `p`, some lift `G` of `σ` has a value `G(b) ∈ P \ P ^ 2`. -/
theorem exists_aeval_mem_notMem_sq {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) {σ : (ZMod p)[X]} (hσ : Irreducible σ)
    (hσm : σ.Monic) (hdeg : σ.natDegree = P.inertiaDeg ℤ) :
    ∃ G : ℤ[X], G.map (Int.castRingHom (ZMod p)) = σ ∧
      ∃ b : 𝓞 K, aeval b G ∈ P ∧ aeval b G ∉ P ^ 2 := by
  haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (span_natCast_ne_bot_of_prime hp.out) hP
  obtain ⟨G, hGσ⟩ := map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) σ
  obtain ⟨a, hGa, hd⟩ := exists_aeval_mem_derivative_notMem hP hσ hσm hdeg hGσ
  refine ⟨G, hGσ, ?_⟩
  by_cases h2 : aeval a G ∈ P ^ 2
  · -- shift `a` by an element of `P \ P ^ 2`: Taylor expansion and separability of `σ`
    obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt
      (Ideal.pow_lt_self P hP0 (Ideal.IsMaximal.ne_top inferInstance) 2 le_rfl)
    obtain ⟨k, hk⟩ := binomExpansion (G.map (algebraMap ℤ (𝓞 K))) a π
    simp only [eval_map, ← aeval_def, derivative_map] at hk
    have hπP2 : k * π ^ 2 ∈ P ^ 2 := Ideal.mul_mem_left _ k (Ideal.pow_mem_pow hπ 2)
    refine ⟨a + π, ?_, fun hb ↦ ?_⟩
    · rw [hk]
      exact add_mem (add_mem hGa (Ideal.mul_mem_left _ _ hπ)) (Ideal.pow_le_self two_ne_zero hπP2)
    · have : aeval a (derivative G) * π ∈ P ^ 2 := by
        have := sub_mem (sub_mem hb h2) hπP2
        rw [hk] at this
        convert this using 1
        ring
      rcases Ideal.IsPrime.mul_mem_pow P this with h | h
      · exact hd h
      · exact hπ2 h
  · exact ⟨a, hGa, h2⟩

/-- If for every `f` there are at most as many primes above `p` of residue degree `f` as monic
irreducible polynomials of degree `f` over `𝔽_p`, we may attach to every prime `P` above `p` a
monic irreducible polynomial of degree the residue degree of `P`, injectively. -/
theorem exists_injOn_monic_irreducible
    (h : ∀ f : ℕ, {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard ≤
      {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}.ncard) :
    ∃ σ : Ideal (𝓞 K) → (ZMod p)[X],
      (∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
        (σ P).Monic ∧ Irreducible (σ P) ∧ (σ P).natDegree = P.inertiaDeg ℤ) ∧
      Set.InjOn σ (primesOver (span {(p : ℤ)}) (𝓞 K)) := by
  classical
  have hemb : ∀ f : ℕ, ∃ g : Ideal (𝓞 K) → (ZMod p)[X],
      Set.MapsTo g {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}
        {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f} ∧
      Set.InjOn g {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f} := by
    intro f
    set s := {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}
    set t := {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}
    have hs : s.Finite := (Set.toFinite _).subset (Set.sep_subset _ _)
    have ht : t.Finite := finite_setOf_monic_irreducible_natDegree_eq (ZMod p) f
    letI := hs.fintype
    letI := ht.fintype
    obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (α := s) (β := t) (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq]
      exact h f)
    refine ⟨fun P ↦ if hP : P ∈ s then (ι ⟨P, hP⟩ : (ZMod p)[X]) else 0, fun P hP ↦ ?_,
      fun P hP Q hQ hPQ ↦ ?_⟩
    · simp only [dif_pos hP]
      exact (ι ⟨P, hP⟩).2
    · simp only [dif_pos hP, dif_pos hQ] at hPQ
      exact congr_arg Subtype.val (ι.injective (Subtype.ext hPQ))
  choose g hmaps hinj using hemb
  refine ⟨fun P ↦ g (P.inertiaDeg ℤ) P, fun P hP ↦ hmaps _ ⟨hP, rfl⟩, fun P hP Q hQ hPQ ↦ ?_⟩
  have hPd : (g (P.inertiaDeg ℤ) P).natDegree = P.inertiaDeg ℤ := (hmaps _ ⟨hP, rfl⟩).2.2
  have hQd : (g (Q.inertiaDeg ℤ) Q).natDegree = Q.inertiaDeg ℤ := (hmaps _ ⟨hQ, rfl⟩).2.2
  have hPQ' : g (P.inertiaDeg ℤ) P = g (Q.inertiaDeg ℤ) Q := hPQ
  have hdeg : P.inertiaDeg ℤ = Q.inertiaDeg ℤ := by rw [← hPd, ← hQd, hPQ']
  rw [hdeg] at hPQ'
  exact hinj _ ⟨hP, hdeg⟩ ⟨hQ, rfl⟩ hPQ'

/-- **The Chinese remainder step.**  Given monic irreducible `σ P` of degree the residue degree of
each prime `P` above `p`, there is `θ ∈ 𝓞 K` such that for every `P` some lift `G` of `σ P` has
`G(θ) ∈ P \ P ^ 2`. -/
theorem exists_forall_aeval_mem_notMem_sq (σ : Ideal (𝓞 K) → (ZMod p)[X])
    (hσ : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
      (σ P).Monic ∧ Irreducible (σ P) ∧ (σ P).natDegree = P.inertiaDeg ℤ) :
    ∃ θ : 𝓞 K, ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), ∃ G : ℤ[X],
      G.map (Int.castRingHom (ZMod p)) = σ P ∧ aeval θ G ∈ P ∧ aeval θ G ∉ P ^ 2 := by
  have := fun P (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) ↦
    exists_aeval_mem_notMem_sq hP (hσ P hP).2.1 (hσ P hP).1 (hσ P hP).2.2
  choose G hG b hb hb2 using this
  have hpb := span_natCast_ne_bot_of_prime hp.out
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := (primesOver (span {(p : ℤ)}) (𝓞 K)).toFinset) id (fun _ ↦ 2)
    (fun P hP ↦ Ideal.prime_of_isPrime
      (Ideal.ne_bot_of_mem_primesOver hpb (Set.mem_toFinset.mp hP))
      (Set.mem_toFinset.mp hP).1)
    (fun _ _ _ _ h ↦ h) (fun P ↦ b P.1 (Set.mem_toFinset.mp P.2))
  refine ⟨θ, fun P hP ↦ ⟨G P hP, hG P hP, ?_⟩⟩
  have hsub : θ - b P hP ∈ P ^ 2 := hθ P (Set.mem_toFinset.mpr hP)
  have hd : aeval θ (G P hP) - aeval (b P hP) (G P hP) ∈ P ^ 2 := by
    obtain ⟨d, hd⟩ := sub_dvd_eval_sub θ (b P hP) ((G P hP).map (algebraMap ℤ (𝓞 K)))
    rw [eval_map, eval_map, ← aeval_def, ← aeval_def] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ hsub
  refine ⟨?_, fun h ↦ hb2 P hP ?_⟩
  · have := add_mem (Ideal.pow_le_self two_ne_zero hd) (hb P hP)
    rwa [sub_add_cancel] at this
  · have := sub_mem h hd
    rwa [sub_sub_cancel] at this

omit hp in
/-- An algebraic integer whose minimal polynomial has degree at least `[K : ℚ]` generates `K`. -/
theorem adjoin_eq_top_of_finrank_le_natDegree {θ : 𝓞 K}
    (h : Module.finrank ℚ K ≤ (minpoly ℤ θ).natDegree) : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
  have h1 : (minpoly ℚ (θ : K)).natDegree = Module.finrank ℚ K := by
    refine le_antisymm (minpoly.natDegree_le _) ?_
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe θ),
      (minpoly.monic (RingOfIntegers.isIntegral_coe θ)).natDegree_map]
    exact (RingOfIntegers.minpoly_coe θ).symm ▸ h
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic _),
    (Field.primitive_element_iff_minpoly_natDegree_eq ℚ (θ : K)).mpr h1,
    IntermediateField.top_toSubalgebra]

omit hp in
/-- A generator of `K` has minimal polynomial of degree `[K : ℚ]`. -/
theorem natDegree_minpoly_eq_finrank {θ : 𝓞 K} (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (minpoly ℤ θ).natDegree = Module.finrank ℚ K := by
  have h1 : ℚ⟮(θ : K)⟯ = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), hθ, IntermediateField.top_toSubalgebra]
  have h2 := (Field.primitive_element_iff_minpoly_natDegree_eq ℚ (θ : K)).mp h1
  rwa [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe θ),
    (minpoly.monic (RingOfIntegers.isIntegral_coe θ)).natDegree_map,
    RingOfIntegers.minpoly_coe] at h2

/-- **Hensel.**  If for every `f` there are at most as many primes above `p` of residue degree `f`
as monic irreducible polynomials of degree `f` over `𝔽_p`, then some generator `θ` of `K` has
`p ∤ exponent θ`, i.e. `ℤ[θ]` is maximal at `p`. -/
theorem exists_not_dvd_exponent
    (h : ∀ f : ℕ, {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard ≤
      {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}.ncard) :
    ∃ θ : 𝓞 K, Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧ ¬ p ∣ RingOfIntegers.exponent θ := by
  classical
  set S := primesOver (span {(p : ℤ)}) (𝓞 K)
  obtain ⟨σ, hσ, hinj⟩ := exists_injOn_monic_irreducible h
  obtain ⟨θ, hθ⟩ := exists_forall_aeval_mem_notMem_sq σ hσ
  choose G hGσ hG hG2 using hθ
  have hpb := span_natCast_ne_bot_of_prime hp.out
  haveI := Int.ideal_span_isMaximal_of_prime p
  set e : Ideal (𝓞 K) → ℕ := fun P ↦ P.ramificationIdx ℤ
  -- `p 𝓞 K = ∏ P ^ e P`
  have hfac : Ideal.span {(p : 𝓞 K)} = ∏ P ∈ S.toFinset, P ^ e P := by
    rw [← Ideal.map_algebraMap_eq_finsetProd_pow hpb, Ideal.map_span, Set.image_singleton,
      map_natCast]
  have hpe : ∀ P ∈ S, (p : 𝓞 K) ∈ P ^ e P := fun P hP ↦ by
    have : Ideal.span {(p : 𝓞 K)} ≤ P ^ e P := by
      rw [hfac]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Set.mem_toFinset.mpr hP))
    exact this (Ideal.mem_span_singleton_self _)
  -- the local computation at each prime above `p`
  have hloc : ∀ P (hP : P ∈ S) (H : ℤ[X]),
      aeval θ H ∈ P ^ e P ↔ σ P ^ e P ∣ H.map (Int.castRingHom (ZMod p)) := by
    intro P hP H
    haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
    exact aeval_mem_pow_iff (Ideal.ne_bot_of_mem_primesOver hpb hP) (hGσ P hP) (hG P hP)
      (hG2 P hP) (aeval_mem_iff_dvd (natCast_mem_of_mem_primesOver hP) (hσ P hP).2.1
        (hσ P hP).1 (hGσ P hP) (hG P hP)) (hpe P hP) _ le_rfl H
  -- pairwise coprimality, of the ideals and of the polynomials
  have hcop : (S.toFinset : Set (Ideal (𝓞 K))).Pairwise
      (Function.onFun IsCoprime fun P ↦ P ^ e P) := by
    intro P hP Q hQ hPQ
    rw [Set.coe_toFinset] at hP hQ
    haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
    haveI : Q.IsMaximal := Ideal.primesOver.isMaximal ⟨Q, hQ⟩
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance hPQ)).pow
  have hσcop : (S.toFinset : Set (Ideal (𝓞 K))).Pairwise
      (Function.onFun IsCoprime fun P ↦ σ P ^ e P) := by
    intro P hP Q hQ hPQ
    rw [Set.coe_toFinset] at hP hQ
    refine IsCoprime.pow ((Irreducible.coprime_iff_not_dvd (hσ P hP).2.1).mpr fun hdvd ↦
      hPQ (hinj hP hQ ?_))
    exact eq_of_monic_of_associated (hσ P hP).1 (hσ Q hQ).1
      ((hσ P hP).2.1.associated_of_dvd (hσ Q hQ).2.1 hdvd)
  set Fbig := ∏ P ∈ S.toFinset, σ P ^ e P
  have hFm : Fbig.Monic := monic_prod_of_monic _ _ fun P hP ↦
    ((hσ P (Set.mem_toFinset.mp hP)).1).pow _
  -- the global computation: `H(θ) ∈ p 𝓞 K ↔ ∏ σ P ^ e P ∣ H mod p`
  have hker : ∀ H : ℤ[X], aeval θ H ∈ Ideal.span {(p : 𝓞 K)} ↔
      Fbig ∣ H.map (Int.castRingHom (ZMod p)) := by
    intro H
    rw [hfac, Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
    simp only [Submodule.mem_iInf, Set.mem_toFinset]
    constructor
    · intro hH
      exact Finset.prod_dvd_of_coprime hσcop fun P hP ↦
        (hloc P (Set.mem_toFinset.mp hP) H).mp (hH P (Set.mem_toFinset.mp hP))
    · intro hd P hP
      exact (hloc P hP H).mpr ((Finset.dvd_prod_of_mem _ (Set.mem_toFinset.mpr hP)).trans hd)
  -- counting: `|𝓞 K / p| = p ^ deg Fbig = p ^ [K : ℚ]`
  have hdegF : Fbig.natDegree = ∑ P ∈ S.toFinset, e P * P.inertiaDeg ℤ := by
    rw [natDegree_prod_of_monic _ _ fun P hP ↦ ((hσ P (Set.mem_toFinset.mp hP)).1).pow _]
    refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [((hσ P (Set.mem_toFinset.mp hP)).1).natDegree_pow, (hσ P (Set.mem_toFinset.mp hP)).2.2]
  have hcardA : Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ Fbig.natDegree := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hfac, map_prod, hdegF,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun P hP ↦ ?_
    rw [map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      natCard_quotient_of_mem_primesOver (Set.mem_toFinset.mp hP), ← pow_mul, mul_comm]
  have hcardA' : Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
      ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hFn : Fbig.natDegree = Module.finrank ℚ K :=
    Nat.pow_right_injective hp.out.two_le (hcardA.symm.trans hcardA')
  -- the `𝔽_p`-algebra `𝓞 K / p` and the evaluation map `𝔽_p[X] → 𝓞 K / p` at `θ`
  set A := 𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}
  haveI hAfin : Finite A := Nat.finite_of_card_ne_zero (by
    rw [hcardA']; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcardA']
    exact Nat.one_lt_pow Module.finrank_pos.ne' hp.out.one_lt)
  haveI : CharP A p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _)
  letI := ZMod.algebra A p
  let φ : (ZMod p)[X] →+* A := (aeval (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) θ)).toRingHom
  have hφ : RingHom.ker φ = Ideal.span {Fbig} := by
    ext g
    obtain ⟨H, rfl⟩ := map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) g
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, ← hker H, ← Ideal.Quotient.eq_zero_iff_mem,
      ringHom_aeval_eq_aeval_map_intCast (p := p)]
    rfl
  have hsurj : Function.Surjective φ := by
    have hbij := (RingHom.kerLift_injective φ).bijective_of_nat_card_le (by
      rw [Nat.card_congr (Ideal.quotEquivOfEq hφ).toEquiv]
      change Nat.card A ≤ Nat.card (AdjoinRoot Fbig)
      rw [natCard_adjoinRoot hFm, hcardA])
    intro x
    obtain ⟨q, hq⟩ := hbij.2 x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨g, by rwa [RingHom.kerLift_mk] at hq⟩
  -- every element of `𝓞 K` is congruent modulo `p` to a polynomial in `θ`
  have hmod : ∀ x : 𝓞 K, ∃ H : ℤ[X], x - aeval θ H ∈ Ideal.span {(p : 𝓞 K)} := by
    intro x
    obtain ⟨g, hg⟩ := hsurj (Ideal.Quotient.mk _ x)
    obtain ⟨H, rfl⟩ := map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) g
    refine ⟨H, ?_⟩
    rw [← Ideal.Quotient.eq, ringHom_aeval_eq_aeval_map_intCast (p := p)]
    exact hg.symm
  -- `θ` generates `K`
  have hprim : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    have hdvd : Fbig ∣ (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) :=
      (hker _).mp (by rw [minpoly.aeval]; exact zero_mem _)
    have hle := natDegree_le_of_dvd hdvd ((minpoly.monic θ.isIntegral).map _).ne_zero
    rw [hFn, (minpoly.monic θ.isIntegral).natDegree_map] at hle
    exact adjoin_eq_top_of_finrank_le_natDegree hle
  -- `p` does not divide the exponent of `θ`
  refine ⟨θ, hprim, fun hdvd ↦ ?_⟩
  have he0 := RingOfIntegers.exponent_ne_zero hprim
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact he0 (by simpa using hm))
  have hmc : (m : 𝓞 K) ∈ conductor ℤ θ := by
    refine mem_conductor_iff.mpr fun x ↦ ?_
    obtain ⟨H, hH⟩ := hmod x
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hH
    have hx : (m : 𝓞 K) * x =
        m • aeval θ H + (RingOfIntegers.exponent θ : 𝓞 K) * y := by
      rw [nsmul_eq_mul, hm, Nat.cast_mul]
      linear_combination (-(m : 𝓞 K)) * hy
    rw [hx]
    exact add_mem (Subalgebra.nsmul_mem _ (aeval_mem_adjoin_singleton ℤ θ) m)
      ((mem_conductor_iff.mp RingOfIntegers.natCast_exponent_mem_conductor) y)
  have hle := Nat.le_of_dvd hm0 (RingOfIntegers.exponent_dvd_of_natCast_mem_conductor hmc)
  have := hp.out.two_le
  rw [hm] at hle
  nlinarith

end Hensel

/-! ### The Dedekind–Engstrom criterion -/

/-- **The Dedekind–Engstrom criterion** (Dedekind 1878, Hensel 1894, Engstrom 1930).  A prime `p`
divides the index `i(K)` of the number field `K` if and only if, for some `f`, the number of prime
ideals of `𝓞 K` above `p` with residue degree `f` exceeds the number of monic irreducible
polynomials of degree `f` over `𝔽_p`. -/
theorem prime_dvd_fieldIndex_iff (p : ℕ) [Fact p.Prime] :
    p ∣ fieldIndex K ↔ ∃ f : ℕ,
      {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = f}.ncard <
        {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard := by
  rw [prime_dvd_fieldIndex_iff_forall_dvd_exponent]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨θ, hθ, hnd⟩ := exists_not_dvd_exponent hne
    exact hnd (h θ hθ)
  · rintro ⟨f, hf⟩ θ -
    by_contra hnd
    exact (ncard_primesOver_inertiaDeg_le hnd f).not_gt hf

/-- **Problem 1, qualitative part.**  Whether a prime `p` divides `i(K)` depends only on the
residue degrees of the primes of `K` above `p`: two number fields in which `p` has, for every `f`,
the same number of primes of residue degree `f`, have the same answer.  (The ramification indices
play no role.) -/
theorem prime_dvd_fieldIndex_iff_of_ncard_eq {L : Type*} [Field L] [NumberField L] (p : ℕ)
    [Fact p.Prime]
    (h : ∀ f : ℕ, {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard =
      {P ∈ primesOver (span {(p : ℤ)}) (𝓞 L) | P.inertiaDeg ℤ = f}.ncard) :
    p ∣ fieldIndex K ↔ p ∣ fieldIndex L := by
  simp only [prime_dvd_fieldIndex_iff, h]

/-! ### Zylinski's bound -/

/-- The fundamental identity `∑_{P ∣ p} e_P f_P = [K : ℚ]`, summed over the finite set of primes
of `𝓞 K` above `p`. -/
theorem sum_ramificationIdx_mul_inertiaDeg (p : ℕ) [Fact p.Prime] :
    ∑ P ∈ (primesOver (span {(p : ℤ)}) (𝓞 K)).toFinset, P.ramificationIdx ℤ * P.inertiaDeg ℤ =
      Module.finrank ℚ K := by
  haveI := Int.ideal_span_isMaximal_of_prime p
  rw [Finset.sum_subtype _ (fun _ ↦ Set.mem_toFinset), Ideal.sum_ramification_inertia_eq_finrank,
    RingOfIntegers.rank]

/-- There are at most `[K : ℚ] / f` primes above `p` of residue degree `f`. -/
theorem ncard_primesOver_inertiaDeg_mul_le (p : ℕ) [Fact p.Prime] (f : ℕ) :
    {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard * f ≤
      Module.finrank ℚ K := by
  classical
  set S := primesOver (span {(p : ℤ)}) (𝓞 K)
  have hT : {P ∈ S | P.inertiaDeg ℤ = f} = ↑(S.toFinset.filter fun P ↦ P.inertiaDeg ℤ = f) := by
    ext P
    simp
  rw [hT, Set.ncard_coe_finset, ← sum_ramificationIdx_mul_inertiaDeg p, Finset.card_eq_sum_ones,
    Finset.sum_mul]
  refine le_trans ?_
    (Finset.sum_le_sum_of_subset (Finset.filter_subset (fun P ↦ P.inertiaDeg ℤ = f) _))
  refine Finset.sum_le_sum fun P hP ↦ ?_
  rw [Finset.mem_filter, Set.mem_toFinset] at hP
  haveI : P.IsPrime := hP.1.1
  rw [one_mul, ← hP.2]
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos (R := ℤ) P)

/-- **Zylinski's bound.**  A prime dividing the index `i(K)` is smaller than the degree:
if `p ∣ i(K)` then `p < [K : ℚ]`. -/
theorem lt_finrank_of_prime_dvd_fieldIndex (p : ℕ) [hp : Fact p.Prime] (h : p ∣ fieldIndex K) :
    p < Module.finrank ℚ K := by
  obtain ⟨f, hf⟩ := (prime_dvd_fieldIndex_iff p).mp h
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨P, hP, hP0⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
      {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = 0}.ncard ≠ 0)
    haveI : P.IsPrime := hP.1
    exact (Ideal.inertiaDeg_pos (R := ℤ) P).ne' hP0
  by_contra hle
  push Not at hle
  have h1 := ncard_primesOver_inertiaDeg_mul_le (K := K) p f
  have h2 := Polynomial.prime_le_mul_ncard_monic_irreducible p hf0
  refine absurd (Nat.le_of_mul_le_mul_right ?_ (Nat.pos_of_ne_zero hf0)) (not_le.mpr hf)
  calc _ ≤ Module.finrank ℚ K := h1
    _ ≤ p := hle
    _ ≤ _ := h2
    _ = _ := mul_comm _ _

/-- The index `i(K)` is never `0`: by Zylinski's bound it has no prime factor `≥ [K : ℚ]`. -/
theorem fieldIndex_ne_zero : fieldIndex K ≠ 0 := by
  intro h
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (Module.finrank ℚ K)
  haveI := Fact.mk hp
  exact (lt_finrank_of_prime_dvd_fieldIndex p (h ▸ dvd_zero p)).not_ge hpge

end NumberField
