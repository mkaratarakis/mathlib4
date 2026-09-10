/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.NormEuclidean.Norm
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Heilbronn's criterion

A number field `K` is *norm-Euclidean* when the division algorithm holds in `𝓞 K` with respect to
the absolute value of the norm: for all `α β ∈ 𝓞 K` with `β ≠ 0` there are `γ ρ ∈ 𝓞 K` with
`α = γ β + ρ` and `|N ρ| < |N β|`.  There is no separate definition of this notion here; it is
carried as a hypothesis, spelled out in full.

Heilbronn's criterion (`NumberField.not_normEuclidean_of_totallyRamified`) says that if a rational
prime `p` is totally ramified in `K`, say `𝔭 ^ n = (p)` with `n = [K : ℚ]`, and if `p` can be
written as `a + b` with `a`, `b` positive, `a` an `n`-th power residue modulo `p`, and neither `a`
nor `-b` a norm from `𝓞 K`, then `K` is not norm-Euclidean.

The proof given here is purely ideal-theoretic.  The classical argument compares `ρ` with its
conjugates, which only makes sense after passing to a Galois closure; instead we use
`Algebra.dvd_norm_sub_pow_finrank`, which says that modulo a totally ramified prime the norm form
is the `n`-th power map on the residue field.

## Main results

* `NumberField.exists_span_singleton_of_normEuclidean`: in a norm-Euclidean number field every
  nonzero ideal is principal.
* `NumberField.natAbs_norm_eq_of_pow_eq_span`: a generator of a totally ramified prime has norm
  `± p`.
* `NumberField.not_normEuclidean_of_totallyRamified`: **Heilbronn's criterion**.

## References

Heilbronn's criterion is due to [Heilbronn, *On Euclid's algorithm in cubic self-conjugate
fields*][heilbronn1950] and [Heilbronn, *On Euclid's algorithm in cyclic
fields*][heilbronn1951]; see [Lemmermeyer, *The Euclidean algorithm in algebraic number
fields*][lemmermeyer1995] for a survey of norm-Euclidean fields.  The form proved here, and its
use, follow [Hibbler, McGown, Treviño, *Polynomial densities and Heilbronn's
criterion*][hibbler_mcgown_trevino2025].
-/

public section

open NumberField Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- In a number field in which the division algorithm holds with respect to the absolute value of
the norm, every nonzero ideal is principal.  (This is the usual proof that a Euclidean domain is
a principal ideal domain, run for a single ideal.) -/
theorem exists_span_singleton_of_normEuclidean
    (hE : ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ∃ π ∈ I, I = Ideal.span {π} := by
  classical
  have hne : ∃ k : ℕ, ∃ β ∈ I, β ≠ 0 ∧ (Algebra.norm ℤ β).natAbs = k := by
    obtain ⟨β, hβI, hβ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨_, β, hβI, hβ0, rfl⟩
  obtain ⟨π, hπI, hπ0, hπk⟩ := Nat.find_spec hne
  refine ⟨π, hπI, le_antisymm (fun α hα => ?_) ((Ideal.span_le).2 (by simpa using hπI))⟩
  obtain ⟨γ, ρ, hρ, hlt⟩ := hE α π hπ0
  have hρI : ρ ∈ I := by
    have : ρ = α - γ * π := by rw [hρ]; ring
    rw [this]
    exact Ideal.sub_mem _ hα (Ideal.mul_mem_left _ _ hπI)
  have hρ0 : ρ = 0 := by
    by_contra h
    exact Nat.find_min hne (hπk ▸ hlt) ⟨ρ, hρI, h, rfl⟩
  rw [hρ, hρ0, add_zero]
  exact Ideal.mem_span_singleton.2 ⟨γ, mul_comm _ _⟩

/-- If `𝔭 ^ n = (p)` with `n = [K : ℚ]`, then any generator of `𝔭` has norm `± p`. -/
theorem natAbs_norm_eq_of_pow_eq_span {p : ℕ} {π : 𝓞 K}
    (h : (Ideal.span {π}) ^ (finrank ℚ K) = Ideal.span {(p : 𝓞 K)}) :
    (Algebra.norm ℤ π).natAbs = p := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hnorm : (Algebra.norm ℤ π) ^ (finrank ℚ K) * Algebra.norm ℤ (u : 𝓞 K) =
      (p : ℤ) ^ finrank ℤ (𝓞 K) := by
    rw [← Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ), ← map_pow, ← map_mul, hu]
    congr 1
    simp
  have hu1 : (Algebra.norm ℤ (u : 𝓞 K)).natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.1 (u.isUnit.map (Algebra.norm ℤ))
  have : ((Algebra.norm ℤ π).natAbs) ^ (finrank ℚ K) = p ^ (finrank ℚ K) := by
    have := congrArg Int.natAbs hnorm
    rwa [Int.natAbs_mul, Int.natAbs_pow, hu1, mul_one, Int.natAbs_pow, Int.natAbs_natCast,
      RingOfIntegers.rank] at this
  exact Nat.pow_left_injective finrank_pos.ne' this

/-- **Heilbronn's criterion.**  Let `K` be a number field of degree `n` in which the rational
prime `p` is totally ramified, say `𝔭 ^ n = (p)`.  Suppose `p = a + b` with `a`, `b` positive,
that `a` is an `n`-th power residue modulo `p`, and that neither `a` nor `-b` is the norm of an
algebraic integer of `K`.  Then `K` is not norm-Euclidean. -/
theorem not_normEuclidean_of_totallyRamified {p : ℕ} (hp : p.Prime)
    {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ^ (finrank ℚ K) = Ideal.span {(p : 𝓞 K)})
    {a b x : ℤ} (ha : 0 < a) (hb : 0 < b) (hab : (p : ℤ) = a + b)
    (hx : (p : ℤ) ∣ x ^ (finrank ℚ K) - a)
    (hna : ∀ α : 𝓞 K, Algebra.norm ℤ α ≠ a) (hnb : ∀ α : 𝓞 K, Algebra.norm ℤ α ≠ -b) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  intro hE
  classical
  set n := finrank ℚ K with hn
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- `𝔭` is not the zero ideal
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    intro h
    have hbot : Ideal.span {(p : 𝓞 K)} = ⊥ := by
      rw [← h𝔭, h, ← Ideal.zero_eq_bot, zero_pow finrank_pos.ne']
    have : ((p : 𝓞 K)) = 0 := Ideal.span_singleton_eq_bot.1 hbot
    exact hp.ne_zero (by exact_mod_cast this)
  -- so it is generated by some `π`, whose norm is `± p`
  obtain ⟨π, hπ𝔭, hπ⟩ := exists_span_singleton_of_normEuclidean hE h𝔭0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact h𝔭0 (by simpa using hπ)
  have hnormπ : (Algebra.norm ℤ π).natAbs = p := natAbs_norm_eq_of_pow_eq_span (hπ ▸ h𝔭)
  -- divide `x` by `π`
  obtain ⟨γ, ρ, hρ, hlt⟩ := hE ((x : 𝓞 K)) π hπ0
  have hmem : ρ - algebraMap ℤ (𝓞 K) x ∈ 𝔭 := by
    have : ρ - algebraMap ℤ (𝓞 K) x = -(γ * π) := by
      have : (algebraMap ℤ (𝓞 K) x) = (x : 𝓞 K) := by simp
      rw [this, hρ]; ring
    rw [this, hπ]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self π))
  -- the norm of `ρ` is congruent to `x ^ n`, hence to `a`, modulo `p`
  have hred : IsReduced (ℤ ⧸ Ideal.span {(p : ℤ)}) := by
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    have := Ideal.Quotient.isDomain (Ideal.span {(p : ℤ)})
    infer_instance
  have hdvd : (p : ℤ) ∣ Algebra.norm ℤ ρ - x ^ finrank ℤ (𝓞 K) := by
    refine Algebra.dvd_norm_sub_pow_finrank ℤ (𝓞 K) hred (I := 𝔭) ?_ hmem
    rw [RingOfIntegers.rank, ← hn, h𝔭]
    simp
  rw [RingOfIntegers.rank, ← hn] at hdvd
  have hcong : (p : ℤ) ∣ Algebra.norm ℤ ρ - a := by
    have := dvd_add hdvd hx
    simpa using this
  -- and `|N ρ| < p`, which pins it down to `a` or `-b`
  have hsmall : (Algebra.norm ℤ ρ).natAbs < p := by rw [← hnormπ]; exact hlt
  obtain ⟨k, hk⟩ := hcong
  have h1 : |Algebra.norm ℤ ρ| < (p : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hsmall
  have h2 : -(p : ℤ) < Algebra.norm ℤ ρ := neg_lt_of_abs_lt h1
  have h3 : Algebra.norm ℤ ρ < (p : ℤ) := lt_of_abs_lt h1
  have hka : k < 1 := by nlinarith [hk, ha.le]
  have hkb : -2 < k := by nlinarith [hk, hab]
  interval_cases k
  · exact hnb ρ (by omega)
  · exact hna ρ (by omega)

end NumberField
