/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.NormEuclidean.Counting
public import Mathlib.NumberTheory.NumberField.NormEuclidean.Dumas
public import Mathlib.NumberTheory.NumberField.NormEuclidean.DegreeOne
public import Mathlib.NumberTheory.NumberField.NormEuclidean.Heilbronn
public import Mathlib.NumberTheory.NumberField.NormEuclidean.Rootless
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Eisenstein–Dumas polynomials that fail to generate norm-Euclidean fields

This file combines the three arithmetic ingredients:

* `NumberField.EisensteinDumas.pow_eq_span`: an Eisenstein–Dumas polynomial at `p` of slope
  `m / n` forces `p` to be totally ramified;
* `NumberField.norm_ne_mul_of_forall_eval_ne_zero`: if the polynomial has no root modulo a prime
  `q`, then `u q` is never a norm when `q ∤ u`;
* `NumberField.not_normEuclidean_of_totallyRamified`: Heilbronn's criterion.

The bridge between them is the representation `p = u q₁ + v q₂` with `q₁ ∤ u` and `q₂ ∤ v`,
which exists as soon as `q₁ ^ 2 q₂ ^ 2 ≤ p` by the Chicken McNugget theorem
(`exists_eq_add_mul_of_sq_mul_sq_le`), together with the fact that every residue is an `n`-th
power modulo `p` when `gcd (p - 1) n = 1`.

## Main results

* `exists_eq_add_mul_of_sq_mul_sq_le`: the representation `p = u q₁ + v q₂`.
* `Nat.exists_pow_eq_of_coprime_sub_one`: every residue is an `n`-th power modulo `p`.
* `NumberField.not_normEuclidean_of_eisensteinDumas`: the arithmetic core — a number field of
  degree `n` containing a root of an Eisenstein–Dumas polynomial that has no root modulo two
  suitable primes is not norm-Euclidean.
## References

The density statements extend those of [Hibbler, McGown, Treviño, *Polynomial densities and
Heilbronn's criterion*][hibbler_mcgown_trevino2025] from the Eisenstein family to the
Eisenstein–Dumas family, and replace the two separate bounds proved there by a single theorem
indexed by the set of auxiliary primes.
-/

public section

open Finset Polynomial NumberField

/-- **Chicken McNugget for Heilbronn's criterion.**  If `q₁ ^ 2 q₂ ^ 2 ≤ p` for coprime
`q₁, q₂ > 1`, then `p = u q₁ + v q₂` for positive `u, v` with `q₁ ∤ u` and `q₂ ∤ v`. -/
theorem exists_eq_add_mul_of_sq_mul_sq_le {q₁ q₂ p : ℕ} (h₁ : 1 < q₁) (h₂ : 1 < q₂)
    (hcop : Nat.Coprime q₁ q₂) (hp : q₁ ^ 2 * q₂ ^ 2 ≤ p) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ p = u * q₁ + v * q₂ ∧ ¬ q₁ ∣ u ∧ ¬ q₂ ∣ v := by
  have hA : 4 ≤ q₁ ^ 2 := by nlinarith
  have hB : 4 ≤ q₂ ^ 2 := by nlinarith
  have hq₁A : q₁ < q₁ ^ 2 := by nlinarith
  have hq₂B : q₂ < q₂ ^ 2 := by nlinarith
  have hAB : q₁ ^ 2 + q₂ ^ 2 ≤ q₁ ^ 2 * q₂ ^ 2 :=
    Nat.add_le_mul (by nlinarith) (by nlinarith)
  have hfrob := frobeniusNumber_pair (Nat.Coprime.pow 2 2 hcop) (by nlinarith) (by nlinarith)
  rw [frobeniusNumber_iff] at hfrob
  have hgt : q₁ ^ 2 * q₂ ^ 2 - q₁ ^ 2 - q₂ ^ 2 < p - q₁ - q₂ := by omega
  obtain ⟨t₁, t₂, ht⟩ := (AddSubmonoid.mem_closure_pair _ _ _).1 (hfrob.2 _ hgt)
  simp only [smul_eq_mul] at ht
  have hle : q₁ + q₂ ≤ p := by omega
  have hS : t₁ * q₁ ^ 2 + t₂ * q₂ ^ 2 + q₁ + q₂ = p := by omega
  refine ⟨q₁ * t₁ + 1, q₂ * t₂ + 1, by omega, by omega, ?_, ?_, ?_⟩
  · calc p = t₁ * q₁ ^ 2 + t₂ * q₂ ^ 2 + q₁ + q₂ := hS.symm
      _ = (q₁ * t₁ + 1) * q₁ + (q₂ * t₂ + 1) * q₂ := by ring
  · exact fun h => absurd (Nat.dvd_one.1 ((Nat.dvd_add_right ⟨t₁, rfl⟩).1 h)) (by omega)
  · exact fun h => absurd (Nat.dvd_one.1 ((Nat.dvd_add_right ⟨t₂, rfl⟩).1 h)) (by omega)

/-- **Detecting `q₂ ∤ v` by a congruence modulo `q₂ ^ 2`.**  If `u q₁ ≡ p + q₁ q₂ (mod q₂ ^ 2)`
and `u q₁ < p`, then `p - u q₁` is `q₂` times a positive integer `v` not divisible by `q₂`.

This replaces the correction step of the classical argument, which shifts `u` by a multiple of
`q₂` and thereby destroys the property of `u q₁` of being an `n`-th power residue. -/
theorem exists_rep_of_congr {p q₁ q₂ u : ℕ} (hq₂ : 1 < q₂) (hq₁q₂ : ¬ (q₂ : ℤ) ∣ (q₁ : ℤ))
    (hlt : u * q₁ < p)
    (hcong : ((u * q₁ : ℕ) : ℤ) ≡ (p : ℤ) + (q₁ : ℤ) * q₂ [ZMOD ((q₂ : ℤ) ^ 2)]) :
    ∃ v : ℕ, 0 < v ∧ p = u * q₁ + v * q₂ ∧ ¬ q₂ ∣ v := by
  have hq₂0 : (0 : ℤ) < q₂ := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq₂.le
  -- `q₂ ^ 2` divides `p + q₁ q₂ - u q₁`
  obtain ⟨k, hk⟩ : ((q₂ : ℤ) ^ 2) ∣ ((p : ℤ) + (q₁ : ℤ) * q₂ - (u * q₁ : ℕ)) :=
    (Int.ModEq.dvd hcong)
  -- hence `p - u q₁ = q₂ * (q₂ k - q₁)`
  have hw : ((p : ℤ) - (u * q₁ : ℕ)) = (q₂ : ℤ) * ((q₂ : ℤ) * k - q₁) := by linarith [hk]
  have hwpos : (0 : ℤ) < (p : ℤ) - (u * q₁ : ℕ) := by
    have : ((u * q₁ : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hlt
    linarith
  have hvpos : (0 : ℤ) < (q₂ : ℤ) * k - q₁ := by
    by_contra hcon
    push Not at hcon
    nlinarith [hw, hwpos, hq₂0]
  -- the integer `v`
  obtain ⟨v, hv⟩ : ∃ v : ℕ, ((v : ℤ)) = (q₂ : ℤ) * k - q₁ := ⟨((q₂ : ℤ) * k - q₁).toNat, by
    rw [Int.toNat_of_nonneg hvpos.le]⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · exact_mod_cast hv ▸ hvpos
  · have : ((p : ℤ)) = ((u * q₁ : ℕ) : ℤ) + (v : ℤ) * q₂ := by rw [hv]; linarith [hw]
    exact_mod_cast this
  · intro hdvd
    obtain ⟨t, rfl⟩ := hdvd
    have : (q₂ : ℤ) ∣ (q₁ : ℤ) := by
      refine ⟨k - t, ?_⟩
      have h2 : ((q₂ * t : ℕ) : ℤ) = (q₂ : ℤ) * k - q₁ := hv
      push_cast at h2
      linarith
    exact hq₁q₂ this

/-- If `n` is coprime to `p - 1` then every residue modulo the prime `p` is an `n`-th power. -/
theorem Nat.exists_pow_eq_of_coprime_sub_one {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hcop : Nat.Coprime (p - 1) n) (y : ZMod p) : ∃ x : ZMod p, x ^ n = y := by
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp [zero_pow hn]⟩
  · have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
    obtain ⟨z, hz⟩ := (powCoprime (G := (ZMod p)ˣ) (n := n) (by rwa [hcard])).surjective
      (Units.mk0 y hy)
    refine ⟨(z : ZMod p), ?_⟩
    have := congrArg (Units.val) hz
    simpa using this

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The arithmetic core.**  Let `K` be a number field of degree `n` containing a root `θ` of a
monic integer polynomial `F` of degree `n` which satisfies the Eisenstein–Dumas condition at `p`
with slope `m / n`, where `gcd (p - 1) n = 1`.  If `F` has no root modulo two primes
`q₁, q₂` admitting a representation `p = u q₁ + v q₂` with `q₁ ∤ u` and `q₂ ∤ v` (for instance
because `q₁ ^ 2 q₂ ^ 2 ≤ p`, see `exists_eq_add_mul_of_sq_mul_sq_le`), then `K` is not
norm-Euclidean. -/
theorem not_normEuclidean_of_eisensteinDumas_of_isPow {θ : 𝓞 K} {n m p q₁ q₂ : ℕ} {a : ℕ → ℤ}
    {c : ℕ → ℕ} {u v : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hrep : 0 < u ∧ 0 < v ∧ p = u * q₁ + v * q₂ ∧ ¬ q₁ ∣ u ∧ ¬ q₂ ∣ v)
    (hres : ∃ x : ℤ, (p : ℤ) ∣ x ^ n - ((u * q₁ : ℕ) : ℤ)) (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
    (hc : ∀ i < n, m * (n - i) ≤ n * c i) (hdvd : ∀ i < n, (p : ℤ) ^ c i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hr₁ : ∀ r : ZMod q₁, eval₂ (Int.castRingHom (ZMod q₁)) r
      (X ^ n + ∑ i ∈ range n, C (a i) * X ^ i) ≠ 0)
    (hr₂ : ∀ r : ZMod q₂, eval₂ (Int.castRingHom (ZMod q₂)) r
      (X ^ n + ∑ i ∈ range n, C (a i) * X ^ i) ≠ 0) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  -- the polynomial evaluates to zero at `θ`
  have haeval : aeval θ (X ^ n + ∑ i ∈ range n, C (a i) * X ^ i) = 0 := by
    rw [map_add, map_pow, aeval_X, map_sum]
    simpa using hroot
  -- a maximal ideal above `p`
  have hspan : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = 1 := by rw [h]; simp
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hdeg] at h1
    have h2 : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
    omega
  obtain ⟨𝔭, h𝔭max, h𝔭le⟩ := Ideal.exists_le_maximal _ hspan
  have hmem : (p : 𝓞 K) ∈ 𝔭 := h𝔭le (Ideal.mem_span_singleton_self _)
  -- total ramification
  have hram : 𝔭 ^ n = Ideal.span {(p : 𝓞 K)} :=
    EisensteinDumas.pow_eq_span hp hn hm hmn hroot hc hdvd hnd h𝔭max hmem hdeg
  -- the representation `p = u q₁ + v q₂` and the power residue
  obtain ⟨hu0, hv0, hpuv, hqu, hqv⟩ := hrep
  obtain ⟨x, hxdvd⟩ := hres
  -- neither `u q₁` nor `-(v q₂)` is a norm
  have hna : ∀ α : 𝓞 K, Algebra.norm ℤ α ≠ (u * q₁ : ℕ) := by
    intro α
    have := norm_ne_mul_of_forall_eval_ne_zero hq₁ haeval hr₁
      (u := (u : ℤ)) (by exact_mod_cast fun h => hqu (Int.ofNat_dvd.1 h)) α
    push_cast
    exact_mod_cast this
  have hnb : ∀ α : 𝓞 K, Algebra.norm ℤ α ≠ -(v * q₂ : ℕ) := by
    intro α
    have := norm_ne_mul_of_forall_eval_ne_zero hq₂ haeval hr₂
      (u := (-v : ℤ)) (fun h => hqv (Int.ofNat_dvd.1 (dvd_neg.1 h))) α
    push_cast at this ⊢
    intro h
    exact this (by rw [h]; ring)
  -- Heilbronn's criterion
  refine not_normEuclidean_of_totallyRamified hp (by rw [← hdeg] at hram; exact hram)
    (a := (u * q₁ : ℕ)) (b := (v * q₂ : ℕ)) (x := x)
    (by exact_mod_cast Nat.mul_pos hu0 hq₁.pos) (by exact_mod_cast Nat.mul_pos hv0 hq₂.pos)
    (by exact_mod_cast hpuv) ?_ hna hnb
  rw [hdeg]
  exact hxdvd


/-- **The arithmetic core, Lemma 3.7.**  When `gcd (p - 1) n = 1` every residue modulo `p` is an
`n`-th power, so the power-residue hypothesis of
`not_normEuclidean_of_eisensteinDumas_of_isPow` is automatic. -/
theorem not_normEuclidean_of_eisensteinDumas {θ : 𝓞 K} {n m p q₁ q₂ : ℕ} {a : ℕ → ℤ} {c : ℕ → ℕ}
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hcop : Nat.Coprime (p - 1) n) (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
    (hc : ∀ i < n, m * (n - i) ≤ n * c i) (hdvd : ∀ i < n, (p : ℤ) ^ c i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hrep : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ p = u * q₁ + v * q₂ ∧ ¬ q₁ ∣ u ∧ ¬ q₂ ∣ v)
    (hr₁ : ∀ r : ZMod q₁, eval₂ (Int.castRingHom (ZMod q₁)) r
      (X ^ n + ∑ i ∈ range n, C (a i) * X ^ i) ≠ 0)
    (hr₂ : ∀ r : ZMod q₂, eval₂ (Int.castRingHom (ZMod q₂)) r
      (X ^ n + ∑ i ∈ range n, C (a i) * X ^ i) ≠ 0) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  obtain ⟨u, v, hu0, hv0, hpuv, hqu, hqv⟩ := hrep
  have hnez : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨x, hx⟩ := Nat.exists_pow_eq_of_coprime_sub_one hp hn.ne' hcop ((u * q₁ : ℕ) : ZMod p)
  refine not_normEuclidean_of_eisensteinDumas_of_isPow hp hn hm hmn ⟨hu0, hv0, hpuv, hqu, hqv⟩
    ⟨(x.val : ℤ), ?_⟩ hdeg hroot hc hdvd hnd hq₁ hq₂ hr₁ hr₂
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_eq_zero]
  exact_mod_cast hx

end NumberField

/-! ### Splitting the local conditions -/

namespace Int

open Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Chinese remainder theorem for tuples of residues.**  If the conditions at two coprime
moduli are imposed independently, the number of residues satisfying both is the product of the
two counts. -/
theorem card_filter_crt {M₁ M₂ : ι → ℕ} [∀ i, NeZero (M₁ i)] [∀ i, NeZero (M₂ i)]
    [∀ i, NeZero (M₁ i * M₂ i)] (hcop : ∀ i, Nat.Coprime (M₁ i) (M₂ i))
    (S₁ : Finset (∀ i, ZMod (M₁ i))) (S₂ : Finset (∀ i, ZMod (M₂ i))) :
    #{x ∈ (Finset.univ : Finset (∀ i, ZMod (M₁ i * M₂ i))) |
        (fun i => ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i)) ∈ S₁ ∧
        (fun i => ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i)) ∈ S₂}
      = #S₁ * #S₂ := by
  classical
  set e : (∀ i, ZMod (M₁ i * M₂ i)) ≃ ((∀ i, ZMod (M₁ i)) × (∀ i, ZMod (M₂ i))) :=
    (Equiv.piCongrRight fun i => (ZMod.chineseRemainder (hcop i)).toEquiv).trans
      (Equiv.arrowProdEquivProdArrow _ _ _) with he
  have hfst : ∀ (x : ∀ i, ZMod (M₁ i * M₂ i)) (i : ι),
      (e x).1 i = ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i) := by
    intro x i; simp [he, ZMod.chineseRemainder]
  have hsnd : ∀ (x : ∀ i, ZMod (M₁ i * M₂ i)) (i : ι),
      (e x).2 i = ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i) := by
    intro x i; simp [he, ZMod.chineseRemainder]
  have hmem : ∀ x : ∀ i, ZMod (M₁ i * M₂ i),
      ((fun i => ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i)) ∈ S₁ ∧
        (fun i => ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i)) ∈ S₂)
      ↔ e x ∈ S₁ ×ˢ S₂ := by
    intro x
    rw [Finset.mem_product]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa [funext fun i => hfst x i] using h1, by simpa [funext fun i => hsnd x i]
        using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa [funext fun i => hfst x i] using h1, by simpa [funext fun i => hsnd x i]
        using h2⟩
  rw [← Finset.card_product S₁ S₂]
  refine Finset.card_bij (fun x _ => e x) (fun x hx => (hmem x).1 (Finset.mem_filter.1 hx).2)
    (fun x₁ _ x₂ _ h => e.injective h) (fun y hy => ⟨e.symm y, ?_, by simp⟩)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmem _).2 (by simpa using hy)⟩

/-- **Relative density.**  The proportion, among the integer tuples in the box `|a i| ≤ X` whose
reduction lies in `T`, of those whose reduction lies in `S`, tends to `#S / #T`. -/
theorem tendsto_card_box_filter_ratio {M : ι → ℕ} (hM : ∀ i, 0 < M i)
    (S T : Finset (∀ i, ZMod (M i))) (hT : T.Nonempty) :
    Filter.Tendsto (fun X : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
            (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
            (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ T} : ℝ))
      Filter.atTop (nhds ((#S : ℝ) / #T)) := by
  have hprod : (0 : ℝ) < ∏ i, (M i : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast hM i
  have hTne : ((#T : ℝ) / ∏ i, (M i : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < #T := by exact_mod_cast Finset.card_pos.2 hT
    positivity
  have h := (tendsto_card_box_filter_div hM S).div (tendsto_card_box_filter_div hM T) hTne
  have hTpos : (0 : ℝ) < #T := by exact_mod_cast Finset.card_pos.2 hT
  have hval : ((#S : ℝ) / ∏ i, (M i : ℝ)) / ((#T : ℝ) / ∏ i, (M i : ℝ)) = (#S : ℝ) / #T := by
    field_simp
  rw [hval] at h
  refine h.congr fun X => ?_
  have hpos : (0 : ℝ) < (2 * (X : ℝ) + 1) ^ Fintype.card ι := by positivity
  simp only [Pi.div_apply]
  rcases eq_or_ne (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
      (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ T} : ℝ) 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

/-- **The auxiliary local conditions carry the whole density.**  Fix a condition `A` at a modulus
`M₁` (in the application: the Eisenstein–Dumas condition at `p`) and a condition `B` at a coprime
modulus `M₂` (in the application: having no root modulo the auxiliary primes).  Among the tuples
satisfying the first condition, the proportion of those satisfying the second tends to
`#B / ∏ i, M₂ i`: the density attached to the first condition cancels. -/
theorem tendsto_ratio_crt {M₁ M₂ : ι → ℕ} [∀ i, NeZero (M₁ i)] [∀ i, NeZero (M₂ i)]
    [∀ i, NeZero (M₁ i * M₂ i)] (hcop : ∀ i, Nat.Coprime (M₁ i) (M₂ i))
    (A : Finset (∀ i, ZMod (M₁ i))) (hA : A.Nonempty) (B : Finset (∀ i, ZMod (M₂ i))) :
    Filter.Tendsto (fun X : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
            (fun i => (((a i : ℤ) : ZMod (M₁ i * M₂ i)))) ∈
              {x ∈ (Finset.univ : Finset (∀ i, ZMod (M₁ i * M₂ i))) |
                (fun i => ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i)) ∈ A ∧
                (fun i => ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i)) ∈ B}} : ℝ)
        /
        (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
            (fun i => (((a i : ℤ) : ZMod (M₁ i * M₂ i)))) ∈
              {x ∈ (Finset.univ : Finset (∀ i, ZMod (M₁ i * M₂ i))) |
                (fun i => ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i)) ∈ A ∧
                (fun i => ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i)) ∈
                  (Finset.univ : Finset (∀ i, ZMod (M₂ i)))}} : ℝ))
      Filter.atTop (nhds ((#B : ℝ) / ∏ i, (M₂ i : ℝ))) := by
  classical
  set G : Finset (∀ i, ZMod (M₁ i * M₂ i)) :=
    {x ∈ (Finset.univ : Finset (∀ i, ZMod (M₁ i * M₂ i))) |
      (fun i => ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i)) ∈ A ∧
      (fun i => ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i)) ∈ B} with hG
  set D : Finset (∀ i, ZMod (M₁ i * M₂ i)) :=
    {x ∈ (Finset.univ : Finset (∀ i, ZMod (M₁ i * M₂ i))) |
      (fun i => ZMod.castHom (dvd_mul_right (M₁ i) (M₂ i)) (ZMod (M₁ i)) (x i)) ∈ A ∧
      (fun i => ZMod.castHom (dvd_mul_left (M₂ i) (M₁ i)) (ZMod (M₂ i)) (x i)) ∈
        (Finset.univ : Finset (∀ i, ZMod (M₂ i)))} with hD
  have hM : ∀ i, 0 < M₁ i * M₂ i := fun i => Nat.pos_of_ne_zero (NeZero.ne _)
  have hcardG : #G = #A * #B := card_filter_crt hcop A B
  have hcardD : #D = #A * ∏ i, M₂ i := by
    rw [hD, card_filter_crt hcop A (Finset.univ : Finset (∀ i, ZMod (M₂ i))), Finset.card_univ,
      Fintype.card_pi]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by simp
  have hApos : 0 < #A := Finset.card_pos.2 hA
  have hM₂pos : 0 < ∏ i, M₂ i := Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne _)
  have hne : D.Nonempty := by
    rw [← Finset.card_pos, hcardD]
    exact Nat.mul_pos hApos hM₂pos
  have h := tendsto_card_box_filter_ratio hM G D hne
  have hval : ((#G : ℝ) / #D) = (#B : ℝ) / ∏ i, (M₂ i : ℝ) := by
    rw [hcardG, hcardD, Nat.cast_mul, Nat.cast_mul, Nat.cast_prod]
    exact mul_div_mul_left _ _ (by exact_mod_cast hApos.ne')
  rw [← hval]
  exact h

end Int


/-! ### The density of Eisenstein–Dumas polynomials satisfying auxiliary local conditions -/

namespace Int

/-- An integer is divisible by `p ^ k` exactly when its residue modulo `p ^ k` vanishes. -/
theorem intCast_pow_eq_zero_iff (p k : ℕ) (a : ℤ) :
    ((a : ZMod (p ^ k)) = 0) ↔ (p : ℤ) ^ k ∣ a := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

end Int

/-- **The density of an auxiliary local condition inside an Eisenstein–Dumas family.**
Fix a prime `p`, exponents `c i`, and a modulus `R` coprime to `p`.  Among the integer tuples
`a` with `|a i| ≤ N` satisfying `p ^ c i ∣ a i` for all `i` and `p ^ (c 0 + 1) ∤ a 0` — the
Eisenstein–Dumas family attached to the exponents `c`, viewed through the coefficients of
`X ^ n + ∑ a i X ^ i` — the proportion of those whose tuple reduces into `B` modulo `R` tends to
`#B / R ^ n`.  The density attached to the condition at `p` cancels. -/
theorem tendsto_density_of_local_condition {n : ℕ} (hn : 0 < n) {p R : ℕ} {c : Fin n → ℕ}
    (hp : p.Prime) (hR : 0 < R) (hcop : Nat.Coprime p R) (B : Finset (Fin n → ZMod R)) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
            (fun i => ((a i : ℤ) : ZMod R)) ∈ B} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩} : ℝ))
      Filter.atTop (nhds ((#B : ℝ) / R ^ n)) := by
  classical
  have hp0 : 0 < p := hp.pos
  have i1 : ∀ i : Fin n, NeZero (p ^ (c i + 1)) := fun i => ⟨by positivity⟩
  have i2 : ∀ _ : Fin n, NeZero R := fun _ => ⟨hR.ne'⟩
  have i3 : ∀ i : Fin n, NeZero (p ^ (c i + 1) * R) := fun i => ⟨by positivity⟩
  have hcop' : ∀ i : Fin n, Nat.Coprime (p ^ (c i + 1)) R := fun i => Nat.Coprime.pow_left _ hcop
  -- the residue conditions at `p`, coordinate by coordinate
  set A : ∀ i : Fin n, Finset (ZMod (p ^ (c i + 1))) := fun i =>
    {y ∈ (Finset.univ : Finset (ZMod (p ^ (c i + 1)))) |
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ (c i))) (ZMod (p ^ c i)) y = 0 ∧
        (i = ⟨0, hn⟩ → y ≠ 0)} with hA
  have hmemA : ∀ (i : Fin n) (t : ℤ), ((t : ZMod (p ^ (c i + 1))) ∈ A i) ↔
      ((p : ℤ) ^ c i ∣ t ∧ (i = ⟨0, hn⟩ → ¬ (p : ℤ) ^ (c i + 1) ∣ t)) := by
    intro i t
    rw [hA]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_intCast, ne_eq,
      Int.intCast_pow_eq_zero_iff]
  -- the family is nonempty: `a i = p ^ c i` works at every coordinate
  have hAne : (Fintype.piFinset A).Nonempty := by
    refine ⟨fun i => (((p : ℤ) ^ c i : ℤ) : ZMod (p ^ (c i + 1))), ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [hmemA i]
    refine ⟨dvd_rfl, fun _ hdd => ?_⟩
    have hppos : (0 : ℤ) < (p : ℤ) ^ c i := by positivity
    have h1 : ((p : ℤ) ^ (c i + 1)) ≤ (p : ℤ) ^ c i := Int.le_of_dvd hppos hdd
    have h2 : ((p : ℤ) ^ c i) < (p : ℤ) ^ (c i + 1) := by
      have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
      calc (p : ℤ) ^ c i = (p : ℤ) ^ c i * 1 := by ring
        _ < (p : ℤ) ^ c i * p := by nlinarith
        _ = (p : ℤ) ^ (c i + 1) := by ring
    omega
  have key := @Int.tendsto_ratio_crt (Fin n) _ _ (fun i : Fin n => p ^ (c i + 1))
    (fun _ : Fin n => R) i1 i2 i3 hcop' (Fintype.piFinset A) hAne B
  -- the dictionary between the integer conditions and the residue conditions
  have hdict : ∀ (B' : Finset (∀ _ : Fin n, ZMod R)) (a : Fin n → ℤ),
      ((fun i => ((a i : ℤ) : ZMod (p ^ (c i + 1) * R))) ∈
        {x ∈ (Finset.univ : Finset (∀ i : Fin n, ZMod (p ^ (c i + 1) * R))) |
          (fun i => ZMod.castHom (dvd_mul_right (p ^ (c i + 1)) R) (ZMod (p ^ (c i + 1))) (x i)) ∈
            Fintype.piFinset A ∧
          (fun i => ZMod.castHom (dvd_mul_left R (p ^ (c i + 1))) (ZMod R) (x i)) ∈ B'})
      ↔ (((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
          (fun i => ((a i : ℤ) : ZMod R)) ∈ B') := by
    intro B' a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_intCast, Fintype.mem_piFinset,
      hmemA]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun i => (h1 i).1, (h1 ⟨0, hn⟩).2 rfl⟩, h2⟩
    · rintro ⟨⟨h1, h0⟩, h2⟩
      refine ⟨fun i => ⟨h1 i, fun hi => ?_⟩, h2⟩
      subst hi
      exact h0
  -- the same dictionary with no condition at `R`, which is the shape the denominator takes
  have hdictA : ∀ a : Fin n → ℤ,
      ((fun i => ((a i : ℤ) : ZMod (p ^ (c i + 1) * R))) ∈
        {x ∈ (Finset.univ : Finset (∀ i : Fin n, ZMod (p ^ (c i + 1) * R))) |
          (fun i => ZMod.castHom (dvd_mul_right (p ^ (c i + 1)) R) (ZMod (p ^ (c i + 1))) (x i)) ∈
            Fintype.piFinset A})
      ↔ ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) := by
    intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_intCast, Fintype.mem_piFinset,
      hmemA]
    constructor
    · intro h1
      exact ⟨fun i => (h1 i).1, (h1 ⟨0, hn⟩).2 rfl⟩
    · rintro ⟨h1, h0⟩
      refine fun i => ⟨h1 i, fun hi => ?_⟩
      subst hi
      exact h0
  -- rewrite the limit value and both counts
  have hval : ((#B : ℝ) / ∏ _i : Fin n, (R : ℝ)) = (#B : ℝ) / R ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hval]
  refine key.congr fun N => ?_
  simp only [hdict, hdictA, Finset.mem_univ, and_true]

/-! ### The main density theorem for a pair of auxiliary primes -/

namespace NumberField

open Polynomial

/-- The Eisenstein–Dumas hypotheses indexed by `Fin n`, as they arise when the polynomial is
presented through its coefficient tuple.  This is `not_normEuclidean_of_eisensteinDumas`
transported along `Fin.sum_univ_eq_sum_range`. -/
theorem not_normEuclidean_of_eisensteinDumas_fin {K : Type*} [Field K] [NumberField K]
    {θ : 𝓞 K} {n m p q₁ q₂ : ℕ} {a : Fin n → ℤ} {c : Fin n → ℕ} (hn : 0 < n)
    (hp : p.Prime) (hm : 0 < m) (hmn : Nat.Coprime m n) (hcop : Nat.Coprime (p - 1) n)
    (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i : Fin n, ((a i : ℤ) : 𝓞 K) * θ ^ (i : ℕ) = 0)
    (hc : ∀ i : Fin n, m * (n - (i : ℕ)) ≤ n * c i)
    (hdvd : ∀ i : Fin n, (p : ℤ) ^ c i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a ⟨0, hn⟩)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hrep : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ p = u * q₁ + v * q₂ ∧ ¬ q₁ ∣ u ∧ ¬ q₂ ∣ v)
    (hr₁ : ∀ r : ZMod q₁,
      ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₁)) * X ^ (i : ℕ)).IsRoot r)
    (hr₂ : ∀ r : ZMod q₂,
      ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₂)) * X ^ (i : ℕ)).IsRoot r) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  set a' : ℕ → ℤ := fun i => if h : i < n then a ⟨i, h⟩ else 0 with ha'
  set c' : ℕ → ℕ := fun i => if h : i < n then c ⟨i, h⟩ else 0 with hc'
  have ha'0 : a' 0 = a ⟨0, hn⟩ := by simp [ha', hn]
  -- the reduction of the polynomial, in the two indexings
  have hmap : ∀ q : ℕ, Polynomial.map (Int.castRingHom (ZMod q))
      (X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i)
      = X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ) := by
    intro q
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun i => Polynomial.map (Int.castRingHom (ZMod q)) (C (a' i) * X ^ i)) n]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    simp [ha', i.2]
  refine not_normEuclidean_of_eisensteinDumas (θ := θ) (a := a') (c := c')
    hp hn hm hmn hcop hdeg ?_ ?_ ?_ ?_ hq₁ hq₂ hrep ?_ ?_
  · rw [← hroot]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => ((a' i : ℤ) : 𝓞 K) * θ ^ i) n]
    exact Finset.sum_congr rfl fun i _ => by simp [ha', i.2]
  · intro i hi
    simpa [hc', hi] using hc ⟨i, hi⟩
  · intro i hi
    simpa [ha', hc', hi] using hdvd ⟨i, hi⟩
  · rwa [ha'0]
  · intro r
    rw [Polynomial.eval₂_eq_eval_map, hmap q₁]
    exact hr₁ r
  · intro r
    rw [Polynomial.eval₂_eq_eval_map, hmap q₂]
    exact hr₂ r

/-- **The density theorem for a pair of auxiliary primes.**  Among the Eisenstein–Dumas family
attached to `p` and the exponents `c`, the proportion of coefficient tuples whose polynomial has
no root modulo `q₁` and no root modulo `q₂` tends to `C_{q₁}(n) · C_{q₂}(n)`, where `C_q(n)` is
the proportion of monic polynomials of degree `n` over `ZMod q` with no root.  Combined with
`not_normEuclidean_of_eisensteinDumas_fin`, which shows that every tuple counted in the numerator
generates a field that is not norm-Euclidean, this is the master density theorem for a
two-element set of auxiliary primes. -/
theorem tendsto_density_pair {n : ℕ} (hn : 0 < n) {p q₁ q₂ : ℕ} {c : Fin n → ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)]
    (hp : p.Prime) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (hpq₁ : p ≠ q₁) (hpq₂ : p ≠ q₂) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
            ((∀ r : ZMod q₁,
                ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₁)) * X ^ (i : ℕ)).IsRoot r) ∧
              (∀ r : ZMod q₂,
                ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₂)) * X ^ (i : ℕ)).IsRoot r))} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩} : ℝ))
      Filter.atTop (nhds
        ((#{y : Fin n → ZMod q₁ |
              ∀ r : ZMod q₁, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q₁ : ℝ) ^ n *
          ((#{y : Fin n → ZMod q₂ |
              ∀ r : ZMod q₂, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q₂ : ℝ) ^ n))) := by
  classical
  have hR : 0 < q₁ * q₂ := Nat.mul_pos hq₁.pos hq₂.pos
  have hcop : Nat.Coprime p (q₁ * q₂) :=
    Nat.Coprime.mul_right ((Nat.coprime_primes hp hq₁).2 hpq₁) ((Nat.coprime_primes hp hq₂).2 hpq₂)
  set T₁ : Finset (Fin n → ZMod q₁) :=
    {y | ∀ r : ZMod q₁, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} with hT₁
  set T₂ : Finset (Fin n → ZMod q₂) :=
    {y | ∀ r : ZMod q₂, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} with hT₂
  set B : Finset (Fin n → ZMod (q₁ * q₂)) :=
    {x ∈ (Finset.univ : Finset (∀ _ : Fin n, ZMod (q₁ * q₂))) |
      (fun i => ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) (x i)) ∈ T₁ ∧
      (fun i => ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) (x i)) ∈ T₂} with hB
  have key := tendsto_density_of_local_condition (c := c) hn hp hR hcop B
  -- the cardinality of `B` factorises
  have hcardB : #B = #T₁ * #T₂ :=
    @Int.card_filter_crt (Fin n) _ _ (fun _ => q₁) (fun _ => q₂) (fun _ => inferInstance)
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => (Nat.coprime_primes hq₁ hq₂).2 hne) T₁ T₂
  -- the value of the limit
  have hval : ((#B : ℝ) / ((q₁ * q₂ : ℕ) : ℝ) ^ n)
      = (#T₁ : ℝ) / (q₁ : ℝ) ^ n * ((#T₂ : ℝ) / (q₂ : ℝ) ^ n) := by
    rw [hcardB]
    push_cast
    rw [mul_pow]
    field_simp
  -- the dictionary at the auxiliary primes
  have hdictB : ∀ a : Fin n → ℤ,
      ((fun i => ((a i : ℤ) : ZMod (q₁ * q₂))) ∈ B)
      ↔ ((∀ r : ZMod q₁,
            ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₁)) * X ^ (i : ℕ)).IsRoot r) ∧
          (∀ r : ZMod q₂,
            ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₂)) * X ^ (i : ℕ)).IsRoot r)) := by
    intro a
    rw [hB]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_intCast, hT₁, hT₂]
  rw [← hval]
  refine key.congr fun N => ?_
  simp only [hdictB]

/-- `C₂(n) = 1/4` for `n ≥ 2`. -/
theorem card_no_root_zmod_two_div {n : ℕ} (hn : 2 ≤ n) :
    (#{y : Fin n → ZMod 2 |
        ∀ r : ZMod 2, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      / ((2 : ℕ) : ℝ) ^ n = 1 / 4 := by
  have hcard : Fintype.card (ZMod 2) = 2 := by simp
  have h := Polynomial.card_no_root_univ_eq (F := ZMod 2) (n := n) (by rw [hcard]; exact hn)
  rw [hcard] at h
  have h' : (#{y : Fin n → ZMod 2 |
      ∀ r : ZMod 2, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      = (2 : ℝ) ^ (n - 2) := by
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h2
    simpa using h2
  have hn2 : ((2 : ℕ) : ℝ) ^ n = 2 ^ (n - 2) * 4 := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h', hn2]
  have hpos : (0 : ℝ) < 2 ^ (n - 2) := by positivity
  field_simp

/-- `C₃(n) = 8/27` for `n ≥ 3`. -/
theorem card_no_root_zmod_three_div {n : ℕ} (hn : 3 ≤ n) :
    (#{y : Fin n → ZMod 3 |
        ∀ r : ZMod 3, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      / ((3 : ℕ) : ℝ) ^ n = 8 / 27 := by
  have hcard : Fintype.card (ZMod 3) = 3 := by simp
  have h := Polynomial.card_no_root_univ_eq (F := ZMod 3) (n := n) (by rw [hcard]; exact hn)
  rw [hcard] at h
  have h' : (#{y : Fin n → ZMod 3 |
      ∀ r : ZMod 3, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      = 8 * (3 : ℝ) ^ (n - 3) := by
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h2
    rw [h2]
  have hn3 : ((3 : ℕ) : ℝ) ^ n = 3 ^ (n - 3) * 27 := by
    push_cast
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h', hn3]
  have hpos : (0 : ℝ) < 3 ^ (n - 3) := by positivity
  field_simp

/-- **The bound `2/27`.**  For `n ≥ 3` and a prime `p ∉ {2,3}`, the proportion of the
Eisenstein–Dumas family attached to `p` and `c` whose polynomial has no root modulo `2` and none
modulo `3` tends to `2/27`.  By `not_normEuclidean_of_eisensteinDumas_fin`, each of those
polynomials generates a field that is not norm-Euclidean, provided `p` can be written as
`2u + 3v` with `u` odd and `3 ∤ v` and `gcd (p-1, n) = 1`. -/
theorem tendsto_density_two_three {n : ℕ} (hn : 3 ≤ n) {p : ℕ} {c : Fin n → ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩) ∧
            ((∀ r : ZMod 2,
                ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod 2)) * X ^ (i : ℕ)).IsRoot r) ∧
              (∀ r : ZMod 3,
                ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod 3)) * X ^ (i : ℕ)).IsRoot r))} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩} : ℝ))
      Filter.atTop (nhds (2 / 27)) := by
  have h := tendsto_density_pair (n := n) (c := c) (by omega) hp Nat.prime_two Nat.prime_three
    (by norm_num) hp2 hp3
  have hv : (1 : ℝ) / 4 * (8 / 27) = 2 / 27 := by norm_num
  rw [card_no_root_zmod_two_div (by omega), card_no_root_zmod_three_div hn, hv] at h
  exact h

end NumberField

/-! ### The master density theorem for an arbitrary set of auxiliary primes -/

namespace Int

variable {n : ℕ} {Q : Finset ℕ}

/-- **Chinese remainder theorem for a family of coprime moduli.**  The number of tuples of
residues modulo `∏ q ∈ Q, q` reducing into a prescribed set modulo each `q` is the product of the
individual counts. -/
theorem card_filter_crt_pi (hcop : Pairwise (Function.onFun Nat.Coprime (fun q : Q => (q : ℕ))))
    [∀ q : Q, NeZero (q : ℕ)] [NeZero (∏ q : Q, (q : ℕ))]
    (S : ∀ q : Q, Finset (Fin n → ZMod (q : ℕ))) :
    #{x ∈ (Finset.univ : Finset (Fin n → ZMod (∏ q : Q, (q : ℕ)))) |
        ∀ q : Q, (fun i => ZMod.castHom (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
          (ZMod (q : ℕ)) (x i)) ∈ S q}
      = ∏ q : Q, #(S q) := by
  classical
  set e : (Fin n → ZMod (∏ q : Q, (q : ℕ))) ≃ (∀ q : Q, Fin n → ZMod (q : ℕ)) :=
    (Equiv.piCongrRight fun _ : Fin n => (ZMod.prodEquivPi _ hcop).toEquiv).trans
      (Equiv.piComm _) with he
  have hcomp : ∀ (x : Fin n → ZMod (∏ q : Q, (q : ℕ))) (q : Q) (i : Fin n),
      e x q i
        = ZMod.castHom (Finset.dvd_prod_of_mem _ (Finset.mem_univ q)) (ZMod (q : ℕ)) (x i) := by
    intro x q i
    exact ZMod.prodEquivPi_apply (fun q : Q => (q : ℕ)) hcop (x i) q
  have hiff : ∀ x : Fin n → ZMod (∏ q : Q, (q : ℕ)),
      (∀ q : Q, (fun i => ZMod.castHom (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
        (ZMod (q : ℕ)) (x i)) ∈ S q) ↔ e x ∈ Fintype.piFinset S := by
    intro x
    rw [Fintype.mem_piFinset]
    refine forall_congr' fun q => ?_
    rw [show e x q = (fun i => ZMod.castHom (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
      (ZMod (q : ℕ)) (x i)) from funext (hcomp x q)]
  rw [← Fintype.card_piFinset S]
  refine Finset.card_bij (fun x _ => e x)
    (fun x hx => (hiff x).1 (Finset.mem_filter.1 hx).2)
    (fun x₁ _ x₂ _ h => e.injective h)
    (fun y hy => ⟨e.symm y, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hiff _).2 ?_⟩,
      e.apply_symm_apply y⟩)
  rw [e.apply_symm_apply]
  exact hy



open scoped Classical in
/-- The tuples for which at least two of the conditions hold split into the classes on which the
set of conditions that hold is a fixed `U`. -/
theorem card_filter_atLeastTwo_eq_sum {α : Type*} (s : Finset α) (Q : Finset ℕ)
    (P : ℕ → α → Prop) :
    #{a ∈ s | 2 ≤ #{q ∈ Q | P q a}}
      = ∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U}, #{a ∈ s | {q ∈ Q | P q a} = U} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => {q ∈ Q | P q a})
    (t := {U ∈ Q.powerset | 2 ≤ #U}) (fun a ha => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ha ⊢
      exact ⟨Finset.filter_subset _ _, ha.2⟩)]
  refine Finset.sum_congr rfl fun U hU => ?_
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
  constructor
  · rintro ⟨⟨ha, -⟩, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨⟨ha, h ▸ hU.2⟩, h⟩

end Int

namespace NumberField

open scoped Classical in
/-- The density of the class of Eisenstein–Dumas polynomials whose set of rootless auxiliary
primes is exactly `U`. -/
theorem tendsto_density_fiber {n : ℕ} (hn : 0 < n) {p : ℕ} {c : Fin n → ℕ} {Q : Finset ℕ}
    (hp : p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hpQ : p ∉ Q) {U : Finset ℕ} (hU : U ⊆ Q) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
            {q ∈ Q | ∀ r : ZMod q,
              ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r} = U} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩} : ℝ))
      Filter.atTop (nhds
        ((∏ q ∈ U, (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q : ℝ) ^ n) *
          ∏ q ∈ Q \ U, (1 - (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q : ℝ) ^ n))) := by
  classical
  -- instances at the auxiliary primes
  have hne : ∀ q : Q, NeZero ((q : ℕ)) := fun q => ⟨(hQ q q.2).ne_zero⟩
  have hfact : ∀ q : Q, Fact (Nat.Prime (q : ℕ)) := fun q => ⟨hQ q q.2⟩
  have hcopQ : Pairwise (Function.onFun Nat.Coprime (fun q : Q => (q : ℕ))) := by
    intro q₁ q₂ h
    exact (Nat.coprime_primes (hQ q₁ q₁.2) (hQ q₂ q₂.2)).2 fun hh => h (Subtype.ext hh)
  have hRpos : 0 < ∏ q : Q, (q : ℕ) := Finset.prod_pos fun q _ => (hQ q q.2).pos
  have hRne : NeZero (∏ q : Q, (q : ℕ)) := ⟨hRpos.ne'⟩
  have hcop : Nat.Coprime p (∏ q : Q, (q : ℕ)) :=
    Nat.Coprime.prod_right fun q _ => (Nat.coprime_primes hp (hQ q q.2)).2 fun h => hpQ (h ▸ q.2)
  -- the rootless sets and the class attached to `U`
  set T : ∀ q : Q, Finset (Fin n → ZMod (q : ℕ)) := fun q =>
    {y | ∀ r : ZMod (q : ℕ), ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} with hT
  set S : ∀ q : Q, Finset (Fin n → ZMod (q : ℕ)) := fun q =>
    if (q : ℕ) ∈ U then T q else (T q)ᶜ with hS
  set B : Finset (Fin n → ZMod (∏ q : Q, (q : ℕ))) :=
    {x ∈ (Finset.univ : Finset (Fin n → ZMod (∏ q : Q, (q : ℕ)))) |
      ∀ q : Q, (fun i => ZMod.castHom (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
        (ZMod (q : ℕ)) (x i)) ∈ S q} with hB
  have key := tendsto_density_of_local_condition (c := c) hn hp hRpos hcop B
  -- membership in `T q` for a tuple of integers
  have hmemT : ∀ (q : Q) (a : Fin n → ℤ),
      ((fun i => ((a i : ℤ) : ZMod (q : ℕ))) ∈ T q)
      ↔ (∀ r : ZMod (q : ℕ),
          ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod (q : ℕ))) * X ^ (i : ℕ)).IsRoot r) := by
    intro q a
    rw [hT]
    simp
  -- the dictionary: the residue condition at the auxiliary primes says the rootless set is `U`
  have hdictB : ∀ a : Fin n → ℤ,
      ((fun i => ((a i : ℤ) : ZMod (∏ q : Q, (q : ℕ)))) ∈ B)
      ↔ {q ∈ Q | ∀ r : ZMod q,
          ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r} = U := by
    intro a
    rw [hB]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_intCast, hS]
    constructor
    · intro h
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq, hroot⟩
        by_contra hqU
        have h2 := h ⟨q, hq⟩
        simp only [hqU, ite_false, Finset.mem_compl] at h2
        exact h2 ((hmemT ⟨q, hq⟩ a).2 hroot)
      · intro hqU
        refine ⟨hU hqU, ?_⟩
        have h2 := h ⟨q, hU hqU⟩
        simp only [hqU, ite_true] at h2
        exact (hmemT ⟨q, hU hqU⟩ a).1 h2
    · intro h q
      have hq := Finset.ext_iff.1 h (q : ℕ)
      simp only [Finset.mem_filter] at hq
      by_cases hqU : (q : ℕ) ∈ U
      · simp only [hqU, ite_true]
        exact (hmemT q a).2 (hq.2 hqU).2
      · simp only [hqU, ite_false, Finset.mem_compl]
        intro hmem
        exact hqU (hq.1 ⟨q.2, (hmemT q a).1 hmem⟩)
  -- the cardinality of `B`
  have hcardB : #B = ∏ q : Q, #(S q) := by
    rw [hB]
    exact @Int.card_filter_crt_pi n Q hcopQ hne hRne S
  -- each local factor
  have hcardT : ∀ q : Q, (Nat.card {y : Fin n → ZMod (q : ℕ) //
      ∀ r : ZMod (q : ℕ), ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r}) = #(T q) := by
    intro q
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hT]
  have hcardfun : ∀ q : Q, Fintype.card (Fin n → ZMod (q : ℕ)) = (q : ℕ) ^ n := by
    intro q
    simp
  have hTle : ∀ q : Q, #(T q) ≤ (q : ℕ) ^ n := fun q => by
    rw [← hcardfun q]; exact Finset.card_le_univ _
  have hqpos : ∀ q : Q, (0 : ℝ) < ((q : ℕ) : ℝ) ^ n := fun q => by
    have := (hQ q q.2).pos
    positivity
  -- splitting a product over `Q` according to membership in `U`
  have hsplit : ∀ g h : ℕ → ℝ, (∏ q : Q, (if (q : ℕ) ∈ U then g (q : ℕ) else h (q : ℕ)))
      = (∏ q ∈ U, g q) * ∏ q ∈ Q \ U, h q := by
    intro g h
    rw [Finset.prod_coe_sort Q (fun q => if q ∈ U then g q else h q), Finset.prod_ite]
    congr 1
    · exact Finset.prod_congr (by rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hU])
        fun q _ => rfl
    · exact Finset.prod_congr (by rw [Finset.filter_not, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hU]) fun q _ => rfl
  -- the value of the limit
  have hval : ((#B : ℝ) / ((∏ q : Q, (q : ℕ) : ℕ) : ℝ) ^ n)
      = (∏ q ∈ U, (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q : ℝ) ^ n) *
          ∏ q ∈ Q \ U, (1 - (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q : ℝ) ^ n) := by
    rw [hcardB]
    push_cast
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    refine Eq.trans (Finset.prod_congr rfl fun q _ => ?_)
      (hsplit (fun x => (Nat.card {y : Fin n → ZMod x //
          ∀ r : ZMod x, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (x : ℝ) ^ n)
        (fun x => 1 - (Nat.card {y : Fin n → ZMod x //
            ∀ r : ZMod x, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
          / (x : ℝ) ^ n))
    rw [hcardT q]
    by_cases hqU : (q : ℕ) ∈ U
    · simp only [hS, hqU, ite_true]
    · simp only [hS, hqU, ite_false]
      rw [Finset.card_compl, hcardfun q, Nat.cast_sub (hTle q), Nat.cast_pow, sub_div,
        div_self (hqpos q).ne']
  rw [← hval]
  refine key.congr fun N => ?_
  simp only [hdictB]

open scoped Classical in
/-- **The master density theorem.**  Let `Q` be a finite set of primes different from `p`.  Among
the Eisenstein–Dumas family attached to `p` and the exponents `c`, the proportion of those
polynomials having no root modulo `q` for at least two `q ∈ Q` tends to
`∑_{U ⊆ Q, #U ≥ 2} ∏_{q ∈ U} C_q(n) ∏_{q ∈ Q \ U} (1 - C_q(n))`.

Together with `not_normEuclidean_of_eisensteinDumas_fin`, applied to two primes of `U`, this is
the master theorem: each polynomial counted in the numerator generates a field that is not
norm-Euclidean, as soon as every pair in `Q` admits a representation `p = u q₁ + v q₂` with
`q₁ ∤ u` and `q₂ ∤ v`. -/
theorem tendsto_density_atLeastTwo {n : ℕ} (hn : 0 < n) {p : ℕ} {c : Fin n → ℕ} {Q : Finset ℕ}
    (hp : p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hpQ : p ∉ Q) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
            2 ≤ #{q ∈ Q | ∀ r : ZMod q,
              ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩} : ℝ))
      Filter.atTop (nhds (∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U},
        ((∏ q ∈ U, (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q : ℝ) ^ n) *
          ∏ q ∈ Q \ U, (1 - (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
            / (q : ℝ) ^ n)))) := by
  classical
  have hsum : ∀ N : ℕ,
      (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
          ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
          2 ≤ #{q ∈ Q | ∀ r : ZMod q,
            ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}} : ℝ)
      = ∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U},
          (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
              ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩) ∧
              {q ∈ Q | ∀ r : ZMod q,
                ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}
                  = U} : ℝ) := by
    intro N
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    refine Eq.trans (Int.card_filter_atLeastTwo_eq_sum _ Q _) (Finset.sum_congr rfl fun U _ => ?_)
    congr 1
    ext a
    simp only [Finset.mem_filter]
    tauto
  have hdiv : ∀ (g : Finset ℕ → ℝ) (d : ℝ), (∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U}, g U) / d
      = ∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U}, g U / d := by
    intro g d
    rw [div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun U _ => (div_eq_mul_inv _ _).symm
  simp only [hsum, hdiv]
  refine tendsto_finsetSum _ fun U hU => ?_
  exact tendsto_density_fiber hn hp hQ hpQ (Finset.mem_powerset.1 (Finset.mem_filter.1 hU).1)

end NumberField

/-! ### The complementary bound of the master theorem -/

namespace NumberField

/-- The subsets of `Q` of cardinality at most one are the empty set and the singletons. -/
theorem card_powerset_filter_lt_two (Q : Finset ℕ) :
    #{U ∈ Q.powerset | ¬ 2 ≤ #U} = 1 + #Q := by
  classical
  have : {U ∈ Q.powerset | ¬ 2 ≤ #U} = Q.powersetCard 0 ∪ Q.powersetCard 1 := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hU, hc⟩
      rcases (by omega : #U = 0 ∨ #U = 1) with h | h
      · exact Or.inl ⟨hU, h⟩
      · exact Or.inr ⟨hU, h⟩
    · rintro (⟨hU, h⟩ | ⟨hU, h⟩) <;> exact ⟨hU, by omega⟩
  rw [this, Finset.card_union_of_disjoint, Finset.card_powersetCard, Finset.card_powersetCard]
  · simp
  · refine Finset.disjoint_left.2 fun U hU hU' => ?_
    rw [Finset.mem_powersetCard] at hU hU'
    omega

/-- **The complementary bound.**  If every `c q` lies in `[1/4, 1/2)`, the probability that at
least two of the independent events occur is at least `1 - (1 + #Q) (3/4) ^ #Q`. -/
theorem le_sum_atLeastTwo {Q : Finset ℕ} (c : ℕ → ℝ) (hc0 : ∀ q ∈ Q, 1 / 4 ≤ c q)
    (hc1 : ∀ q ∈ Q, c q < 1 / 2) :
    1 - (1 + #Q) * (3 / 4 : ℝ) ^ #Q
      ≤ ∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U}, (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q) := by
  classical
  have hpos : ∀ q ∈ Q, (0 : ℝ) ≤ 1 - c q := fun q hq => by have := hc1 q hq; linarith
  have hle : ∀ q ∈ Q, 1 - c q ≤ 3 / 4 := fun q hq => by have := hc0 q hq; linarith
  -- the total sum over all subsets is one
  have htot : ∑ U ∈ Q.powerset, (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q) = 1 := by
    have := Finset.prod_add (fun q => c q) (fun q => 1 - c q) Q
    simp only [add_sub_cancel] at this
    rw [← this, Finset.prod_const_one]
  -- the product over all of `Q` is small
  have hprodle : (∏ q ∈ Q, (1 - c q)) ≤ (3 / 4 : ℝ) ^ #Q := by
    calc ∏ q ∈ Q, (1 - c q) ≤ ∏ _q ∈ Q, (3 / 4 : ℝ) := Finset.prod_le_prod hpos hle
      _ = (3 / 4 : ℝ) ^ #Q := by rw [Finset.prod_const]
  -- every class with at most one success is bounded by that product
  have hterm : ∀ U ∈ {U ∈ Q.powerset | ¬ 2 ≤ #U},
      (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q) ≤ (3 / 4 : ℝ) ^ #Q := by
    intro U hU
    rw [Finset.mem_filter, Finset.mem_powerset] at hU
    obtain ⟨hUQ, hcard⟩ := hU
    refine le_trans ?_ hprodle
    rcases (by omega : #U = 0 ∨ #U = 1) with h | h
    · rw [Finset.card_eq_zero.1 h]
      simp
    · obtain ⟨q, rfl⟩ := Finset.card_eq_one.1 h
      have hq : q ∈ Q := hUQ (Finset.mem_singleton_self q)
      rw [Finset.prod_singleton, Finset.sdiff_singleton_eq_erase q Q]
      calc c q * ∏ x ∈ Q.erase q, (1 - c x)
          ≤ (1 - c q) * ∏ x ∈ Q.erase q, (1 - c x) := by
            have h1 : c q ≤ 1 - c q := by have := hc1 q hq; linarith
            have h2 : (0 : ℝ) ≤ ∏ x ∈ Q.erase q, (1 - c x) :=
              Finset.prod_nonneg fun x hx => hpos x (Finset.mem_of_mem_erase hx)
            nlinarith
        _ = ∏ x ∈ Q, (1 - c x) := Finset.mul_prod_erase Q (fun x => 1 - c x) hq
  -- put the two halves together
  have hsplit : ∑ U ∈ Q.powerset, (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q)
      = (∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U}, (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q))
        + ∑ U ∈ {U ∈ Q.powerset | ¬ 2 ≤ #U}, (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsmall : ∑ U ∈ {U ∈ Q.powerset | ¬ 2 ≤ #U}, (∏ q ∈ U, c q) * ∏ q ∈ Q \ U, (1 - c q)
      ≤ (1 + #Q) * (3 / 4 : ℝ) ^ #Q := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [card_powerset_filter_lt_two, nsmul_eq_mul]
    push_cast
    ring_nf
    rfl
  linarith [htot, hsplit, hsmall]

set_option linter.style.haveILetI false in
/-- The local densities `C_q(n)` at a prime `q`, expressed with `Nat.card`, satisfy the bounds of
`le_sum_atLeastTwo`. -/
theorem card_no_root_div_mem_Ico {n : ℕ} (hn : 2 ≤ n) {q : ℕ} (hq : q.Prime) :
    1 / 4 ≤ (Nat.card {y : Fin n → ZMod q //
        ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n,
          C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (q : ℝ) ^ n ∧
      (Nat.card {y : Fin n → ZMod q //
        ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n,
          C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (q : ℝ) ^ n < 1 / 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have hbridge : (Nat.card {y : Fin n → ZMod q //
      ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n,
        C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (q : ℝ) ^ n
      = (#{y : Fin n → ZMod q |
          ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n,
            C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
        / (Fintype.card (ZMod q) : ℝ) ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hcard]
  rw [hbridge]
  exact ⟨Polynomial.card_no_root_univ_div_ge_quarter hn,
    Polynomial.card_no_root_univ_div_lt_half hn⟩

/-- **Proposition 6.1.**  For `n ≥ 2` and a finite set `Q` of primes, the density of the
Eisenstein–Dumas polynomials having no root modulo at least two primes of `Q` is at least
`1 - (1 + #Q) (3/4) ^ #Q`. -/
theorem le_sum_atLeastTwo_of_prime {n : ℕ} (hn : 2 ≤ n) {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) :
    1 - (1 + #Q) * (3 / 4 : ℝ) ^ #Q
      ≤ ∑ U ∈ {U ∈ Q.powerset | 2 ≤ #U},
          (∏ q ∈ U, (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n,
                C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (q : ℝ) ^ n) *
            ∏ q ∈ Q \ U, (1 - (Nat.card {y : Fin n → ZMod q //
              ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n,
                C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (q : ℝ) ^ n) :=
  le_sum_atLeastTwo _ (fun q hq => (card_no_root_div_mem_Ico hn (hQ q hq)).1)
    (fun q hq => (card_no_root_div_mem_Ico hn (hQ q hq)).2)

end NumberField

/-! ### The density of the Eisenstein–Dumas family itself -/

namespace Nat

/-- For `m` coprime to `n` and `0 < j < n`, the two floors `⌊mj/n⌋` and `⌊m(n-j)/n⌋` add up to
`m - 1`. -/
theorem div_add_div_sub_of_coprime {m n j : ℕ} (hm : 0 < m) (hmn : Nat.Coprime m n) (hj1 : 1 ≤ j)
    (hjn : j < n) : m * j / n + m * (n - j) / n = m - 1 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hjn
  set q := m * j / n with hq
  set r := m * j % n with hr
  have hmod : n * q + r = m * j := Nat.div_add_mod (m * j) n
  have hrlt : r < n := Nat.mod_lt _ hn
  have hr0 : r ≠ 0 := by
    intro h
    have hdvd : n ∣ m * j := Nat.dvd_of_mod_eq_zero h
    have hnj : n ∣ j := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hmn) hdvd
    have := Nat.le_of_dvd (by omega) hnj
    omega
  have hqm : q < m := by
    have hlt : m * j < m * n := Nat.mul_lt_mul_of_pos_left hjn hm
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm n m]; exact hlt)
  -- rewrite `m * (n - j)`
  have h1 : m * (n - j) = m * n - m * j := by rw [Nat.mul_sub]
  have h2 : n * (m - q - 1) + n * (q + 1) = n * m := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have h3 : n * (q + 1) = n * q + n := by ring
  have h4 : m * n = n * m := mul_comm m n
  have hsub : m * (n - j) = (n - r) + n * (m - q - 1) := by omega
  rw [hsub, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (by omega)]
  omega

/-- **The floor sum.**  For coprime `m` and `n`, `∑_{j=1}^{n-1} ⌊mj/n⌋ = (m-1)(n-1)/2`. -/
theorem two_mul_sum_div_eq {m n : ℕ} (hm : 0 < m) (hmn : Nat.Coprime m n) :
    2 * ∑ j ∈ Finset.Ico 1 n, m * j / n = (m - 1) * (n - 1) := by
  have hre : ∑ j ∈ Finset.Ico 1 n, (m * (n - j) / n) = ∑ j ∈ Finset.Ico 1 n, (m * j / n) := by
    have h := Finset.sum_Ico_reflect (fun x => m * x / n) 1 (Nat.le_succ n)
    simpa using h
  have key : ∀ j ∈ Finset.Ico 1 n, m * j / n + m * (n - j) / n = m - 1 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact div_add_div_sub_of_coprime hm hmn hj.1 hj.2
  have h2 := Finset.sum_congr rfl key
  rw [Finset.sum_add_distrib, hre, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at h2
  have hcomm : (n - 1) * (m - 1) = (m - 1) * (n - 1) := Nat.mul_comm _ _
  omega

/-- **The exponent of the Eisenstein–Dumas density.**  For coprime `m` and `n`,
`∑_{i<n} ⌈m(n-i)/n⌉ = (m+1)(n+1)/2 - 1`. -/
theorem two_mul_sum_ceil_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    2 * ∑ i ∈ Finset.range n, ((m * (n - i) + n - 1) / n) = (m + 1) * (n + 1) - 2 := by
  have hIco : ∀ a b : ℕ, Finset.Ico a (b + 1) = Finset.Icc a b := fun a b => Finset.val_inj.mp rfl
  -- reflect the sum onto `Icc 1 n`
  have hre : ∑ i ∈ Finset.range n, ((m * (n - i) + n - 1) / n)
      = ∑ j ∈ Finset.Icc 1 n, ((m * j + n - 1) / n) := by
    have h := Finset.sum_Ico_reflect (fun x => (m * x + n - 1) / n) 0 (Nat.le_succ n)
    rw [Finset.range_eq_Ico, h, show n + 1 - n = 1 from by omega,
      show n + 1 - 0 = n + 1 from by omega, hIco]
  -- split off the top term
  have hsplit : ∑ j ∈ Finset.Icc 1 n, ((m * j + n - 1) / n)
      = ((m * n + n - 1) / n) + ∑ j ∈ Finset.Ico 1 n, ((m * j + n - 1) / n) := by
    rw [← hIco 1 n, Finset.sum_Ico_succ_top (by omega)]
    omega
  -- the top term is `m`
  have htop : (m * n + n - 1) / n = m := by
    have : m * n + n - 1 = n * m + (n - 1) := by
      rw [Nat.mul_comm m n]
      omega
    rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  -- each remaining ceiling is one more than the floor
  have hceil : ∀ j ∈ Finset.Ico 1 n, (m * j + n - 1) / n = m * j / n + 1 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hn0 : 0 < n := by omega
    set q := m * j / n with hq
    set r := m * j % n with hr
    have hmod : n * q + r = m * j := Nat.div_add_mod (m * j) n
    have hrlt : r < n := Nat.mod_lt _ hn0
    have hr0 : r ≠ 0 := by
      intro h
      have hdvd : n ∣ m * j := Nat.dvd_of_mod_eq_zero h
      have hnj : n ∣ j := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hmn) hdvd
      have := Nat.le_of_dvd (by omega) hnj
      omega
    have hrw : m * j + n - 1 = n * (q + 1) + (r - 1) := by
      have : n * (q + 1) = n * q + n := by ring
      omega
    rw [hrw, Nat.mul_add_div hn0, Nat.div_eq_of_lt (by omega)]
  rw [hre, hsplit, htop, Finset.sum_congr rfl hceil, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Ico, smul_eq_mul, Nat.mul_one]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hfloor := two_mul_sum_div_eq (m := m' + 1) (n := n' + 1) (by omega) hmn
  have hprod : (m' + 1 + 1) * (n' + 1 + 1) = m' * n' + 2 * m' + 2 * n' + 4 := by ring
  simp only [Nat.add_sub_cancel] at hfloor
  omega

end Nat

namespace Int

/-- **The density of a family of divisibility conditions.**  The proportion of integer tuples in
the box `|a i| ≤ N` with `p ^ d i ∣ a i` for every `i` tends to `p ^ -(∑ i, d i)`. -/
theorem tendsto_density_dvd {n : ℕ} {p : ℕ} (hp : 0 < p) (d : Fin n → ℕ) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ∀ i, (p : ℤ) ^ d i ∣ a i} : ℝ) / (2 * N + 1) ^ n)
      Filter.atTop (nhds (1 / (p : ℝ) ^ (∑ i, d i))) := by
  classical
  have hM : ∀ i : Fin n, 0 < p ^ d i := fun i => by positivity
  have hNe : ∀ i : Fin n, NeZero (p ^ d i) := fun i => ⟨(hM i).ne'⟩
  have key := Int.tendsto_card_box_filter_div_piFinset (M := fun i : Fin n => p ^ d i) hM
    (fun _ => ({0} : Finset (ZMod (p ^ _))))
  -- the value
  have hval : (∏ i : Fin n, (#({0} : Finset (ZMod (p ^ d i))) : ℝ) / (p ^ d i : ℕ))
      = 1 / (p : ℝ) ^ (∑ i, d i) := by
    have : ∀ i : Fin n, (#({0} : Finset (ZMod (p ^ d i))) : ℝ) / ((p ^ d i : ℕ) : ℝ)
        = 1 / (p : ℝ) ^ d i := by
      intro i
      rw [Finset.card_singleton]
      push_cast
      ring
    rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_div_distrib, Finset.prod_const_one,
      ← Finset.prod_pow_eq_pow_sum]
  rw [hval, Fintype.card_fin] at key
  have hdict : ∀ a : Fin n → ℤ,
      ((fun i => ((a i : ℤ) : ZMod (p ^ d i))) ∈
        Fintype.piFinset (fun i : Fin n => ({0} : Finset (ZMod (p ^ d i)))))
      ↔ (∀ i, (p : ℤ) ^ d i ∣ a i) := by
    intro a
    rw [Fintype.mem_piFinset]
    exact forall_congr' fun i => by rw [Finset.mem_singleton, Int.intCast_pow_eq_zero_iff]
  refine key.congr fun N => ?_
  simp only [hdict]

open scoped Classical in
/-- **The density of the Eisenstein–Dumas family.**  For exponents `c` with `c 0 = m`, the
proportion of monic integer polynomials of degree `n` and height at most `N` whose coefficients
satisfy `p ^ c i ∣ a i` and `p ^ (c 0 + 1) ∤ a 0` tends to `(1 - 1/p) p ^ -(∑ i, c i)`.

For the Eisenstein–Dumas exponents `c i = ⌈m (n - i) / n⌉` the exponent `∑ i, c i` is `S(m,n)`,
and for `m = 1` this is the Eisenstein density `p ^ -n - p ^ -(n+1)`. -/
theorem tendsto_density_exact_dvd {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : 0 < p) (c : Fin n → ℕ) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩} : ℝ) / (2 * N + 1) ^ n)
      Filter.atTop (nhds ((1 - 1 / (p : ℝ)) / (p : ℝ) ^ (∑ i, c i))) := by
  classical
  set c' : Fin n → ℕ := Function.update c ⟨0, hn⟩ (c ⟨0, hn⟩ + 1) with hc'
  have hle : ∀ i, c i ≤ c' i := by
    intro i
    rw [hc']
    by_cases hi : i = ⟨0, hn⟩
    · simp [hi]
    · simp [Function.update_of_ne hi]
  have hsum : ∑ i, c' i = (∑ i, c i) + 1 := by
    rw [hc', Finset.sum_update_of_mem (Finset.mem_univ _),
      ← Finset.add_sum_erase _ c (Finset.mem_univ (⟨0, hn⟩ : Fin n)),
      Finset.sdiff_singleton_eq_erase]
    ring
  -- the two divisibility families, the second contained in the first
  have hsub : ∀ N : ℕ,
      {a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
          ∀ i, (p : ℤ) ^ c' i ∣ a i} ⊆
        {a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
          ∀ i, (p : ℤ) ^ c i ∣ a i} := by
    intro N a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, fun i => dvd_trans (pow_dvd_pow _ (hle i)) (ha.2 i)⟩
  -- the numerator is the difference of the two counts
  have hdiff : ∀ N : ℕ,
      (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
          (∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩} : ℝ)
      = (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ∀ i, (p : ℤ) ^ c i ∣ a i} : ℝ)
        - (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ∀ i, (p : ℤ) ^ c' i ∣ a i} : ℝ) := by
    intro N
    have hset : {a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
          (∀ i, (p : ℤ) ^ c i ∣ a i) ∧ ¬ (p : ℤ) ^ (c ⟨0, hn⟩ + 1) ∣ a ⟨0, hn⟩}
        = {a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ∀ i, (p : ℤ) ^ c i ∣ a i} \
          {a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ∀ i, (p : ℤ) ^ c' i ∣ a i} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, not_forall]
      constructor
      · rintro ⟨hbox, hdvd, hnd⟩
        refine ⟨⟨hbox, hdvd⟩, fun _ => ⟨⟨0, hn⟩, ?_⟩⟩
        rwa [hc', Function.update_self]
      · rintro ⟨⟨hbox, hdvd⟩, h2⟩
        obtain ⟨i, hi⟩ := h2 hbox
        refine ⟨hbox, hdvd, ?_⟩
        by_cases hi0 : i = ⟨0, hn⟩
        · subst hi0
          rwa [hc', Function.update_self] at hi
        · exact absurd (dvd_trans (pow_dvd_pow _
            (le_of_eq (by simp [hc', Function.update_of_ne hi0]))) (hdvd i)) hi
    rw [hset, Finset.card_sdiff, Finset.inter_eq_left.2 (hsub N),
      Nat.cast_sub (Finset.card_le_card (hsub N))]
  simp only [hdiff]
  have h1 := tendsto_density_dvd (n := n) hp c
  have h2 := tendsto_density_dvd (n := n) hp c'
  have hlim := h1.sub h2
  rw [hsum] at hlim
  have hvalue : (1 : ℝ) / (p : ℝ) ^ (∑ i, c i) - 1 / (p : ℝ) ^ ((∑ i, c i) + 1)
      = (1 - 1 / (p : ℝ)) / (p : ℝ) ^ (∑ i, c i) := by
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp
    have hspos : (0 : ℝ) < (p : ℝ) ^ (∑ i, c i) := by positivity
    rw [pow_succ]
    field_simp
  rw [← hvalue]
  exact hlim.congr fun N => (sub_div _ _ _).symm

end Int

namespace NumberField

open Filter

/-- **Theorem 1.4: the density of the Eisenstein–Dumas family.**  For coprime `m, n ≥ 1` and a
prime `p`, the proportion of monic integer polynomials of degree `n` and height at most `N` that
satisfy the Eisenstein–Dumas condition at `p` of slope `m / n` tends to
`(1 - 1/p) p ^ -S(m,n)` with `S(m,n) = (m+1)(n+1)/2 - 1`.

For `m = 1` this is `S(1,n) = n`, the Eisenstein density `p ^ -n - p ^ -(n+1)`. -/
theorem tendsto_density_eisensteinDumas {n m p : ℕ} (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hmn : Nat.Coprime m n) :
    Filter.Tendsto (fun N : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i : Fin n, (p : ℤ) ^ ((m * (n - (i : ℕ)) + n - 1) / n) ∣ a i) ∧
              ¬ (p : ℤ) ^ (m + 1) ∣ a ⟨0, hn⟩} : ℝ) / (2 * N + 1) ^ n)
      Filter.atTop (nhds ((1 - 1 / (p : ℝ)) / (p : ℝ) ^ ((m + 1) * (n + 1) / 2 - 1))) := by
  classical
  set c : Fin n → ℕ := fun i => (m * (n - (i : ℕ)) + n - 1) / n with hc
  -- the exponent at the constant coefficient is `m`
  have hc0 : c ⟨0, hn⟩ = m := by
    have h1 : m * (n - (0 : ℕ)) + n - 1 = n * m + (n - 1) := by
      rw [Nat.sub_zero, Nat.mul_comm m n]
      omega
    rw [hc]
    change (m * (n - (0 : ℕ)) + n - 1) / n = m
    rw [h1, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  -- the sum of the exponents is `S(m,n)`
  have hsum : ∑ i : Fin n, c i = (m + 1) * (n + 1) / 2 - 1 := by
    have h2 := Nat.two_mul_sum_ceil_eq hm hn hmn
    have h3 : ∑ i : Fin n, c i = ∑ i ∈ Finset.range n, ((m * (n - i) + n - 1) / n) := by
      rw [hc, Fin.sum_univ_eq_sum_range (fun i => (m * (n - i) + n - 1) / n) n]
    have heven : 2 ∣ (m + 1) * (n + 1) := by
      rcases Nat.even_or_odd m with hme | hmo
      · rcases Nat.even_or_odd n with hne | hno
        · exfalso
          have h2m : 2 ∣ m := hme.two_dvd
          have h2n : 2 ∣ n := hne.two_dvd
          have := Nat.dvd_gcd h2m h2n
          rw [hmn] at this
          omega
        · exact Dvd.dvd.mul_left hno.add_one.two_dvd _
      · exact Dvd.dvd.mul_right hmo.add_one.two_dvd _
    have hge : 2 ≤ (m + 1) * (n + 1) := by nlinarith
    omega
  have key := Int.tendsto_density_exact_dvd (n := n) hn hp c
  rw [hc0, hsum] at key
  exact key

end NumberField

namespace NumberField

open scoped Classical in
/-- **The lower density form of the master theorem.**  For `n ≥ 2` and a finite set `Q` of primes
different from `p`, the proportion of the Eisenstein–Dumas family whose polynomial has no root
modulo at least two primes of `Q` is eventually at least `1 - (1 + #Q) (3/4) ^ #Q - ε`.

Every polynomial counted in the numerator generates a field that is not norm-Euclidean, by
`not_normEuclidean_of_eisensteinDumas_fin` applied to two of those primes; so this is the lower
density bound of the master theorem. -/
theorem eventually_le_density_atLeastTwo {n : ℕ} (hn : 2 ≤ n) {p : ℕ} {c : Fin n → ℕ}
    {Q : Finset ℕ} (hp : p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hpQ : p ∉ Q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      1 - (1 + #Q) * (3 / 4 : ℝ) ^ #Q - ε ≤
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩) ∧
            2 ≤ #{q ∈ Q | ∀ r : ZMod q,
              ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩} : ℝ) := by
  have hlim := tendsto_density_atLeastTwo (n := n) (c := c) (by omega) hp hQ hpQ
  have hbound := le_sum_atLeastTwo_of_prime (n := n) hn hQ
  refine hlim.eventually_const_le ?_
  linarith

end NumberField
