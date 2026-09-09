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
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Units

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
  -- the representation `p = u q₁ + v q₂`
  obtain ⟨u, v, hu0, hv0, hpuv, hqu, hqv⟩ := hrep
  -- `u q₁` is an `n`-th power residue modulo `p`
  have hnez : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨x, hx⟩ := Nat.exists_pow_eq_of_coprime_sub_one hp hn.ne' hcop ((u * q₁ : ℕ) : ZMod p)
  have hxdvd : (p : ℤ) ∣ (x.val : ℤ) ^ n - ((u * q₁ : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [sub_eq_zero]
    exact_mod_cast hx
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
    (a := (u * q₁ : ℕ)) (b := (v * q₂ : ℕ)) (x := (x.val : ℤ))
    (by exact_mod_cast Nat.mul_pos hu0 hq₁.pos) (by exact_mod_cast Nat.mul_pos hv0 hq₂.pos)
    (by exact_mod_cast hpuv) ?_ hna hnb
  rw [hdeg]
  exact hxdvd

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
