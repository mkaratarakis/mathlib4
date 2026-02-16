/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.Tactic

/-!
# Hilbert's Seventh Problem (Gelfond–Schneider Theorem)
The goal of this file is to formalize a proof of the **Gelfond–Schneider Theorem**, which solves
Hilbert’s Seventh Problem: namely, that for algebraic numbers `α ≠ 0, 1` and irrational algebraic
`β`, the number `α ^ β` is transcendental.

## Main results
* `gelfondSchneider`: If `α` and `β` are algebraic, `α ≠ 0`, `α ≠ 1`, and `β` is irrational, then
  `α ^ β` is transcendental.

## Implementation details
We follow the proof in Keng’s *Introduction to Number Theory*, Chapter 17, Section 5, p.488 - 493.

The argument proceeds by contradiction. The core of the proof is an auxiliary function lemma, where
we construct a nonzero integer linear combination of exponential functions that vanishes to high
order at several algebraic points.

## References
Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter XII (§13).
A. O. Gelfond (1934), *Sur le septième Problème de Hilbert
T. Schneider (1935), *Transzendenzuntersuchungen periodischer Funktionen*
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

/-!
Suppose that `α, β, γ` lie in an algebraic field `K` with degree `h`.
-/

lemma isNumberField_adjoin_alg_numbers (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : NumberField (adjoin ℚ {α, β, γ}) := {
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin (fun x hx ↦ by
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with ⟨ha, hb⟩
  · simp_rw [isAlgebraic_iff_isIntegral.1 hα]
  rename_i hb
  rcases hb with ⟨hb,hc⟩;
  · simp_rw [isAlgebraic_iff_isIntegral.1 hβ]
  rename_i hc
  simp_rw [mem_singleton_iff.1 hc, isAlgebraic_iff_isIntegral.1 hγ])}

lemma adjoin_simple_le_adjoin_insert (α β : ℂ) (_ : IsAlgebraic ℚ α) (_ : IsAlgebraic ℚ β) :
    (adjoin _ {α} ≤ adjoin ℚ {α, β}) ∧ (adjoin _ {β} ≤ adjoin ℚ {α, β}) :=
  ⟨by apply adjoin.mono; intros x hx; left; exact hx,
   by apply adjoin.mono; intros x hx; right; exact hx⟩

lemma exists_common_field_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ)
    (_ : DecidableEq (K →+* ℂ)), ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have hab := adjoin.mono ℚ {α, β} {α, β, γ} fun x hxab ↦ by
    rcases hxab with ⟨hxa, hxb⟩
    · left; simp only
    simp_all only [mem_singleton_iff, mem_insert_iff, mem_singleton_iff, true_or, or_true]
  refine ⟨adjoin ℚ {α, β, γ}, ?_⟩
  let σ : ↥ℚ⟮α, β, γ⟯ →+* ℂ :=
    { toFun := fun x ↦ x.1, map_one' := rfl, map_mul' := fun x y ↦ rfl
      map_zero' := rfl, map_add' := fun x y ↦ rfl}
  refine ⟨inferInstance, isNumberField_adjoin_alg_numbers α β γ hα hβ hγ, σ,
    Classical.typeDecidableEq (↥ℚ⟮α, β, γ⟯ →+* ℂ), ⟨⟨α, ?_⟩, ⟨β, ?_⟩, ⟨γ, ?_⟩, ?_⟩⟩
  · exact adjoin_simple_le_iff.1 fun _ hx ↦ hab ((adjoin_simple_le_adjoin_insert  α β hα hβ).1 hx)
  · refine adjoin_simple_le_iff.1 fun _ hx ↦ hab ?_
    apply adjoin.mono;
    intros x hx;
    · right; exact hx;
    · exact hx
  · exact adjoin_simple_le_iff.1 fun _ hx ↦ (adjoin.mono ℚ {α, γ} {α, β, γ} (fun x hx ↦ by grind))
     ((adjoin_simple_le_adjoin_insert α γ hα hγ).2 hx)
  aesop

variable {K} [Field K] [NumberField K]

lemma exists_int_smul_isIntegral {K : Type*} [Field K] [NumberField K] (α : K) :
    ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

/--
A choice of a non-zero integer `c₀` such that `c₀ • α` is an algebraic integer.
-/
def c₀ {K : Type*} [Field K] [NumberField K] (α : K) : {c : ℤ // c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(exists_int_smul_isIntegral α).choose, (exists_int_smul_isIntegral α).choose_spec⟩

/-- A choice of a non-zero integer `c₀` such that `c • α` is an algebraic integer.
See `c₀`. -/
abbrev c₀Coeff {K : Type*} [Field K] [NumberField K] (α : K) : ℤ := (c₀ α : ℤ)

lemma c₀Coeff_ne_zero (α : K) : c₀Coeff α ≠ 0 := (c₀ α).2.1

/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational. We prove that `αᵇ` is
transcendental by contradiction. Suppose `γ = αᵇ = e^(β log α)` is also algebraic.
-/

/--
This structure encapsulates all the foundational data and hypotheses for the proof.
-/
structure Setup where
  (α β : ℂ)
  (K : Type)
  [isField : Field K]
  [isNumberField : NumberField K]
  (σ : K →+* ℂ)
  (α' β' γ' : K)
  hirr : ∀ i j : ℤ, β ≠ i / j
  htriv : α ≠ 0 ∧ α ≠ 1
  hα : IsAlgebraic ℚ α
  hβ : IsAlgebraic ℚ β
  habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ'
  hd : DecidableEq (K →+* ℂ)

namespace Setup

attribute [instance] isField isNumberField

variable (h7 : Setup)

open Setup

lemma alpha_cpow_beta_ne_zero : h7.α ^ h7.β ≠ 0 :=
  fun H ↦ h7.htriv.1 ((cpow_eq_zero_iff h7.α h7.β).mp H).1

lemma beta_ne_zero : h7.β ≠ 0 :=
  fun H ↦ h7.hirr 0 1 (by simpa [div_one] using H)

lemma alpha'_beta'_gamma'_ne_zero : h7.α' ≠ 0 ∧ h7.β' ≠ 0 ∧ h7.γ' ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro H
  · exact h7.htriv.1 (by simp [h7.habc.1, H, RingHom.map_zero h7.σ])
  · exact h7.beta_ne_zero (by simp [h7.habc.2.1, H, RingHom.map_zero h7.σ])
  · exact h7.alpha_cpow_beta_ne_zero (by simp [h7.habc.2.2, H, RingHom.map_zero h7.σ])

lemma alpha'_ne_one : h7.α' ≠ 1 := fun h ↦
  h7.htriv.2 <| by simpa [h7.habc.1, map_one] using congrArg h7.σ h

lemma beta'_ne_zero : h7.β' ≠ 0 := h7.alpha'_beta'_gamma'_ne_zero.2.1

open Complex

lemma log_zero_zero : log h7.α ≠ 0 :=
  mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2

def c₁ : ℤ := abs (c₀ h7.α' * c₀ h7.β' * c₀ h7.γ')

lemma one_le_c₁ : 1 ≤ h7.c₁ := by
  simpa [c₁] using Int.one_le_abs <| mul_ne_zero (mul_ne_zero (c₀Coeff_ne_zero h7.α')
    (c₀Coeff_ne_zero h7.β')) (c₀Coeff_ne_zero h7.γ')

lemma one_le_abs_c₁ : 1 ≤ |↑h7.c₁| := Int.one_le_abs (Ne.symm (Int.ne_of_lt h7.one_le_c₁))

lemma IsIntegral_assoc (K : Type) [Field K] {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
    IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  simpa [Int.cast_mul, zsmul_eq_mul, mul_assoc] using IsIntegral.smul (x * y) ha

lemma isIntegral_c₁α : IsIntegral ℤ (h7.c₁ • h7.α') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.α') h7.α'
    ((c₀ h7.α').2.2)
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (c₀Coeff h7.α') (c₀Coeff h7.β'), ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.β' * c₀Coeff h7.α') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (h7.c₁ • h7.β') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.α') h7.K (c₀Coeff h7.β') h7.β'
    ((c₀ h7.β').2.2)
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.α' * c₀Coeff h7.β') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (h7.c₁ • h7.γ') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.α') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.γ') h7.γ'
    ((c₀ h7.γ').2.2)
  rw [c₁]
  rcases abs_choice (c₀Coeff h7.α' * c₀Coeff h7.β' * c₀Coeff h7.γ') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

def h : ℕ := Module.finrank ℚ h7.K

/-!
Let `m = 2h + 2`, and `n = q ^ 2 / (2 * h7.m)`, where $q^2 = t $ is a square of a natural number
and is a multiple of $2m.$ Following the reference text, we define parameters `m` and `n` dependent
on the degree `h = [K : ℚ]` and a free parameter `q`.  -/

def m : ℕ := 2 * h7.h + 2

lemma one_le_m : 1 ≤ h7.m := Nat.succ_le_succ (Nat.zero_le (2 * h7.h + 1))

def n (q : ℕ) : ℕ := q ^ 2 / (2 * h7.m)


variable (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q)) (t : Fin (q * q))

/- Also, let `ρ₁, ρ₂, …, ρₜ` represent the `t` numbers
  `(a + bβ) log α,  1 ≤ a ≤ q, 1 ≤ b ≤ q.`-/

-- `a, b, k, l` are values that depend on the context variables `t` and `u`.
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1
def k : ℕ := (finProdFinEquiv.symm.toFun u).2
def l : ℕ := (finProdFinEquiv.symm.toFun u).1 + 1

def ρ : ℂ := (a q t + (b q t • h7.β)) * Complex.log h7.α

lemma b_le_q : b q t ≤ q := ((finProdFinEquiv.symm.toFun t).2).isLt

lemma l_le_m : h7.l q u ≤ h7.m := ((finProdFinEquiv.symm.toFun u).1).isLt

lemma a_le_q : a q t ≤ q := ((finProdFinEquiv.symm.toFun t).1).isLt

/-!
We introduce the integral function
  `R(x) = η₁ e^(ρ₁ x) + … + ηₜ e^(ρₜ x)`
where the coefficients `η₁, …, ηₜ` are determined by the following conditions.

We solve the system of `mn` homogeneous linear equations
  `(log α)⁻ᵏ R⁽ᵏ⁾(l) = 0,  0 ≤ k ≤ n - 1, 1 ≤ l ≤ m`
in the `t = 2mn` unknowns `η₁, …, ηₜ`.

The coefficients are in `K` and
  `(log α)⁻ᵏ ((a + bβ) log α)ᵏ e^(l(a + bβ) log α) = (a + bβ)ᵏ αᵃˡ γᵇˡ`
for `1 ≤ l ≤ m, 1 ≤ a, b ≤ q, 0 ≤ k ≤ n - 1`.-/

/-!
Let `c₁, c₂, …` be natural numbers independent of `n`. There exists `c₁` such that
`c₁ α, c₁ β, c₁ γ` are integers in `K`. Multiplying the system by
`c₁ⁿ⁻¹ c₁ᵐᵠ c₁ᵐᵠ = c₁^{n-1+2mq} ≤ c₁^n` ensures the coefficients are integers in `K`.
-/

abbrev c_coeffs0 (q : ℕ) (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :=
  h7.c₁ ^ (h7.k q u : ℕ) * h7.c₁ ^ (a q t * h7.l q u) * h7.c₁ ^ (b q t * h7.l q u)

lemma IsIntegral.Cast (K : Type) [Field K] (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma c₁ac (u : h7.K) (n k a l : ℕ) (hnk : a * l ≤ n * k) (H : IsIntegral ℤ (↑h7.c₁ * u)) :
    IsIntegral ℤ (h7.c₁ ^ (n * k) • u ^ (a *l)) := by
  have : h7.c₁ ^ (n * k) = h7.c₁ ^ (n * k - a * l) * h7.c₁ ^ (a *l) := by
    rw [← pow_add]; rwa [Nat.sub_add_cancel]
  rw [this, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow]; rw [mul_assoc]
  apply IsIntegral.mul <| IsIntegral.pow (IsIntegral.Cast h7.K h7.c₁) _
  rw [← mul_pow]; exact IsIntegral.pow H _

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma c₁b (n : ℕ) (_ : 1 ≤ n) (k : ℕ) (hkn : k ≤ n - 1) (a : ℕ) (_ : 1 ≤ a) (b : ℕ) (_ : 1 ≤ b) :
    IsIntegral ℤ (h7.c₁ ^ (n - 1) • (↑a + ↑b • h7.β') ^ k) := by
  have : h7.c₁^(n - 1) = h7.c₁^(n - 1 - k) * h7.c₁^k := by
    rwa [← pow_add, Nat.sub_add_cancel]
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.pow (IsIntegral.Cast h7.K h7.c₁) _
  rw [← mul_pow]
  apply IsIntegral.pow _ _
  rw [mul_add]
  apply IsIntegral.add _ _
  · apply IsIntegral.mul <| IsIntegral.Cast _ _
    · apply IsIntegral.Nat
  rw [mul_comm, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.Nat _ _
  rw [mul_comm, ← zsmul_eq_mul]
  exact isIntegral_c₁β h7

lemma c1a0 : IsIntegral ℤ (h7.c₁ ^ (a q t * h7.l q u) • (h7.α' ^ (a q t * h7.l q u))) := by
  apply h7.c₁ac h7.α' (a q t) (h7.l q u) (a q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α

lemma c1c0 : IsIntegral ℤ (h7.c₁ ^ (b q t * h7.l q u) • (h7.γ'^ (b q t * (h7.l q u)))) := by
  apply h7.c₁ac h7.γ' (b q t) (h7.l q u) (b q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

open Nat in include hq0 in
lemma c1a : IsIntegral ℤ (h7.c₁^(h7.m * q) • (h7.α' ^ (a q t * h7.l q u))) := by
  refine h7.c₁ac h7.α' (h7.m) q (a q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
      (add_le_of_le_sub hq0 (le_sub_one_of_lt ((finProdFinEquiv.symm.1 t).1).isLt))
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α

open Nat in include hq0 in
lemma c1c : IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.γ'^ (b q t * h7.l q u))) := by
  refine h7.c₁ac h7.γ' (h7.m) q (b q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt)) (add_le_of_le_sub hq0 (le_sub_one_of_lt
        (finProdFinEquiv.symm.1 t).2.isLt))
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

abbrev sys_coe : h7.K :=
  (a q t + b q t • h7.β') ^ (h7.k q u) * h7.α' ^ (a q t * h7.l q u) * h7.γ' ^ (b q t * h7.l q u)

variable (h2mq : 2 * h7.m ∣ q ^ 2)

include h2mq in
lemma q_eq_2sqrtmn : q ^ 2 = 2 * h7.m * h7.n q := Eq.symm (Nat.mul_div_cancel' h2mq)

open Real

include h2mq in
lemma q_eq_sqrtmn : q = sqrt (2*h7.m*h7.n q) := by
  norm_cast
  rw [← h7.q_eq_2sqrtmn q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, sqrt_sq]

include hq0 h2mq in
lemma card_mn_pos : 0 < h7.m * h7.n q := by
  simp only [CanonicallyOrderedAdd.mul_pos]
  refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), ?_⟩
  · simp only [n, Nat.div_pos_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (by positivity) h2mq⟩

include hq0 h2mq in
lemma one_le_n : 1 ≤ h7.n q := by
  rw [n, Nat.one_le_div_iff]
  · apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq
  · exact Nat.zero_lt_succ (Nat.mul 2 (2 * h7.h + 1) + 1)

include hq0 h2mq in
lemma n_neq_zero : h7.n q ≠ 0 := Nat.ne_zero_of_lt (h7.one_le_n q hq0 h2mq)

include hq0 h2mq in
lemma qsqrt_le_2m : 2 * h7.m ≤ q ^ 2 := Nat.le_of_dvd (Nat.pow_pos hq0) h2mq

lemma hm : 0 < h7.m := Nat.zero_lt_succ (2 * h7.h + 1)

include hq0 h2mq in
lemma h0m : 0 < h7.m * h7.n q := mul_pos (h7.hm) (h7.one_le_n q hq0 h2mq)

include hq0 h2mq in
lemma hmn : h7.m * h7.n q < q * q := by
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  rw [← pow_two q, ← mul_lt_mul_iff_right₀ (Nat.zero_lt_two)]
  rw [← mul_assoc, n, h2mq, lt_mul_iff_one_lt_left (Nat.pow_pos hq0)]
  · exact one_lt_two

include h2mq in
lemma sq_le_two_mn : q ^ 2 ≤ 2 * h7.m * h7.n q := by
  simpa using le_of_eq (h7.q_eq_2sqrtmn q h2mq)

abbrev c_coeffs (q : ℕ) := h7.c₁ ^ (h7.n q - 1) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)

open Nat in include hq0 h2mq in
lemma c₁IsInt (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :
    IsIntegral ℤ (h7.c_coeffs q • h7.sys_coe q u t) := by
  have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
     ((a * b) * c) • ((x * y) * z) = a•x * b•y * c•z := by
    simp only [zsmul_eq_mul, Int.cast_mul]; ring
  rw [triple_comm h7.K (h7.c₁ ^ (h7.n q - 1) : ℤ) (h7.c₁ ^ (h7.m * q) : ℤ)
      (h7.c₁ ^ (h7.m * q) : ℤ) (((a q t) + b q t • h7.β') ^ (h7.k q u)) (h7.α' ^ (a q t * h7.l q u))
      (h7.γ' ^ (b q t * h7.l q u))]
  rw [mul_assoc]
  apply IsIntegral.mul ?_ (IsIntegral.mul (h7.c1a q hq0 u t) (h7.c1c q hq0 u t))
  · exact h7.c₁b (h7.n q) (h7.one_le_n q hq0 h2mq) (h7.k q u)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt)
      (a q t) (le_add_left 1 (finProdFinEquiv.symm.1 t).1)
      (b q t) (le_add_left 1 (finProdFinEquiv.symm.1 t).2)

lemma c₁_ne_zero : h7.c₁ ≠ 0 := Ne.symm (Int.ne_of_lt h7.one_le_c₁)

lemma c₁αneq0 : h7.c₁ • h7.α' ≠ 0 := by
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).1⟩

lemma c₁cneq0 : h7.c₁ • h7.γ' ≠ 0 := by
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

lemma c_coeffs_neq_zero : h7.c_coeffs q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁))))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))

def A : Matrix (Fin (h7.m * h7.n q)) (Fin (q * q)) (𝓞 h7.K) :=
  fun i j ↦ RingOfIntegers.restrict _ (fun _ ↦ (h7.c₁IsInt q hq0 h2mq i j)) ℤ

lemma β'_neq_zero (y : ℕ) : (↑↑(a q t) + (↑(b q t)) • h7.β') ^ y ≠ 0 := by
  apply pow_ne_zero
  intro H
  have H1 : h7.β' = (↑↑(a q t))/ (-(↑(b q t))) := by
    rw [eq_div_iff_mul_eq]
    · rw [← eq_neg_iff_add_eq_zero] at H
      rw [mul_neg, mul_comm, H]
      grind
    intros H
    norm_cast at H
    have : b q t ≠ 0 := by unfold b; aesop
    apply this
    exact H.1
  apply h7.hirr (↑(a q t)) (-(↑(b q t)))
  rw [h7.habc.2.1, H1]
  simp only [map_div₀, map_natCast, map_neg, Int.cast_natCast, Int.cast_neg]

lemma add_nsmul_beta_ne_add_nsmul_beta_of_ne (i1 i2 j1 j2 : ℕ) (Heq : ¬ i2 = j2) :
    i1 + i2 • h7.β ≠ j1 + j2 • h7.β := fun h ↦
  h7.hirr ((i1 : ℤ) - j1) ((j2 : ℤ) - i2) (by simpa [Int.cast_sub, Int.cast_natCast] using
    ((eq_div_iff (sub_ne_zero.mpr (by aesop))).2 (by grind)))

include hq0 in
lemma b_sum_neq_zero : (↑q : h7.K) + q • h7.β' ≠ 0 := by
  intro H
  have hqC : (q : ℂ) ≠ 0 := mod_cast (Nat.ne_zero_of_lt hq0)
  have hEq : (q : ℂ) + (q : ℂ) * h7.β = 0 := by
    simpa [nsmul_eq_mul, map_add, map_mul, map_natCast, ← h7.habc.2.1] using (congrArg h7.σ H)
  exact h7.hirr (-1) 1 (by simpa [div_one] using
    ((eq_neg_of_add_eq_zero_right ((mul_eq_zero.mp (by grind)).resolve_left hqC))))

lemma house_bound_c₁α :
    house (h7.c₁ • h7.α') ^ (a q t * h7.l q u) ≤ house (h7.c₁ • h7.α') ^ (h7.m * q) := by
  refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨one_le_house_of_isIntegral
    (h7.isIntegral_c₁α) h7.c₁αneq0, ?_⟩)
  simpa [mul_comm] using mul_le_mul (a_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _)

lemma isInt_β_bound : IsIntegral ℤ (h7.c₁ • (↑q + q • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (IsIntegral.add ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K q))
    ((IsIntegral.Nat h7.K q).mul h7.isIntegral_c₁β))

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
    IsIntegral ℤ (h7.c₁ • (↑(a q t) + b q t • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_add,
  mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
  (IsIntegral.add
    ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K (a q t)))
    ((IsIntegral.Nat h7.K (b q t)).mul h7.isIntegral_c₁β))

lemma bound_c₁β (q : ℕ) (hq0 : 0 < q) : 1 ≤ house ((h7.c₁ • (q + q • h7.β'))) := by
  apply one_le_house_of_isIntegral (h7.isInt_β_bound q)
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), h7.b_sum_neq_zero q hq0⟩

lemma one_le_house_c₁γ : 1 ≤ house (h7.c₁ • h7.γ') := by
  apply one_le_house_of_isIntegral h7.isIntegral_c₁γ
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

lemma hM_ne_zero : h7.A q hq0 h2mq ≠ 0 := by
  simp (config :=  {unfoldPartialApp := true} ) only [A]
  rw [Ne, funext_iff]
  simp only [zsmul_eq_mul, RingOfIntegers.restrict]
  intros H
  let u : Fin (h7.m * h7.n q) := ⟨0, h7.card_mn_pos q hq0 h2mq⟩
  specialize H u
  rw [funext_iff] at H
  let t : Fin (q * q) := ⟨0, (mul_pos hq0 hq0)⟩
  specialize H t
  simp only [Int.cast_mul, Int.cast_pow, zero_apply] at H
  injection H with H
  simp only [mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or] at H
  rcases H
  · rename_i H1; rcases H1;
    · rename_i H1 ; rcases H1 with ⟨H1, H11⟩
      · apply h7.c₁_ne_zero; assumption
      · rename_i H11; apply h7.c₁_ne_zero; exact H11.1
    rename_i H1; apply h7.c₁_ne_zero; exact H1.1
  · rename_i H2;
    rcases H2 with ⟨H2, H22⟩
    · apply h7.β'_neq_zero q t (h7.k q u); aesop
    · rename_i H1; apply (h7.alpha'_beta'_gamma'_ne_zero).1; exact H1.1
    rename_i H2;
    apply (h7.alpha'_beta'_gamma'_ne_zero).2.2
    exact H2.1

def c₂ : ℤ := (|h7.c₁| ^ (((1 + 2*h7.m * (↑2*h7.m))) + (1 + 2*h7.m * (↑2*h7.m))))

lemma one_le_c₂ : 1 ≤ h7.c₂ := by
  apply le_trans (Int.cast_one_le_of_pos (h7.one_le_abs_c₁))
  nth_rw 1 [← pow_one (a:= |h7.c₁|)]
  apply pow_le_pow_right₀ (h7.one_le_abs_c₁)
  exact Nat.le_add_left 1 ((1 + 2 * h7.m * (2 * h7.m)).add (Nat.add 1
    (((2 * h7.m).mul (Nat.mul 2 (2 * h7.h + 1) + 1)).add (Nat.mul 2 (2 * h7.h + 1) + 1))))

def c₃ : ℝ := h7.c₂ * (1 + house h7.β')* sqrt (2 * h7.m) *
  (max 1 (((house h7.α' ^ (2 * h7.m ^ 2)) * house h7.γ' ^(2 * h7.m ^2))))

lemma one_le_c₃ : 1 ≤ h7.c₃ := by
  trans
  · have := h7.one_le_c₂; norm_cast at this
  · simp only [c₃, mul_assoc]
    norm_cast
    refine one_le_mul_of_one_le_of_one_le (by norm_cast; exact h7.one_le_c₂) ?_
    · have h1 : 1 ≤ (1 + house h7.β') := by
        simp only [le_add_iff_nonneg_right]; apply house_nonneg
      have h2 : 1 ≤ (max 1 ((house h7.α' ^ (2 * h7.m ^ 2) *
        house h7.γ' ^ (2 * h7.m ^ 2)) ^ 2 * ↑(h7.m))) := le_max_left _ _
      have h3 : 1 ≤ ((sqrt ((2*h7.m)))) := by
         rw [one_le_sqrt]
         apply le_trans (mod_cast h7.hm) (le_mul_of_one_le_left (by simp) (one_le_two))
      calc 1 ≤ (1 + house h7.β') := h1
           _ ≤ (1 + house h7.β') * (sqrt ((2*h7.m))) := by
            nth_rw 1 [← mul_one (a := (1 + house h7.β'))]
            apply mul_le_mul (Preorder.le_refl (1 + house h7.β')) (h3)
              (zero_le_one' ℝ) (zero_le_one.trans h1)
      nth_rw 1 [← mul_one (a := (1 + house h7.β') * (sqrt ((2*h7.m))))]
      simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
      apply mul_le_mul (le_refl _) ?_ (by grind) (by grind)
      · apply mul_le_mul (le_refl _) (by grind) (by positivity) (by positivity)

lemma house_add_mul_le :
    house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ≤ (|h7.c₁| * |(q : ℤ)|) * (1 + house (h7.β')) := by
  calc _ ≤ house (h7.c₁ • ((a q t : ℤ) : h7.K)) + house (h7.c₁ • ((b q t : ℤ) • h7.β')) := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) + house (h7.c₁ : h7.K) *
           house ((b q t : ℤ) • h7.β') := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) + house (h7.c₁ : h7.K) *
           (house ((b q t : ℤ) : h7.K) * house ( h7.β')) := ?_
       _ = |h7.c₁| * |(a q t : ℤ)| + |h7.c₁| * |(b q t : ℤ)| * house (h7.β') := ?_
       _ ≤ |h7.c₁| * |(q : ℤ)| + |h7.c₁| * |(q : ℤ)| * house h7.β' := ?_
       _ = |h7.c₁| * |(q : ℤ)| * (1 + house h7.β') := ?_
  · norm_cast; rw [smul_add]; apply house_add_le
  · refine add_le_add (by rw [zsmul_eq_mul]; apply house_mul_le)
      (by rw [zsmul_eq_mul]; apply house_mul_le)
  · refine add_le_add (by grind) (?_)
    · refine mul_le_mul (le_refl _) (by rw [zsmul_eq_mul]; apply house_mul_le)
        (house_nonneg _) (house_nonneg _)
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add (mul_le_mul (le_refl _) (mod_cast ((finProdFinEquiv.symm.toFun t).1).isLt)
      (Int.cast_nonneg (Int.zero_le_ofNat (a q t))) (Int.cast_nonneg  (abs_nonneg (h7.c₁)))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (by rfl) ?_ (mul_nonneg (by positivity) (house_nonneg _)) (by simp)
      · apply mul_le_mul (mod_cast ((finProdFinEquiv.symm.toFun t).2).isLt) (le_refl _)
          (house_nonneg _) ?_
        · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
  · rw [mul_add]; simp only [Int.cast_abs, mul_one]

lemma c₃_pow : h7.c₃ ^ ↑(h7.n q : ℝ) = h7.c₂ ^ ↑(h7.n q) * ((1 + house (h7.β'))^ ↑(h7.n q)) *
    (sqrt ((2*h7.m)) ^ ↑(h7.n q)) * (max 1 ((house (h7.α') ^ (2*h7.m^2)) * house (h7.γ') ^
    (2*h7.m^2)))^ ↑(h7.n q) := by
  simp only [c₃, rpow_natCast]; rw [mul_pow, mul_pow, mul_pow]

include h2mq in
lemma q_eq_n_etc : q ^ ((h7.n q) - 1) ≤ (sqrt (2 * h7.m) ^ ((h7.n q) - 1)) * (sqrt (h7.n q)) ^
  ((h7.n q) - 1) := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ (h7.n q - 1)
  have hq : (q : ℝ) ≤ sqrt (2 * h7.m * h7.n q) := by
    refine (le_sqrt (by positivity) (by positivity)).2 ?_
    exact_mod_cast h7.sq_le_two_mn q h2mq
  simpa [mul_assoc, sqrt_mul] using hq

include h2mq in
lemma q_le_two_mn : q ≤ 2 * h7.m * h7.n q :=
  le_trans (Nat.le_pow (Nat.zero_lt_two)) ((by simpa using le_of_eq (h7.q_eq_2sqrtmn q h2mq)))

include h2mq hq0 in
lemma fracmqn : ((h7.m : ℝ) * (h7.n q : ℝ) / (2 * (h7.m : ℝ) * (h7.n q : ℝ) -
    (h7.m * (h7.n q : ℝ))) : ℝ) = 1 := by
  have : 2 * (h7.m : ℝ) * (h7.n q : ℝ) - (h7.m : ℝ) * (h7.n q : ℝ) =
     ↑(h7.m : ℝ) * ↑(h7.n q : ℝ ) := by ring
  rw [this]
  norm_cast
  refine (div_eq_one_iff_eq ?_).mpr rfl
  simp only [Nat.cast_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Nat.zero_ne_add_one (2 * h7.h + 1)), h7.n_neq_zero q hq0 h2mq⟩

include hq0 h2mq in
lemma hfrac : (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2) = (h7.n q : ℝ) ^
    (((h7.n q : ℝ) + 1) / 2) := by
  nth_rw 1 [← rpow_one (x := ↑(h7.n q))]
  rw [← rpow_add]
  · congr; ring
  · norm_cast
    grind [h7.one_le_n q hq0 h2mq]

lemma c_coeffspow' : ((h7.c₁ : ℤ) ^ (h7.n q - 1) * (h7.c₁ : ℤ) ^ (h7.m * q) * (h7.c₁ : ℤ) ^
    (h7.m * q)) = ((h7.c₁ : ℤ) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : ℤ) ^
    (h7.m * q - a q t * h7.l q u) * (h7.c₁ : ℤ) ^ (h7.m * q - b q t * h7.l q u)) • ((h7.c₁ : ℤ) ^
    h7.k q u * (h7.c₁ : ℤ) ^  (a q t * h7.l q u) * (h7.c₁ : ℤ) ^ (b q t * h7.l q u)) := by
  have hpow (A B : ℕ) (h : B ≤ A) :
      (h7.c₁ : ℤ) ^ A = (h7.c₁ : ℤ) ^ (A - B) * (h7.c₁ : ℤ) ^ B := by
    simpa [Nat.sub_add_cancel h] using (pow_add (h7.c₁ : ℤ) (A - B) B)
  have hpowA := hpow (A := h7.m * q) (B := a q t * h7.l q u)
    (by simpa [Nat.mul_comm] using mul_le_mul (a_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _))
  have hpowB := hpow (A := h7.m * q) (B := b q t * h7.l q u) (by
    simpa [Nat.mul_comm] using mul_le_mul (b_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _))
  rw [hpow (A := h7.n q - 1) (B := h7.k q u)
    (Nat.le_pred_of_lt ((finProdFinEquiv.symm.toFun u).2.isLt)), hpowA]
  simp
  grind

include h2mq hq0 in
lemma foo : |↑q| ^ (h7.n q - 1) * ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^ (h7.m * (2 *
    (h7.m * h7.n q))) * house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) ≤ (1 + house h7.β') ^ h7.n q
    * (√(2 * ↑h7.m) ^ h7.n q * (max 1 (house h7.α' ^ (2 * h7.m ^ 2) * house h7.γ' ^ (2 * h7.m ^ 2))
    ^ h7.n q * √↑(h7.n q) ^ (↑(h7.n q : ℝ) - 1))) := by
        calc _ ≤ (sqrt (2 * h7.m) ^ (h7.n q -1))* (sqrt (h7.n q)) ^ ((h7.n q) -1) *
                 ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                 house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) := ?_
             _ ≤ (sqrt (2 * h7.m) ^ (h7.n q -1)) * ((1 + house h7.β') ^ (h7.n q - 1) *
                 (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^
                 (h7.m * (2 * (h7.m * h7.n q))))) * sqrt (h7.n q) ^ (((h7.n q) : ℝ) - 1) := ?_
             _ ≤ √(2 * ↑(h7.m)) ^ (h7.n q - 1) * ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^
                 (h7.m * 2 * h7.m * h7.n q) * house h7.γ' ^ (h7.m * 2 * h7.m * h7.n q))) *
                 (sqrt (h7.n q)) ^ (((h7.n q) : ℝ) -1) := ?_
             _ ≤ √(2 * ↑(h7.m)) ^ ((h7.n q)) * ((1 + house h7.β') ^ ((h7.n q)) * (house h7.α' ^
                 (h7.m * 2 * h7.m)) ^ (h7.n q) * (house h7.γ' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)) *
                 (sqrt (h7.n q )) ^ (((h7.n q) : ℝ)-1) := ?_
        · apply mul_le_mul (by simpa using (h7.q_eq_n_etc q h2mq)) (by rfl) (by positivity)
            (by positivity)
        · have hsqrt : (sqrt (h7.n q) ^ (h7.n q - 1)) = (sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1)) := by
            simpa [(Nat.cast_sub (h7.one_le_n q hq0 h2mq))] using
            (rpow_natCast (x := sqrt (h7.n q)) (n := h7.n q - 1)).symm
          refine le_of_eq ?_
          simp [hsqrt]
          ac_rfl
        · simp [mul_assoc]
        · simp only [mul_assoc]
          apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ?_)
            refine ⟨?_, by simp⟩
            have hm1 : (1 : ℝ) ≤ (h7.m : ℝ) := by exact_mod_cast h7.one_le_m
            have : (1 : ℝ) ≤ (2 : ℝ) * (h7.m : ℝ) := by nlinarith
            simpa [Nat.cast_mul, Nat.cast_ofNat] using (one_le_sqrt).2 this
          · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ?_)
              refine ⟨?_, Nat.sub_le _ _⟩
              simp [le_add_iff_nonneg_right]
            · apply mul_le_mul (by simp [pow_mul]) (by simp [pow_mul]) (by positivity)
                (pow_nonneg (pow_nonneg (house_nonneg _) _) _)
        · nth_rw 2 [← mul_assoc]
          rw [mul_comm  ((1 + house h7.β') ^ (h7.n q)) (((sqrt ((2*h7.m)))) ^ (h7.n q))]
          simp only [mul_assoc]
          apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · refine pow_le_pow_left₀ (sqrt_nonneg _) (by rfl) (h7.n q)
          · apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
            · simp only [← mul_assoc]
              apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
              · rw [← mul_pow]
                refine pow_le_pow_left₀ (by positivity) ?_ (h7.n q)
                · have : ((h7.m * 2) * h7.m) = (2 * h7.m^2) := by
                    rw [mul_comm, ← mul_assoc, pow_two, mul_comm]
                  rw [this]; clear this
                  calc _ ≤ ((house h7.α' ^ (2 * h7.m ^ 2) * house h7.γ' ^ (2 * h7.m ^ 2))) := ?_
                       _ ≤ max 1 ((house h7.α' ^ (2 * h7.m^ 2) *
                           house h7.γ' ^ (2 * h7.m ^ 2))) := ?_
                  · apply Preorder.le_refl
                  · simp only [le_sup_right]

/-! Moreover, the absolute value of the conjugates of the various coefficients is at most
  `c₂^n (q + q * |β|)^(n - 1) * |α|^(m q) * |γ|^(m q) ≤ c₃^n * n^((n - 1) / 2)`.
-/
include hq0 h2mq in
lemma hAkl : house ((algebraMap (𝓞 h7.K) h7.K) ((h7.A q) hq0 h2mq u t)) ≤
      (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))  := by
    simp only [A, sys_coe, RingOfIntegers.restrict, RingOfIntegers.map_mk]
    calc _ = house ((h7.c₁ ^ ((h7.n q - 1) - h7.k q u) * h7.c₁ ^ (h7.m * q - a q t * h7.l q u) *
             (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u)) • (((h7.c₁ : h7.K) ^ h7.k q u) *
             ((a q t : h7.K) + (b q t) * h7.β') ^ h7.k q u * ((h7.c₁ : h7.K) ^ (a q t * h7.l q u)) *
             h7.α' ^ (a q t * h7.l q u) * ((h7.c₁ : h7.K) ^ (b q t * h7.l q u)) *
             h7.γ' ^ (b q t * h7.l q u))) := ?_
         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
             (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
             house (h7.c₁ ^ (h7.k q u) • (↑(a q t) + (b q t) • h7.β') ^ (h7.k q u)) *
             house (h7.c₁ ^ (a q t * h7.l q u) • h7.α' ^ (a q t * h7.l q u)) *
             house (h7.c₁ ^ (b q t * h7.l q u) • h7.γ' ^ (b q t * h7.l q u)) := ?_
         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
             (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
             house (h7.c₁ • (↑(a q t) + (b q t) • h7.β')) ^ (h7.k q u) * house (h7.c₁ • h7.α') ^
             (a q t * h7.l q u) * house (h7.c₁ • h7.γ') ^ (b q t * h7.l q u) := ?_
         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
             (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
             house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ^ (h7.n q - 1) *
             house (h7.c₁ • h7.α') ^ (h7.m * q) * house (h7.c₁ • h7.γ') ^ (h7.m * q) := ?_
         _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
             (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * (|h7.c₁| *
             (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.n q - 1) * (|h7.c₁| * house (h7.α')) ^
             (h7.m * (2 * (h7.m * h7.n q))) * (|h7.c₁| * house (h7.γ')) ^
             (h7.m * (2 * (h7.m * h7.n q))) := ?_
         _ = |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
             (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * |h7.c₁ ^ (h7.n q - 1)| •
             (↑|↑q| * (1 + house h7.β')) ^ (h7.n q - 1) * |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
             house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))|
             • house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
         _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
             (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * ↑|h7.c₁| ^ ((h7.n q - 1) +
             (2 * h7.m * (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^
             (h7.n q - 1) * house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
             house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ = |(h7.c₁) ^ (h7.n q - 1 - h7.k q u)| * |(h7.c₁) ^ (h7.m * q - a q t * h7.l q u)| *
             |(h7.c₁) ^ (h7.m * q - b q t * h7.l q u)| * ↑|h7.c₁| ^ ((h7.n q - 1) +
             (2 * h7.m * (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q)- 1) *
             (1 + house h7.β') ^ (h7.n q - 1) * house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
             house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ = |(h7.c₁)| ^ (h7.n q - 1 - h7.k q u) * |(h7.c₁)| ^ (h7.m * q - a q t * h7.l q u) *
             |(h7.c₁)| ^ (h7.m * q - b q t * h7.l q u) * ↑|h7.c₁| ^ ((h7.n q - 1) +  (2 * h7.m *
             (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
             house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
             house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ ≤ ↑(h7.c₂) ^ (h7.n q) * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
             house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
             house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ ≤ (h7.c₃)^(h7.n q : ℝ) * ((sqrt (h7.n q))^((h7.n q : ℝ)- 1)) := ?_
         _ ≤ (h7.c₃ ^ (h7.n q: ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)) := ?_
    · rw [c_coeffs, h7.c_coeffspow' q u t, smul_assoc]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a * b) * c) • ((x * y)* z) = a • x * b • y * c • z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      rw [triple_comm h7.K (h7.c₁^(h7.k q u)) (h7.c₁^(a q t * h7.l q u)) (h7.c₁^(b q t * h7.l q u))
          (((a q t) + b q t • h7.β')^(h7.k q u))
          (h7.α' ^ (a q t * h7.l q u)) (h7.γ' ^ (b q t * h7.l q u))]
      simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_mul, smul_eq_mul,mul_assoc]
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,mul_assoc]
      apply le_trans (house_mul_le _ _) (mul_le_mul (by rfl) ?_ (house_nonneg _) (house_nonneg _))
      · rw [← mul_assoc,← mul_assoc,← mul_assoc]
        apply le_trans (house_mul_le _ _)
        rw [← mul_assoc]
        apply mul_le_mul ?_ (by rfl) (house_nonneg _) (mul_nonneg (house_nonneg _) (house_nonneg _))
        · rw [mul_assoc]; apply house_mul_le
    · simp only [mul_assoc]
      apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
      · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, ← mul_pow]
        apply mul_le_mul (house_pow_le _ _) ?_ (by positivity) (by positivity)
        · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
            (pow_nonneg (house_nonneg _) _)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · apply mul_le_mul (by rfl) ?_ (by positivity) (house_nonneg _)
          · apply Bound.pow_le_pow_right_of_le_one_or_one_le
              (Or.inl ⟨one_le_house_of_isIntegral (isInt_β_bound_low _ _ _) ?_, ?_⟩)
            · intros H
              simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H
              cases H with
              | inl hp => apply h7.c₁_ne_zero; exact hp
              | inr hq => apply h7.β'_neq_zero q t 1; rw [pow_one]; exact hq
            · refine (Nat.le_sub_iff_add_le' (h7.one_le_n q hq0 h2mq)).mpr ?_
              · rw [add_comm]; exact (finProdFinEquiv.symm.toFun u).2.isLt
        · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁α h7.c₁αneq0, ?_⟩)
          · rw [mul_comm h7.m q]
            apply mul_le_mul (a_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _)
      · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁γ h7.c₁cneq0, ?_⟩)
        · rw [mul_comm h7.m q]
          apply (mul_le_mul (b_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _))
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · rw [← house_intCast (K := h7.K)]; simp
          · refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.n q - 1)
            · rw [← mul_assoc]; apply h7.house_add_mul_le q t
        · calc _ ≤ house (h7.c₁ • h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
               _ ≤ (↑|h7.c₁| * house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
          · have house_alg_int_le_pow (α : h7.K) (n m : ℕ) (h : n ≤ m) (hα0 : α ≠ 0)
               (H : IsIntegral ℤ α) : house α ^ n ≤ house α ^ m :=
              Bound.pow_le_pow_right_of_le_one_or_one_le
              (Or.inl ⟨one_le_house_of_isIntegral H hα0, h⟩)
            refine house_alg_int_le_pow (h7.c₁ • h7.α') (h7.m * q) (h7.m * (2 * (h7.m * h7.n q)))
              ?_ h7.c₁αneq0 h7.isIntegral_c₁α
            · apply mul_le_mul (by rfl) ?_ (by simp) (by simp)
              · exact (by have H := h7.q_le_two_mn q h2mq; rw [mul_assoc] at H; exact H )
          · refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.m * (2 * (h7.m * h7.n q)))
            · calc _ ≤ house (h7.c₁ : h7.K) * house (h7.α') := ?_
                   _ ≤ _ := ?_
              · simp only [zsmul_eq_mul]; apply house_mul_le
              · simp
      · calc _ ≤ house (h7.c₁ • h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
             _ ≤ (↑|h7.c₁| * house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
        · have house_alg_int_le_pow (α : h7.K) (n m : ℕ) (h : n ≤ m) (hα0 : α ≠ 0)
             (H : IsIntegral ℤ α) : house α ^ n ≤ house α ^ m :=
            Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral H hα0, h⟩)
          refine house_alg_int_le_pow (h7.c₁ • h7.γ') (h7.m * q)
            (h7.m * (2 * (h7.m * h7.n q))) ?_ h7.c₁cneq0 h7.isIntegral_c₁γ
          · apply mul_le_mul (by rfl) (by grind [h7.q_le_two_mn q h2mq]) (by simp) (by simp)
        refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.m * (2 * (h7.m * h7.n q)))
        · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.γ') := ?_
               _ ≤ _ := ?_
          · simp only [zsmul_eq_mul]; apply house_mul_le
          · simp only [house_intCast, Int.cast_abs, le_refl]
    · rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
         abs_pow, abs_pow]; congr; all_goals simp
    · have triple_comm {K : Type} [Field K] (a b c : ℤ) (x y z : K) : ((a * b) * c) • ((x * y) * z)
         = a • x * b • y * c • z := by grind
      have := triple_comm |(h7.c₁ ^ (h7.n q - 1) : ℤ)|
         |(h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q))) : ℤ)|
         |(h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q))) : ℤ)|
         ((↑|↑q| * (1 + house (h7.β'))) ^ (h7.n q - 1))
         ((house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))))
         ((house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))))
      simp only [mul_assoc, zsmul_eq_mul] at *
      rw [← this, abs_pow, abs_pow, ← pow_add, ← pow_add]
      apply mul_le_mul (by simp) ?_ (by positivity) (by positivity)
      · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · rw [← pow_add, ← pow_add, Eq.symm (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
          simp only [Int.cast_pow, Int.cast_abs, le_refl]
        · rw [mul_pow]; simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
    · simp only [← pow_add, ← pow_add, Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow,
        ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    · rw [abs_pow, abs_pow, abs_pow]; simp
    · apply mul_le_mul ?_ ?_ (by positivity) ?_
      · rw [← pow_add, ← pow_add, ← pow_add, Int.cast_abs,
          c₂, Int.cast_pow, Int.cast_abs, ← pow_mul]
        refine pow_le_pow_right₀ (mod_cast h7.one_le_abs_c₁) ?_
        · simp only [add_mul, add_mul, one_mul, mul_assoc, (Nat.two_mul
            (h7.m * (2 * (h7.m * h7.n q)))), add_assoc]
          refine Nat.add_le_add ?_ (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
            simpa [mul_assoc] using Nat.mul_le_mul_left h7.m (h7.q_le_two_mn q h2mq))
              (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
            simpa [mul_assoc] using Nat.mul_le_mul_left h7.m (h7.q_le_two_mn q h2mq)) (by simp)))
          · grind
      · simp only [Nat.abs_cast, le_refl]
      · apply pow_nonneg; exact mod_cast (le_trans Int.one_nonneg (h7.one_le_c₂))
    · simp_rw [h7.c₃_pow q, mul_assoc]
      apply mul_le_mul (by rfl) (h7.foo q hq0 h2mq) (by positivity) ?_
      · apply pow_nonneg; norm_cast; apply le_trans Int.one_nonneg (h7.one_le_c₂)
    · rw [le_iff_eq_or_lt]; left;
      have : sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1) = (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2) := by
        nth_rw 1 [sqrt_eq_rpow, ← rpow_mul, mul_comm, mul_div]
        · simp only [mul_one]
        · simp only [Nat.cast_nonneg]
      rw [← this]

variable [DecidableEq (h7.K →+* ℂ)]

abbrev η : Fin (q * q) → 𝓞 h7.K :=
  (NumberField.house.exists_ne_zero_int_vec_house_le h7.K (h7.A q hq0 h2mq)
  (h7.hM_ne_zero q hq0 h2mq) (h7.h0m q hq0 h2mq) (h7.hmn q hq0 h2mq) (Fintype.card_fin _)
  (fun u t ↦ h7.hAkl q hq0 u t h2mq) (Fintype.card_fin _)).choose

def c₄ : ℝ := (max 1 ((house.c₁ h7.K) * house.c₁ h7.K * 2 * h7.m)) * h7.c₃

lemma one_le_c₄ : 1 ≤ h7.c₄ := by
  refine one_le_mul_of_one_le_of_one_le
    (le_max_left 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m))) (h7.one_le_c₃)

lemma zero_le_c₄ : 0 ≤ h7.c₄ := by
  simp only [c₄, lt_sup_iff, zero_lt_one, true_or, mul_nonneg_iff_of_pos_left]
  exact le_trans zero_le_one (h7.one_le_c₃)

lemma one_le_house_c₁ : 1 ≤ house.c₁ h7.K := one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr
  (Module.finrank_pos)) (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))

/-!
It follows from lemma 8.2 that there is a non-trivial set of integer solutions `η₁, …, η₂` in `K`
such that `‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/
open NumberField.house in
lemma fromlemma82_bound : house (algebraMap (𝓞 h7.K) h7.K (h7.η q hq0 h2mq t)) ≤
    h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1)/2)) := by
  calc _ ≤ house.c₁ h7.K * (house.c₁ h7.K * ↑(q * q) *
           (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))) ^
           ((h7.m * h7.n q : ℝ) / (↑(q * q : ℝ) - ↑(h7.m * h7.n q ))) := ?_
       _ = (house.c₁ h7.K * (house.c₁ h7.K * 2 * h7.m * (h7.c₃ ^ (h7.n q : ℝ)) * ((h7.n q : ℝ) *
           (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)))) := ?_
       _ ≤ h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) : ℝ) := ?_
  · exact mod_cast ((NumberField.house.exists_ne_zero_int_vec_house_le
    h7.K (h7.A q hq0 h2mq) (h7.hM_ne_zero q hq0 h2mq) (h7.h0m q hq0 h2mq) (h7.hmn q hq0 h2mq)
    (Fintype.card_fin _) (fun u t ↦ h7.hAkl q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec).2.2 t
  · have : (q * q : ℝ) = q^2 := mod_cast (pow_two ↑q).symm
    rw [← pow_two q, this, h7.q_eq_2sqrtmn q h2mq]
    have : (q ^ 2 : ℝ) = 2 * h7.m * h7.n q := mod_cast (h7.q_eq_2sqrtmn q h2mq)
    rw [this]
    have fracmqn := h7.fracmqn q hq0 h2mq
    nth_rw 2 [← Nat.cast_mul] at fracmqn
    rw [fracmqn, rpow_one, h7.hfrac q hq0 h2mq, mul_eq_mul_left_iff]; left
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    refine (mul_right_inj' (by grind [h7.one_le_house_c₁])).mpr ?_
    · grind [h7.hfrac q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  · rw [h7.hfrac q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · rw [c₄]
      rw [mul_rpow (le_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
         (le_of_lt (lt_of_lt_of_le (by norm_num) h7.one_le_c₃))]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · have hn : (1 : ℝ) ≤ (h7.n q : ℝ) := mod_cast h7.one_le_n q hq0 h2mq
        have hpow :
        (max 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑h7.m) : ℝ) ≤
          (max 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑h7.m)) ^ (h7.n q : ℝ) := by
          simpa [Real.rpow_one] using
        (rpow_le_rpow_of_exponent_le (le_max_left (1 : ℝ) _) hn)
        exact (le_max_right (1 : ℝ) _).trans hpow
      · apply rpow_nonneg
        exact le_trans zero_le_one h7.one_le_c₃
    · apply rpow_nonneg; simp only [Nat.cast_nonneg]

end Setup
