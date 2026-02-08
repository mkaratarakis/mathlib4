/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
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

The structure of the proof is as follows:

* The argument proceeds by **contradiction**. The core of the proof is
  an **auxiliary function lemma**, where we construct a nonzero integer linear
  combination of exponential functions that vanishes to high order at several algebraic
  points.

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

lemma isNumberField_adjoin_alg_numbers (α β γ : ℂ)
  (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    NumberField (adjoin ℚ {α, β, γ}) :=  {
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin (fun x hx => by
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with ⟨ha, hb⟩; · simp_rw [isAlgebraic_iff_isIntegral.1 hα]
    rename_i hb
    rcases hb with ⟨hb,hc⟩; · simp_rw [isAlgebraic_iff_isIntegral.1 hβ]
    rename_i hc
    simp_rw [mem_singleton_iff.1 hc, isAlgebraic_iff_isIntegral.1 hγ]
    )}

lemma adjoin_simple_le_adjoin_insert (α β : ℂ) (_ : IsAlgebraic ℚ α) (_ : IsAlgebraic ℚ β) :
  (adjoin _ {α} ≤ adjoin ℚ {α, β}) ∧ (adjoin _ {β} ≤ adjoin ℚ {α, β}) :=
  ⟨by apply adjoin.mono; intros x hx; left; exact hx,
   by apply adjoin.mono; intros x hx; right; exact hx⟩

lemma exists_common_field_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ)
    (_ : DecidableEq (K →+* ℂ)), ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have  hab := adjoin.mono ℚ {α, β} {α, β, γ}
    fun x hxab => by
      rcases hxab with ⟨hxa, hxb⟩
      ·  left;
         simp only
      rename_i h
      simp only [mem_singleton_iff] at h
      subst h
      simp_all only [mem_insert_iff, mem_singleton_iff, true_or, or_true]
  have hac := adjoin.mono ℚ {α, γ} {α, β, γ}
    fun x hx => by
    rcases hx with ⟨hsf, hff⟩;
    · left; rfl ;
    · rename_i h; aesop;
  use adjoin ℚ {α, β, γ}
  constructor
  use isNumberField_adjoin_alg_numbers α β γ hα hβ hγ
  use { toFun := fun x => x.1, map_one' := rfl, map_mul' := fun x y => rfl
        map_zero' := rfl, map_add' := fun x y => rfl}
  use Classical.typeDecidableEq (↥ℚ⟮α, β, γ⟯ →+* ℂ)
  simp only [exists_and_left, exists_and_right, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.exists, exists_prop, exists_eq_right']
  exact ⟨adjoin_simple_le_iff.1 fun _ hx =>
     hab ((adjoin_simple_le_adjoin_insert  α β hα hβ).1 hx),
    adjoin_simple_le_iff.1 fun _ hx =>  hab (by
    apply adjoin.mono; intros x hx;
    · right; exact hx;
    · exact hx),
    adjoin_simple_le_iff.1 fun _ hx =>
    hac ((adjoin_simple_le_adjoin_insert α γ hα hγ).2 hx)⟩

variable {K} [Field K] [NumberField K]

lemma exists_int_smul_isIntegral {K : Type*} [Field K] [NumberField K] (α : K) :
  ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

/--
A choice of a non-zero integer `c₀` such that `c₀ • α` is an algebraic integer.
-/
def c₀ {K : Type*} [Field K] [NumberField K] (α : K) :
  {c : ℤ // c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(exists_int_smul_isIntegral α).choose, (exists_int_smul_isIntegral α).choose_spec⟩

/-- A choice of a non-zero integer `c₀` such that `c • α` is an algebraic integer.
See `c₀`. -/
abbrev c₀Coeff {K : Type*} [Field K] [NumberField K] (α : K) : ℤ :=
  (c₀ α : ℤ)

lemma c₀Coeff_ne_zero (α : K) : c₀Coeff α ≠ 0 :=
  (c₀ α).2.1


/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational.
We prove that `αᵇ` is transcendental by contradiction.
Suppose `γ = αᵇ = e^(β log α)` is also algebraic.
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
  fun H => h7.htriv.1 ((cpow_eq_zero_iff h7.α h7.β).mp H).1

lemma beta_ne_zero : h7.β ≠ 0 :=
  fun H => h7.hirr 0 1 (by simpa [div_one] using H)

lemma alpha'_beta'_gamma'_ne_zero : h7.α' ≠ 0 ∧ h7.β' ≠ 0 ∧ h7.γ' ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro H
  · exact h7.htriv.1 (by simp [h7.habc.1, H, RingHom.map_zero h7.σ])
  · exact h7.beta_ne_zero (by simp [h7.habc.2.1, H, RingHom.map_zero h7.σ])
  · exact h7.alpha_cpow_beta_ne_zero (by simp [h7.habc.2.2, H, RingHom.map_zero h7.σ])

lemma alpha'_ne_one : h7.α' ≠ 1 :=
  fun h => h7.htriv.2 <| by simpa [h7.habc.1, map_one] using congrArg h7.σ h

lemma beta'_ne_zero : h7.β' ≠ 0 := h7.alpha'_beta'_gamma'_ne_zero.2.1

open Complex

lemma log_zero_zero : log h7.α ≠ 0 :=
  mt (fun h => by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2

def c₁ : ℤ := abs (c₀ h7.α' * c₀ h7.β' * c₀ h7.γ')

lemma one_leq_c₁ : 1 ≤ h7.c₁ := by
  simpa [c₁] using
    Int.one_le_abs <|
  mul_ne_zero (mul_ne_zero (c₀Coeff_ne_zero h7.α') (c₀Coeff_ne_zero h7.β')) (c₀Coeff_ne_zero h7.γ')

lemma c₁_neq_zero : h7.c₁ ≠ 0 :=
  Ne.symm (Int.ne_of_lt h7.one_leq_c₁)

lemma one_leq_abs_c₁ : 1 ≤ |↑h7.c₁| := by
  refine Int.one_le_abs (Ne.symm (Int.ne_of_lt h7.one_leq_c₁))

lemma IsIntegral_assoc (K : Type) [Field K]
  {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
  IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  simpa [Int.cast_mul, zsmul_eq_mul, mul_assoc] using IsIntegral.smul (x * y) ha

lemma isIntegral_c₁α : IsIntegral ℤ (h7.c₁ • h7.α') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.α') h7.α'
    ((c₀ h7.α').2.2)
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (c₀Coeff h7.α') (c₀Coeff h7.β'), ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.β' * c₀Coeff h7.α')
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (h7.c₁ • h7.β') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ')
     (y := c₀Coeff h7.α') h7.K (c₀Coeff h7.β') h7.β'
    ((c₀ h7.β').2.2)
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.α' * c₀Coeff h7.β')
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (h7.c₁ • h7.γ') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.α') (y := c₀Coeff h7.β')
    h7.K (c₀Coeff h7.γ') h7.γ' ((c₀ h7.γ').2.2)
  rw [c₁]
  rcases abs_choice (c₀Coeff h7.α' * c₀Coeff h7.β' * c₀Coeff h7.γ')
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

def h : ℕ := Module.finrank ℚ h7.K

def m : ℕ := 2 * h7.h + 2

lemma one_le_m : 1 ≤ h7.m :=
  Nat.succ_le_succ (Nat.zero_le (2 * h7.h + 1))

-- `q` is a parameter, so it remains an argument.
def n (q : ℕ) : ℕ := q ^ 2 / (2 * h7.m)

-- These are parameters for the auxiliary function construction.
variable (q : ℕ) (hq0 : 0 < q)
variable (u : Fin (h7.m * h7.n q))
variable (t : Fin (q * q))

-- `a, b, k, l` are values that depend on the context variables `t` and `u`.
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1
def k : ℕ := (finProdFinEquiv.symm.toFun u).2
def l : ℕ := (finProdFinEquiv.symm.toFun u).1 + 1

lemma b_le_q : b q t ≤ q :=
  ((finProdFinEquiv.symm.toFun t).2).isLt

lemma l_le_m : h7.l q u ≤ h7.m :=
  ((finProdFinEquiv.symm.toFun u).1).isLt

lemma a_le_q : a q t ≤ q :=
  ((finProdFinEquiv.symm.toFun t).1).isLt

lemma k_le_n_sub1 : (h7.k q u : ℤ) ≤ (h7.n q - 1 : ℤ) := by
  rw [sub_eq_add_neg]
  have : (k h7 q u : ℤ) + 1 ≤ ↑(h7.n q) → (h7.k q u : ℤ) ≤ ↑(h7.n q) + -1 := by
    simp only [Int.reduceNeg, le_add_neg_iff_add_le, imp_self]
  apply this
  norm_cast
  exact ((finProdFinEquiv.symm.toFun u).2).isLt

lemma al_leq_mq : a q t * h7.l q u ≤ q * h7.m := by
  apply mul_le_mul (a_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _)

lemma bl_leq_mq : b q t * h7.l q u ≤ q * h7.m := by
  apply mul_le_mul (b_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _)

lemma k_le_n : k h7 q u  ≤ h7.n q := Fin.is_le'

abbrev c_coeffs0 (q : ℕ)
(u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :=
  h7.c₁^(h7.k q u : ℕ) * h7.c₁^ (a q t * h7.l q u) * h7.c₁^(b q t * h7.l q u)

lemma IsIntegral.Cast (K : Type) [Field K] (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma c₁ac (u : h7.K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑h7.c₁ * u)) :
    IsIntegral ℤ (h7.c₁ ^ (n * k) • u ^ (a *l)) := by
  have : h7.c₁ ^ (n * k) = h7.c₁ ^ (n * k - a * l) * h7.c₁ ^ (a *l) := by
    rw [← pow_add]; rwa [Nat.sub_add_cancel]
  rw [this, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow]; rw [mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow (IsIntegral.Cast h7.K h7.c₁) _
  rw [← mul_pow]; exact IsIntegral.pow H _

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma c₁b (n : ℕ) :
    1 ≤ n → (k : ℕ) → k ≤ n - 1 → (a : ℕ) → 1 ≤ a → (b : ℕ) → 1 ≤ b →
    IsIntegral ℤ (h7.c₁ ^ (n - 1) • (↑a + ↑b • h7.β') ^ k) := by
  intros hn k hkn a ha b hb
  have : h7.c₁^(n - 1) = h7.c₁^(n - 1 - k) * h7.c₁^k := by
    rwa [← pow_add, Nat.sub_add_cancel]
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow (IsIntegral.Cast _ _) _
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

open Nat in include hq0 in omit hq0 in
lemma c1a0 :
 IsIntegral ℤ (h7.c₁ ^ (a q t * h7.l q u) • (h7.α' ^ (a q t * h7.l q u : ℕ))) := by
  apply h7.c₁ac h7.α' (a q t) (h7.l q u) (a q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α

open Nat in include hq0 in omit hq0 in
lemma c1c0 :
    IsIntegral ℤ (h7.c₁ ^ (b q t * h7.l q u) • (h7.γ'^ (b q t * (h7.l q u) : ℕ))) := by
  apply h7.c₁ac h7.γ' (b q t) (h7.l q u) (b q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

open Nat in include hq0 in
lemma c1a :
 IsIntegral ℤ (h7.c₁^(h7.m * q) • (h7.α' ^ (a q t * h7.l q u : ℕ))) := by
  apply h7.c₁ac h7.α' (h7.m) q (a q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
      (add_le_of_le_sub hq0 (le_sub_one_of_lt ((finProdFinEquiv.symm.1 t).1).isLt))
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α

open Nat in include hq0 in
lemma c1c : IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.γ'^ (b q t * h7.l q u : ℕ))) := by
  apply h7.c₁ac h7.γ' (h7.m) q (b q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
        (add_le_of_le_sub hq0 (le_sub_one_of_lt
        (finProdFinEquiv.symm.1 t).2.isLt))
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

abbrev sys_coe : h7.K := (a q t + b q t • h7.β')^(h7.k q u) *
h7.α' ^(a q t * h7.l q u) * h7.γ' ^((b q t) * h7.l q u)

variable (h2mq : 2 * h7.m ∣ q ^ 2)

include h2mq in
lemma q_eq_2sqrtmn : q^2 = 2*h7.m*h7.n q := Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq in
lemma q_eq_sqrtmn : q = Real.sqrt (2*h7.m*h7.n q) := by
  norm_cast
  rw [← q_eq_2sqrtmn h7 q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, Real.sqrt_sq]

include hq0 h2mq in
lemma card_mn_pos : 0 < h7.m * h7.n q := by
  simp only [CanonicallyOrderedAdd.mul_pos]
  refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), ?_⟩
  · dsimp [n]
    simp only [Nat.div_pos_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (by positivity) h2mq⟩

include hq0 h2mq in
lemma one_le_n : 1 ≤ h7.n q := by
  rw [n, Nat.one_le_div_iff]
  · apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq
  · exact Nat.zero_lt_succ (Nat.mul 2 (2 * h7.h + 1) + 1)

include hq0 h2mq in
lemma n_neq_0 : h7.n q ≠ 0 := Nat.ne_zero_of_lt (one_le_n h7 q hq0 h2mq)

include hq0 h2mq in
lemma qsqrt_leq_2m : 2 * h7.m ≤ q^2 := Nat.le_of_dvd (Nat.pow_pos hq0) h2mq

lemma hm : 0 < h7.m := Nat.zero_lt_succ (2 * h7.h + 1)

include hq0 h2mq in
lemma h0m : 0 < h7.m * h7.n q :=
  mul_pos (h7.hm) (one_le_n h7 q hq0 h2mq)

include hq0 h2mq in
lemma hmn : h7.m * h7.n q < q*q := by
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  rw [← pow_two q, ← mul_lt_mul_iff_right₀ (Nat.zero_lt_two)]
  rw [← mul_assoc, n, h2mq, lt_mul_iff_one_lt_left]
  · exact one_lt_two
  · exact Nat.pow_pos hq0

include h2mq in
lemma sq_le_two_mn : q^2 ≤ 2 * h7.m * h7.n q := by
  dsimp only [n]
  refine Nat.le_sqrt'.mp ?_
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  refine Nat.le_sqrt'.mpr ?_
  nth_rw 1 [← h2mq]

abbrev c_coeffs (q : ℕ) := h7.c₁^(h7.n q - 1) * h7.c₁^(h7.m * q) * h7.c₁^(h7.m * q)

open Nat in include hq0 h2mq in
lemma c₁IsInt (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :
  IsIntegral ℤ (h7.c_coeffs q • h7.sys_coe q u t) := by
  unfold c_coeffs
  unfold sys_coe
  have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
   ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
     simp only [zsmul_eq_mul, Int.cast_mul]; ring
  rw [triple_comm h7.K
    (h7.c₁^(h7.n q - 1) : ℤ)
    (h7.c₁^(h7.m * q) : ℤ)
    (h7.c₁^(h7.m * q) : ℤ)
    (((a q t : ℕ) + b q t • h7.β')^(h7.k q u : ℕ))
    (h7.α' ^ (a q t * h7.l q u))
    (h7.γ' ^ (b q t * h7.l q u))]
  rw [mul_assoc]
  apply IsIntegral.mul
  · exact h7.c₁b (h7.n q) (one_le_n h7 q hq0 h2mq)
      (h7.k q u) (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt)
      (a q t) (le_add_left 1 (finProdFinEquiv.symm.1 t).1)
      (b q t) (le_add_left 1 (finProdFinEquiv.symm.1 t).2)
  · exact IsIntegral.mul (c1a h7 q hq0 u t) (c1c h7 q hq0 u t)

lemma c₁neq0 : h7.c₁ ≠ 0 := by
  unfold c₁
  unfold c₀
  intros H
  simp_all only [ne_eq, abs_eq_zero, mul_eq_zero]
  grind

lemma c₁αneq0 : h7.c₁ • h7.α' ≠ 0 := by
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨h7.c₁neq0, (h7.alpha'_beta'_gamma'_ne_zero).1⟩

lemma c₁cneq0 : h7.c₁ • h7.γ' ≠ 0 := by
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨h7.c₁neq0, (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

lemma c_coeffs_neq_zero : h7.c_coeffs q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (h7.c₁neq0))
  (pow_ne_zero _ (h7.c₁neq0))) (pow_ne_zero _ (h7.c₁neq0))

def A : Matrix (Fin (h7.m * h7.n q)) (Fin (q * q)) (𝓞 h7.K) :=
  fun i j => RingOfIntegers.restrict _ (fun _ => (c₁IsInt h7 q hq0 h2mq i j)) ℤ

lemma α'_neq_zero : h7.α' ^ (a q t * h7.l q u) ≠ 0 :=
  pow_ne_zero _ (h7.alpha'_beta'_gamma'_ne_zero).1

lemma γ'_neq_zero : h7.γ' ^ (b q t * h7.l q u) ≠ 0 :=
  pow_ne_zero _ (h7.alpha'_beta'_gamma'_ne_zero).2.2

lemma β'_neq_zero (y : ℕ) : (↑↑(a q t) + (↑(b q t)) • h7.β') ^ y ≠ 0 := by
  apply pow_ne_zero
  intro H
  have H1 : h7.β' = (↑↑(a q t))/(-(↑(b q t))) := by
    rw [eq_div_iff_mul_eq]
    · rw [← eq_neg_iff_add_eq_zero] at H
      rw [mul_neg, mul_comm, H]
      have : (↑↑(b q t)) ≠ 0 := by
        simp only [ne_eq]
        unfold b
        simp only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_modNat,
          AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
      unfold b
      simp only [Equiv.toFun_as_coe, nsmul_eq_mul]
    intros H
    norm_cast at H
    have : b q t ≠ 0 := by unfold b; aesop
    apply this
    exact H.1
  apply h7.hirr (↑(a q t)) (-(↑(b q t)))
  rw [h7.habc.2.1, H1]
  simp only [map_div₀, map_natCast, map_neg, Int.cast_natCast, Int.cast_neg]

lemma sum_b
   (i1 i2 j1 j2 : ℕ) (Heq : ¬i2 = j2) : i1 + i2 • h7.β ≠ j1 + j2 • h7.β := by
      intros H
      have hb := h7.hirr (i1 - j1) (j2 - i2)
      apply (h7.hirr (i1 - j1) (j2 - i2))
      have h1 : i1 + i2 • h7.β = j1 + j2 • h7.β  ↔
        (i1 + i2 • h7.β) - (j1 + j2 • h7.β) = 0 :=
          (sub_eq_zero (a := (i1 + i2 • h7.β : ℂ)) (b := (j1 + j2 • h7.β : ℂ))).symm
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • h7.β - (↑j1 + ↑j2 • h7.β) = 0 ↔
         ↑i1 + i2 • h7.β - ↑j1 - ↑j2 • h7.β = 0 := by
          simp_all only [ne_eq, Int.cast_sub, nsmul_eq_mul,
            iff_true, sub_self, add_sub_cancel_left]
      rw [h2] at H
      have h3 : ↑i1 + i2 • h7.β - ↑j1 - j2 • h7.β = 0 ↔
          ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 := by
        ring_nf
      rw [h3] at H
      have h4 : ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 := by
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul, add_assoc, ← add_mul, smul_eq_mul, ← sub_eq_add_neg]
      rw [h4] at H
      rw [add_eq_zero_iff_eq_neg] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) ↔
          ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β := by
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul, neg_sub]
      rw [h6] at H
      have h7 :
          (↑i1 - ↑j1 : ℂ) = (↑j2 - ↑i2 : ℂ) • h7.β ↔
        (↑i1 - ↑j1) / (↑j2 - ↑i2 : ℂ) = h7.β := by
        simpa [smul_eq_mul, mul_comm] using
          (div_eq_iff (sub_ne_zero.2 (mod_cast (by intro h; exact Heq h.symm)))).symm
      rw [h7] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast]

include hq0 in
lemma b_sum_neq_0 : (↑q : h7.K) + q • h7.β' ≠ 0 := by
  intro H
  have hqC : (q : ℂ) ≠ 0 := mod_cast (Nat.ne_zero_of_lt hq0)
  have hEq : (q : ℂ) + (q : ℂ) * h7.β = 0 := by
    simpa [nsmul_eq_mul, map_add, map_mul, map_natCast, ← h7.habc.2.1] using (congrArg h7.σ H)
  exact h7.hirr (-1) 1 (by simpa [div_one] using
    ((eq_neg_of_add_eq_zero_right ((mul_eq_zero.mp (by grind)).resolve_left (hqC)))))

lemma one_leq_house_c₁β : 1 ≤ house (h7.c₁ • h7.β') := by
  refine one_le_house_of_isIntegral h7.isIntegral_c₁β ?_
  have hc : ((h7.c₁ : ℤ) : h7.K) ≠ 0 := mod_cast h7.c₁neq0
  simpa [zsmul_eq_mul] using mul_ne_zero hc h7.alpha'_beta'_gamma'_ne_zero.2.1

lemma one_leq_house_c₁α : 1 ≤ house (h7.c₁ • h7.α') :=
  one_le_house_of_isIntegral (h7.isIntegral_c₁α) h7.c₁αneq0

lemma house_bound_c₁α :
  house (h7.c₁ • h7.α') ^ (a q t * h7.l q u) ≤ house (h7.c₁ • h7.α') ^ (h7.m * q) := by
  refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨h7.one_leq_house_c₁α, ?_⟩)
  simpa [mul_comm] using h7.al_leq_mq q u t

lemma isInt_β_bound : IsIntegral ℤ (h7.c₁ • (↑q + q • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (IsIntegral.add
      ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K q))
      ((IsIntegral.Nat h7.K q).mul h7.isIntegral_c₁β))

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
  IsIntegral ℤ (h7.c₁ • (↑(a q t) + b q t • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_add,
  mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
  (IsIntegral.add
    ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K (a q t)))
    ((IsIntegral.Nat h7.K (b q t)).mul h7.isIntegral_c₁β))

lemma bound_c₁β (q : ℕ) (hq0 : 0 < q) :
  1 ≤ house ((h7.c₁ • (q + q • h7.β'))) := by
  apply one_le_house_of_isIntegral (h7.isInt_β_bound q)
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨h7.c₁neq0, h7.b_sum_neq_0 q hq0⟩

lemma one_leq_house_c₁γ : 1 ≤ house (h7.c₁ • h7.γ') := by
  apply one_le_house_of_isIntegral
  · exact h7.isIntegral_c₁γ
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨h7.c₁neq0, (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

--include u t in
lemma sys_coe_ne_zero : h7.sys_coe q u t ≠ 0 := by
  unfold sys_coe
  rw [mul_assoc]
  apply mul_ne_zero
    (mod_cast β'_neq_zero h7 q t (h7.k q u))
  · exact mul_ne_zero (mod_cast α'_neq_zero h7 q u t)
      (mod_cast γ'_neq_zero h7 q u t)

lemma hM_neq0 : h7.A q hq0 h2mq ≠ 0 := by
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
      · apply h7.c₁neq0; assumption
      · rename_i H11; apply h7.c₁neq0; exact H11.1
    rename_i H1; apply h7.c₁neq0; exact H1.1
  · rename_i H2;
    rcases H2 with ⟨H2, H22⟩
    · apply h7.β'_neq_zero q t (h7.k q u)
      simp_all only [nsmul_eq_mul, ne_eq, not_false_eq_true,
      zero_pow, t, u]
    · rename_i H1; apply (h7.alpha'_beta'_gamma'_ne_zero).1; exact H1.1
    rename_i H2;
    apply (h7.alpha'_beta'_gamma'_ne_zero).2.2
    exact H2.1

lemma cardmn : Fintype.card (Fin (h7.m * h7.n q)) = h7.m * h7.n q := by
  simp only [Fintype.card_fin]

omit hq0 h2mq in
lemma cardqq : card (Fin (q*q)) = q * q := by
  simp only [Fintype.card_fin]

lemma housec1_gt_zero : 0 ≤ @house.c₁ h7.K _ _ h7.hd := by
  apply mul_nonneg
  · rw [le_iff_eq_or_lt]
    · right
      simp only [Nat.cast_pos]
      exact Module.finrank_pos
  · apply mul_nonneg
    · simp only [le_sup_iff, zero_le_one, true_or]
    · apply (le_trans zero_le_one (le_max_left ..))

def c₂ : ℤ := (|h7.c₁| ^ (((1 + 2*h7.m * (↑2*h7.m))) + (1 + 2*h7.m * (↑2*h7.m))))

omit h2mq in
lemma one_leq_c₂ : 1 ≤ h7.c₂ := by
  apply le_trans (Int.cast_one_le_of_pos (h7.one_leq_abs_c₁))
  · nth_rw 1 [← pow_one (a:= |h7.c₁|)]
    unfold c₂
    simp only [Int.cast_eq]
    apply pow_le_pow_right₀ (h7.one_leq_abs_c₁)
    exact
      Nat.le_add_left 1
      ((1 + 2 * h7.m * (2 * h7.m)).add
      (Nat.add 1
      (((2 * h7.m).mul (Nat.mul 2 (2 * h7.h + 1) + 1)).add (Nat.mul 2 (2 * h7.h + 1) + 1))))

lemma zero_leq_c₂ : 0 ≤ h7.c₂ :=
  le_trans Int.one_nonneg (h7.one_leq_c₂)

def c₃ : ℝ := h7.c₂ * (1 + house h7.β')* Real.sqrt (2*h7.m) *
  (max 1 (((house h7.α' ^ (2*h7.m^2)) * house h7.γ' ^(2*h7.m^2))))

lemma one_leq_c₃ : 1 ≤ h7.c₃ := by
  dsimp [c₃]
  trans
  · have := h7.one_leq_c₂; norm_cast at this
  · simp only [mul_assoc]
    norm_cast
    refine one_le_mul_of_one_le_of_one_le (by norm_cast; exact h7.one_leq_c₂) ?_
    · have h1 : 1 ≤ (1 + house h7.β') := by
        simp only [le_add_iff_nonneg_right]; apply house_nonneg
      have h2 : 1 ≤ (max 1 ((house h7.α' ^ (2 * h7.m ^ 2) *
        house h7.γ' ^ (2 * h7.m ^ 2)) ^ 2 * ↑(h7.m))) := le_max_left _ _
      have h3 : 1 ≤ ((Real.sqrt ((2*h7.m)))) := by
         rw [Real.one_le_sqrt]
         calc 1 ≤ (h7.m : ℝ) := mod_cast h7.hm
              _ ≤ 2 * h7.m := le_mul_of_one_le_left (by simp) (one_le_two)
      calc 1 ≤ (1 + house h7.β') := h1
           _ ≤ (1 + house h7.β') * (Real.sqrt ((2*h7.m))) := by
            nth_rw 1 [← mul_one (a := (1 + house h7.β'))]
            apply mul_le_mul (Preorder.le_refl (1 + house h7.β')) (h3)
              (zero_le_one' ℝ) (zero_le_one.trans h1)
      nth_rw 1 [← mul_one (a := (1 + house h7.β') * (Real.sqrt ((2*h7.m))))]
      simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
      apply mul_le_mul (le_refl _) ?_ (by grind) (by grind)
      · apply mul_le_mul (le_refl _) (by grind) (by positivity) (by positivity)

include hq0 h2mq in
lemma c2_abs_val_pow : ↑|(h7.c₂ ^ h7.n q : ℤ)| ≤ (h7.c₂ ^ h7.n q : ℤ) := by
  simp only [abs_pow]
  refine (pow_le_pow_iff_left₀ (abs_nonneg _)
    (h7.zero_leq_c₂)
    (h7.n_neq_0 q hq0 h2mq)).mpr (abs_le_of_sq_le_sq (le_refl _) (h7.zero_leq_c₂))

lemma house_muls (s t : ℕ) (h : s ≤ t) (_ : 0 ≤ t) :
  (s • house h7.β') ≤ (t • house h7.β') := by
  simp only [nsmul_eq_mul]
  apply mul_le_mul (by aesop) (le_refl _) (house_nonneg h7.β') (by positivity)

lemma house_add_mul_leq :
    house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ≤
     (|h7.c₁| * |(q : ℤ)|) * (1 + house (h7.β')) := by
  calc _ ≤ house (h7.c₁ • (a q t : ℤ) + h7.c₁ • (b q t : ℤ) • h7.β') := ?_
       _ ≤ house (h7.c₁ • ((a q t : ℤ) : h7.K)) +
        house (h7.c₁ • ((b q t : ℤ) • h7.β')) := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) +
         house (h7.c₁ : h7.K) * house ((b q t : ℤ) • h7.β') := ?_
       _ ≤  house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) +
         house (h7.c₁ : h7.K) * (house ((b q t : ℤ) : h7.K) * house ( h7.β')) := ?_
       _ = |h7.c₁| * |(a q t : ℤ)| + |h7.c₁| * |((b q t) : ℤ)| * house (h7.β') := ?_
       _ ≤ |h7.c₁| * |(q : ℤ)| + |h7.c₁| * |((q) : ℤ)| * house h7.β' := ?_
       _ = |h7.c₁| * |(q : ℤ)| * (1 + house h7.β') := ?_
  · norm_cast; rw [smul_add]
  · apply house_add_le
  · refine add_le_add (by rw [zsmul_eq_mul]; apply house_mul_le)
                      (by rw [zsmul_eq_mul]; apply house_mul_le)
  · refine add_le_add ?_ ?_
    · apply mul_le_mul (le_refl _) (le_refl _); all_goals apply house_nonneg
    · refine mul_le_mul (le_refl _) (by rw [zsmul_eq_mul]; apply house_mul_le)
        (house_nonneg _) (house_nonneg _)
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add
      (mul_le_mul (le_refl _)
        (mod_cast ((finProdFinEquiv.symm.toFun t).1).isLt)
        (Int.cast_nonneg (Int.zero_le_ofNat (a q t)))
        (Int.cast_nonneg  (abs_nonneg (h7.c₁)))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (Preorder.le_refl _)
      · apply mul_le_mul (mod_cast ((finProdFinEquiv.symm.toFun t).2).isLt) (le_refl _)
          (house_nonneg _) ?_
        · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
      · apply mul_nonneg (by positivity) (house_nonneg _)
      · simp only [Int.cast_abs, abs_nonneg]
  · rw [mul_add]
    simp only [Int.cast_abs, mul_one]

lemma c₃_pow : h7.c₃ ^ ↑(h7.n q : ℝ) = h7.c₂ ^ ↑(h7.n q) * ((1 + house (h7.β'))^ ↑(h7.n q)) *
   (((Real.sqrt ((2*h7.m)))) ^ ↑(h7.n q)) * (max 1 (((house (h7.α') ^ (2*h7.m^2)) *
    house (h7.γ') ^(2*h7.m^2))))^ ↑(h7.n q) := by
    unfold c₃
    simp only [Real.rpow_natCast]
    rw [mul_pow, mul_pow, mul_pow]

include h2mq in
lemma q_eq_n_etc : ↑q ^ ((h7.n q) - 1) ≤
  (Real.sqrt (2*h7.m)^((h7.n q)- 1))* (Real.sqrt (h7.n q))^((h7.n q)- 1) := by
  have : (Real.sqrt ((2*h7.m)*(h7.n q))) =
    Real.sqrt (2*h7.m)* Real.sqrt (h7.n q) := by
    rw [Real.sqrt_mul]
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ ((h7.n q - 1))
  · rw [← this, Real.le_sqrt]
    · norm_cast; apply sq_le_two_mn h7 q h2mq
    · positivity
    · positivity

include h2mq in
lemma q_le_two_mn : q ≤ 2 * h7.m * h7.n q :=
  le_trans (Nat.le_pow (Nat.zero_lt_two)) ((sq_le_two_mn h7 q h2mq))

include h2mq in
lemma pow_c₂ : h7.m * q - a q t * h7.l q u ≤ h7.m * (2 * (h7.m * h7.n q)) := by
  simp only [tsub_le_iff_right]
  calc _ ≤  h7.m * (2 * (h7.m * h7.n q)) := ?_
       _ ≤ h7.m * (2 * (h7.m * h7.n q)) + a q t * h7.l q u := ?_
  · apply mul_le_mul (by rfl) ?_ (by simp) (by simp)
    · have := h7.q_le_two_mn q h2mq
      simp only [mul_assoc] at *
      exact this
  · simp only [le_add_iff_nonneg_right, zero_le]

include h2mq in
lemma pow_c₂' : h7.m * q - b q t * h7.l q u ≤ h7.m * (2 * (h7.m * h7.n q)) := by
  simp only [tsub_le_iff_right]
  calc _ ≤  h7.m * (2 * (h7.m * h7.n q)) := ?_
       _ ≤ h7.m * (2 * (h7.m * h7.n q)) + b q t * h7.l q u := ?_
  · apply mul_le_mul (by rfl) ?_ (by simp) (by simp)
    · have := h7.q_le_two_mn q h2mq
      simp only [mul_assoc] at *
      exact this
  · simp

lemma c_coeffspow' :
  ((h7.c₁ : ℤ) ^ ((h7.n q)- 1) *
   (h7.c₁ : ℤ) ^ (h7.m * q) * (h7.c₁) ^ (h7.m * q)) =
    ((h7.c₁ : ℤ) ^ (((h7.n q) - 1 - h7.k q u)) *
      (h7.c₁ : ℤ) ^ (h7.m * q - (a q t * h7.l q u) ) *
      (h7.c₁ : ℤ) ^ (h7.m * q - ((b q t * h7.l q u)))) •
  ((h7.c₁) ^ (h7.k q u ) * (h7.c₁ ) ^ (a q t * h7.l q u) *
    (h7.c₁) ^ (b q t * h7.l q u )) := by
  have triple_comm_int (a b c : ℤ) (x y z : ℤ) :
   ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
     simp only [zsmul_eq_mul, Int.cast_mul]; ring
  rw [triple_comm_int]
  congr
  · simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_eq]
    rw [← pow_add (m := (h7.n q - 1 - h7.k q u)) (n:=h7.k q u) (a:=h7.c₁)]
    have : (h7.n q - 1 - h7.k q u + h7.k q u) = (h7.n q - 1) := by
      rw [add_comm]
      refine add_tsub_cancel_of_le (Nat.le_sub_of_add_le ((finProdFinEquiv.symm.toFun u).2.isLt))
    rw [this]
  · simp only [smul_eq_mul]
    rw [← pow_add]
    have : (h7.m * q - (a q t * h7.l q u) + (a q t * h7.l q u)) = (h7.m * q) := by
      rw [add_comm]
      refine add_tsub_cancel_of_le ?_
      rw [mul_comm h7.m]
      exact al_leq_mq h7 q u t
    rw [this]
  · simp only [smul_eq_mul]
    rw [← pow_add]
    have : (h7.m * q - (b q t * h7.l q u) + (b q t * h7.l q u)) = (h7.m * q) := by
      rw [add_comm]
      refine add_tsub_cancel_of_le ?_
      rw [mul_comm h7.m]
      exact bl_leq_mq h7 q u t
    rw [this]

lemma sq_n : (Real.sqrt (h7.n q))^((h7.n q : ℝ)-1) =
   (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1)/2) := by
  nth_rw 1 [Real.sqrt_eq_rpow, ← Real.rpow_mul, mul_comm, mul_div]
  · simp only [mul_one]
  · simp only [Nat.cast_nonneg]

include hq0 h2mq in
lemma hAkl : --∀ (k : Fin (h7.m * h7.n q)) (l : Fin (q * q)),
  house ((algebraMap (𝓞 h7.K) h7.K) ((A h7 q) hq0 h2mq u t)) ≤
      (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))  := by
    unfold A sys_coe
    simp only [RingOfIntegers.restrict, RingOfIntegers.map_mk]
    --have:= Real.rpow_natCast (x:=↑(h7.n q : ℝ)) (n:= (((h7.n q) - 1) / 2))
    calc
         _ = house (((h7.c₁ : h7.K) ^ ((h7.n q - 1) - h7.k q u) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ)) •
         (((h7.c₁ : h7.K) ^ h7.k q u) * ((a q t : h7.K) + (b q t) * h7.β') ^ h7.k q u *
          ((h7.c₁ : h7.K) ^ (a q t * h7.l q u)) * h7.α' ^ (a q t * h7.l q u) *
          ((h7.c₁ : h7.K) ^ (b q t * h7.l q u)) * h7.γ' ^ (b q t * h7.l q u))) := ?_
         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ))) *
             house (h7.c₁ ^ (h7.k q u) • (↑(a q t) + (b q t) • h7.β') ^ (h7.k q u)) *
             house (h7.c₁ ^ (a q t * h7.l q u) • h7.α' ^ (a q t * h7.l q u)) *
             house (h7.c₁ ^ (b q t * h7.l q u) • h7.γ' ^ (b q t * h7.l q u)) := ?_
         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ))) *
             house (h7.c₁ • (↑(a q t) + (b q t) • h7.β')) ^ (h7.k q u) *
             house (h7.c₁ • h7.α') ^ (a q t * h7.l q u) *
             house (h7.c₁ • h7.γ') ^ (b q t * h7.l q u) := ?_
         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ))) *
             house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ^ (h7.n q - 1) *
             house (h7.c₁ • h7.α') ^ (h7.m * q) *
             house (h7.c₁ • h7.γ') ^ (h7.m * q) := ?_
         _ ≤  |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)))| *
             (|h7.c₁| * (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.n q - 1) *
             (|h7.c₁| * house (h7.α')) ^ (h7.m * (2 * (h7.m * h7.n q))) *
             (|h7.c₁| * house (h7.γ')) ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
         _ = |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)))| *
            |h7.c₁ ^ (h7.n q - 1)| • (↑|↑q| * (1 + house h7.β')) ^ (h7.n q - 1) *
            |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
              house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
            |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
              house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
         _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)))| *
             ↑|h7.c₁| ^ ((h7.n q - 1) + (2 * h7.m * (2 * (h7.m * h7.n q))))
            * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
               house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ = |(h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ)| *
            |(h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)|
             * |(h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)| *
             ↑|h7.c₁| ^ ((h7.n q - 1) + (2 * h7.m * (2 * (h7.m * h7.n q))))
            * (↑|↑q| ^ ((h7.n q)- 1) * (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
               house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ = |(h7.c₁)| ^ (h7.n q - 1 - h7.k q u : ℕ) *
            |(h7.c₁)| ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * |(h7.c₁)| ^ (h7.m * q - b q t * h7.l q u : ℕ) *
             ↑|h7.c₁| ^ ((h7.n q - 1) + (2 * h7.m * (2 * (h7.m * h7.n q))))
            * (↑|↑q| ^ ((h7.n q) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
               house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ ≤  ↑(h7.c₂)^(h7.n q)
             * (↑|↑q| ^ ((h7.n q ) - 1) *
              (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
         _ ≤ (h7.c₃)^(h7.n q : ℝ) * ((Real.sqrt (h7.n q))^((h7.n q : ℝ)-1)) := ?_
         _ ≤ (h7.c₃ ^ (h7.n q: ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)) := ?_
    · unfold c_coeffs
      rw [h7.c_coeffspow' q u t, smul_assoc]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      rw [triple_comm h7.K (h7.c₁^(h7.k q u))
        (h7.c₁^(a q t * h7.l q u)) (h7.c₁^(b q t * h7.l q u))
        (((a q t) + b q t • h7.β')^(h7.k q u))
         (h7.α' ^ (a q t * h7.l q u)) (h7.γ' ^ (b q t * h7.l q u))]
      simp only [nsmul_eq_mul, zsmul_eq_mul,
        Int.cast_pow, Int.cast_mul, smul_eq_mul,mul_assoc]
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,mul_assoc]
      trans
      · apply house_mul_le
      apply mul_le_mul ?_ ?_ (house_nonneg _) (house_nonneg _)
      · rfl
      · rw [← mul_assoc,← mul_assoc,← mul_assoc]
        trans
        · apply house_mul_le
        rw [← mul_assoc]
        apply mul_le_mul
        · rw [mul_assoc]; apply house_mul_le
        · rfl
        · apply (house_nonneg _)
        · apply mul_nonneg (house_nonneg _) (house_nonneg _)
    · simp only [mul_assoc]
      apply mul_le_mul
      · rfl
      · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
        rw [← mul_pow]; rw [← mul_pow]; rw [← mul_pow]
        apply mul_le_mul (house_pow_le _ _)
        · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
            (by apply pow_nonneg (house_nonneg _))
        · apply mul_nonneg (house_nonneg _) (house_nonneg _)
        · apply pow_nonneg; apply house_nonneg
      · unfold house; positivity
      · apply house_nonneg
    · apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · rfl
          · apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
            · apply isInt_β_bound_low
            · intros H
              rw [zsmul_eq_mul] at H
              simp only [mul_eq_zero, Int.cast_eq_zero] at H
              cases H with
              | inl hp => apply h7.c₁_neq_zero; exact hp
              | inr hq => apply h7.β'_neq_zero q t 1; rw [pow_one]; exact hq
            · refine (Nat.le_sub_iff_add_le' ?_).mpr ?_
              · apply one_le_n h7 q hq0 h2mq
              · rw [add_comm]; exact (finProdFinEquiv.symm.toFun u).2.isLt
          · apply pow_nonneg; apply house_nonneg
          · apply house_nonneg
        · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
          · exact h7.isIntegral_c₁α
          · exact h7.c₁αneq0
          · rw [mul_comm h7.m q]; apply al_leq_mq h7 q u t
        · apply pow_nonneg; apply house_nonneg
        · unfold house; positivity
      · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
        · exact h7.isIntegral_c₁γ
        · exact h7.c₁cneq0
        · rw [mul_comm h7.m q]; apply bl_leq_mq h7 q u t
      · apply pow_nonneg; apply house_nonneg
      · unfold house
        positivity
    · apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · rw [← house_intCast (K:=h7.K)]
            simp only [Int.cast_mul, Int.cast_pow, le_refl]
          · refine pow_le_pow_left₀ ?_ ?_ (h7.n q - 1)
            · apply house_nonneg
            · rw [← mul_assoc]
              apply h7.house_add_mul_leq q t
          · apply pow_nonneg; apply house_nonneg
          · simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_nonneg]
        · calc _ ≤ house (h7.c₁ • h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
               _ ≤ (↑|h7.c₁| * house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
          · have house_alg_int_leq_pow (α : h7.K) (n m : ℕ)
                (h : n ≤ m) (hα0 : α ≠ 0) (H : IsIntegral ℤ α) : house α ^ n ≤ house α ^ m :=
                 Bound.pow_le_pow_right_of_le_one_or_one_le
              (Or.inl ⟨one_le_house_of_isIntegral H hα0, h⟩)
            refine house_alg_int_leq_pow (h7.c₁ • h7.α') (h7.m * q)
              (h7.m * (2 * (h7.m * h7.n q))) ?_ ?_ ?_
            · apply mul_le_mul
              · apply Preorder.le_refl
              · exact (by  have H := q_le_two_mn h7 q h2mq; rw [mul_assoc] at H; exact H )
              · simp only [zero_le]
              · simp only [zero_le]
            · exact h7.c₁αneq0
            · exact h7.isIntegral_c₁α
          · refine pow_le_pow_left₀ ?_ ?_ (h7.m * (2 * (h7.m * h7.n q)))
            · apply house_nonneg
            · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.α') := ?_
                   _ ≤ _ := ?_
              · simp only [zsmul_eq_mul]
                apply house_mul_le
              · simp only [house_intCast, Int.cast_abs, le_refl]
        · apply pow_nonneg; apply house_nonneg
        · apply mul_nonneg
          · simp only [Int.cast_abs, abs_nonneg]
          · unfold house
            positivity
      · calc _ ≤ house (h7.c₁ • h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
             _ ≤ (↑|h7.c₁| * house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
        · have house_alg_int_leq_pow (α : h7.K) (n m : ℕ)
                (h : n ≤ m) (hα0 : α ≠ 0) (H : IsIntegral ℤ α) : house α ^ n ≤ house α ^ m :=
                 Bound.pow_le_pow_right_of_le_one_or_one_le
                 (Or.inl ⟨one_le_house_of_isIntegral H hα0, h⟩)
          refine
            house_alg_int_leq_pow (h7.c₁ • h7.γ') (h7.m * q)
              (h7.m * (2 * (h7.m * h7.n q))) ?_ ?_ ?_
          · apply mul_le_mul
            · apply Preorder.le_refl
            · exact (by  have H := q_le_two_mn h7 q h2mq; rw [mul_assoc] at H; exact H )
            · simp only [zero_le]
            · simp only [zero_le]
          · exact h7.c₁cneq0
          · exact h7.isIntegral_c₁γ
        refine pow_le_pow_left₀ ?_ ?_ (h7.m * (2 * (h7.m * h7.n q)))
        · apply house_nonneg
        · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.γ') := ?_
               _ ≤ _ := ?_
          · simp only [zsmul_eq_mul]
            apply house_mul_le
          · simp only [house_intCast, Int.cast_abs, le_refl]
      · apply pow_nonneg; apply house_nonneg
      · unfold house
        positivity
    · rw [zsmul_eq_mul]; rw [zsmul_eq_mul]; rw [zsmul_eq_mul]
      rw [mul_pow]; rw [mul_pow]; rw [mul_pow]
      rw [mul_pow]; rw [mul_pow]; rw [abs_pow]; rw [abs_pow]
      congr
      · simp only [Int.cast_abs, Int.cast_pow]
      · simp only [Nat.abs_cast, Int.cast_natCast]
      · simp only [Int.cast_abs, Int.cast_pow]
      · simp only [Int.cast_abs, Int.cast_pow]
    · have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
          ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      have := triple_comm ℝ
       |(h7.c₁^(h7.n q - 1) : ℤ)|
       |(h7.c₁^(h7.m * (2 * (h7.m * h7.n q))) : ℤ)|
       |(h7.c₁^(h7.m * (2 * (h7.m * h7.n q))) : ℤ)|
       ((↑|↑q| * (1 + house (h7.β')))^(h7.n q - 1))
       ((house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))))
       ((house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))))
      simp only [mul_assoc] at *
      simp only [zsmul_eq_mul] at *
      rw [← this]; clear this
      rw [abs_pow]; rw [abs_pow]; rw [← pow_add]; rw [← pow_add]
      apply mul_le_mul
      · simp only [abs_pow, Int.cast_pow, Int.cast_abs, le_refl]
      · apply mul_le_mul
        · rw [← pow_add]; rw [← pow_add]
          rw [Eq.symm (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
          simp only [Int.cast_pow, Int.cast_abs, le_refl]
        · rw [mul_pow]
          simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
        · unfold house; positivity
        · apply pow_nonneg; simp only [Int.cast_abs, abs_nonneg]
      · unfold house; positivity
      · simp only [Int.cast_abs, abs_nonneg]
    · rw [← pow_add]; rw [← pow_add]
      simp only [Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow]
      rw [← pow_add]; rw [← pow_add]; rw [← pow_add]; rw [← pow_add]
    · rw [abs_pow]; rw [abs_pow]; rw [abs_pow]
      simp only [mul_assoc,Int.cast_pow, Int.cast_abs, Nat.abs_cast]
    · apply mul_le_mul
      · rw [← pow_add]; rw [← pow_add]; rw [← pow_add]
        simp only [Int.cast_abs]
        unfold c₂
        simp only [Int.cast_pow, Int.cast_abs]
        rw [← pow_mul]
        refine pow_le_pow_right₀ ?_ ?_
        · exact mod_cast h7.one_leq_abs_c₁
        · rw [add_mul]
          rw [add_mul]
          simp only [one_mul]
          simp only [mul_assoc]
          rw [(Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
          simp only [add_assoc]
          refine Nat.add_le_add ?_ ?_
          · simp only [tsub_le_iff_right]
            refine Nat.le_succ_of_le ?_
            exact Nat.le_add_right (h7.n q) (h7.k q u)
          · refine Nat.add_le_add ?_ ?_
            · exact pow_c₂ h7 q u t h2mq
            · refine Nat.add_le_add ?_ ?_
              ·  exact pow_c₂' h7 q u t h2mq
              · simp only [add_le_add_iff_right, tsub_le_iff_right, le_add_iff_nonneg_right,
                zero_le]
      · simp only [Nat.abs_cast, le_refl]
      · unfold house; positivity
      · apply pow_nonneg; exact mod_cast zero_leq_c₂ h7
    · rw [h7.c₃_pow q]
      simp only [mul_assoc]
      apply mul_le_mul
      · rfl
      · calc _ ≤ (Real.sqrt (2*h7.m)^(h7.n q -1))* (Real.sqrt (h7.n q))^((h7.n q) -1)
                * ((1 + house h7.β') ^ (h7.n q - 1) *
                  (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                    house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) := ?_
             _ ≤ (Real.sqrt (2*h7.m)^(h7.n q -1))
                * ((1 + house h7.β') ^ (h7.n q - 1) *
                   (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q)))
                * house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) *
                  (Real.sqrt (h7.n q))^(((h7.n q) : ℝ)-1) := ?_
             _ ≤ √(2 * ↑(h7.m)) ^ (h7.n q - 1) *
                ((1 + house h7.β') ^ (h7.n q - 1) *
                  (house h7.α' ^ (h7.m * 2 * h7.m * h7.n q)
                * house h7.γ' ^ (h7.m * 2 * h7.m * h7.n q))) *
                (Real.sqrt (h7.n q))^(((h7.n q) : ℝ)-1) := ?_
             _ ≤ √(2 * ↑(h7.m)) ^ ((h7.n q)) *
               ((1 + house h7.β') ^ ((h7.n q)) * (house h7.α' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)
                * (house h7.γ' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)) *  (Real.sqrt (h7.n q ))
                 ^(((h7.n q) : ℝ)-1) := ?_
        · apply mul_le_mul
          · simp only [Nat.abs_cast]
            apply h7.q_eq_n_etc q h2mq
          · apply Preorder.le_refl
          · unfold house; positivity
          · positivity
        · simp only [mul_assoc]
          nth_rw 3 [mul_comm]
          simp only [mul_assoc]
          simp only [Nat.ofNat_nonneg, Real.sqrt_mul]
          apply mul_le_mul
          · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · apply mul_le_mul
              · apply Preorder.le_refl
              · apply mul_le_mul
                · apply Preorder.le_refl
                · rw [← Real.rpow_natCast (x:=√(h7.n q : ℝ))]
                  apply Real.rpow_le_rpow_of_exponent_le
                  · refine Real.one_le_sqrt.mpr ?_
                    simp only [Nat.one_le_cast]
                    exact one_le_n h7 q hq0 h2mq
                  · rw [le_iff_lt_or_eq]
                    right
                    refine Nat.cast_pred ?_
                    refine Nat.zero_lt_of_ne_zero ?_
                    exact n_neq_0 h7 q hq0 h2mq
                · simp only [Real.sqrt_nonneg, pow_nonneg]
                · apply pow_nonneg; apply house_nonneg
              · unfold house; positivity
              · apply pow_nonneg; apply house_nonneg
            · unfold house; positivity
            · apply pow_nonneg
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
          · unfold house; positivity
          · positivity
        · simp only [mul_assoc]
          apply mul_le_mul
          · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · apply mul_le_mul
              · apply Preorder.le_refl
              · apply Preorder.le_refl
              · unfold house; positivity
              · unfold house; positivity
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · positivity
        · simp only [mul_assoc]
          apply mul_le_mul
          · refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
            left
            constructor
            · refine Real.one_le_sqrt.mpr ?_
              nth_rw 1 [← mul_one (a:=1)]
              apply mul_le_mul
              · simp only [Nat.one_le_ofNat]
              · simp only [Nat.one_le_cast]
                unfold m
                simp only [le_add_iff_nonneg_left, zero_le]
              · simp only [zero_le_one]
              · simp only [Nat.ofNat_nonneg]
            · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
          · apply mul_le_mul
            · refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
              left
              constructor
              · simp only [le_add_iff_nonneg_right]
                apply house_nonneg
              · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
            · apply mul_le_mul
              · rw [← pow_mul]
                simp only [mul_assoc]
                apply Preorder.le_refl
              · rw [← pow_mul]
                simp only [mul_assoc]
                apply Preorder.le_refl
              · unfold house; positivity
              · apply pow_nonneg; apply pow_nonneg; apply house_nonneg
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · positivity
        · nth_rw 2 [← mul_assoc]
          rw [mul_comm  ((1 + house h7.β') ^ (h7.n q)) (((Real.sqrt ((2*h7.m)))) ^ (h7.n q))]
          simp only [mul_assoc]
          apply mul_le_mul
          · refine pow_le_pow_left₀ ?_ ?_ (h7.n q)
            · simp only [Real.sqrt_nonneg]
            · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · simp only  [← mul_assoc]
              apply mul_le_mul
              · rw [← mul_pow]
                refine pow_le_pow_left₀ ?_ ?_ (h7.n q)
                · unfold house; positivity
                · have : ((h7.m * 2) * h7.m) = (2 * h7.m^2) := by
                    rw [mul_comm]
                    rw [← mul_assoc]
                    rw [pow_two]
                    rw [mul_comm]
                  rw [this]; clear this
                  calc _ ≤ ((house h7.α' ^ (2 * h7.m ^ 2) *
                      house h7.γ' ^ (2 * h7.m ^ 2))) := ?_
                       _ ≤ max 1 ((house h7.α' ^ (2 * h7.m^ 2) * house h7.γ' ^ (2 * h7.m ^ 2))
                        ) := ?_
                  · apply Preorder.le_refl
                  · simp only [le_sup_right]
              · apply Preorder.le_refl
              · positivity
              · positivity
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · positivity
      · unfold house; positivity
      · apply pow_nonneg; norm_cast; apply h7.zero_leq_c₂
    · rw [le_iff_eq_or_lt]
      left
      rw [← sq_n]

def applylemma82 [DecidableEq (h7.K →+* ℂ)] :=
    NumberField.house.exists_ne_zero_int_vec_house_le h7.K
  (h7.A q hq0 h2mq)
  (hM_neq0 h7 q hq0 h2mq)
  (h7.h0m q hq0 h2mq)
  (h7.hmn q hq0 h2mq)
  (cardqq q)
  (fun u t => hAkl h7 q hq0 u t h2mq)
  (h7.cardmn q)

variable [DecidableEq (h7.K →+* ℂ)]

abbrev η : Fin (q * q) → 𝓞 h7.K := (applylemma82 h7 q hq0 h2mq).choose

def c₄ : ℝ := (max 1 ((house.c₁ h7.K) * house.c₁ h7.K * 2 * h7.m)) * h7.c₃

lemma one_leq_c₄ : 1 ≤ h7.c₄ := by
  dsimp [c₄]
  refine one_le_mul_of_one_le_of_one_le ?_ (h7.one_leq_c₃)
  · exact le_max_left 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m))

lemma zero_leq_c₄ : 0 ≤ h7.c₄ := by
  unfold c₄
  simp only [lt_sup_iff, zero_lt_one, true_or, mul_nonneg_iff_of_pos_left]
  exact le_trans zero_le_one (h7.one_leq_c₃)

lemma q_sq_real : (q * q : ℝ) = q^2 := by
  norm_cast; exact Eq.symm (pow_two ↑q)

include h2mq in
omit [DecidableEq (h7.K →+* ℂ)] in
lemma q_eq_2sqrtmn_real : (q^2 : ℝ) = 2*h7.m*h7.n q := by
  norm_cast; refine Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq hq0 in
omit [DecidableEq (h7.K →+* ℂ)] in
lemma fracmqn : (↑(h7.m : ℝ) * ↑(h7.n q : ℝ) /
  (2 * ↑(h7.m : ℝ) * ↑(h7.n q : ℝ) - (h7.m * (h7.n q : ℝ))) : ℝ) = 1 := by
    have : 2 * ↑(h7.m : ℝ) * ↑(h7.n q : ℝ) - ↑(h7.m : ℝ) * ↑(h7.n q : ℝ) =
      ↑(h7.m : ℝ) * ↑(h7.n q : ℝ ) := by ring
    rw [this]
    norm_cast
    refine (div_eq_one_iff_eq ?_).mpr rfl
    simp only [Nat.cast_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    refine ⟨  Ne.symm (Nat.zero_ne_add_one (2 * h7.h + 1)), h7.n_neq_0 q hq0 h2mq⟩

include hq0 h2mq in
omit [DecidableEq (h7.K →+* ℂ)] in
lemma hfrac : ↑(h7.n q : ℝ) * ↑(h7.n q : ℝ) ^ ((↑(h7.n q : ℝ) - 1) / 2) =
  ↑(h7.n q : ℝ) ^ ((↑(h7.n q : ℝ) + 1) / 2) := by
    nth_rw 1 [← Real.rpow_one (x := ↑(h7.n q))]
    rw [← Real.rpow_add]
    · congr; ring
    · norm_cast
      have := h7.one_le_n q hq0 h2mq
      linarith

open NumberField.house in
lemma fromlemma82_bound :
  house (algebraMap (𝓞 h7.K) h7.K (h7.η q hq0 h2mq t)) ≤
     h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) := by
  calc _ ≤  house.c₁ h7.K * (house.c₁ h7.K * ↑(q * q) *
    (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))) ^
      ((h7.m * h7.n q : ℝ) / (↑(q * q : ℝ) - ↑(h7.m * h7.n q ))) := ?_
       _ = (house.c₁ h7.K * (house.c₁ h7.K * 2 * h7.m *
    (h7.c₃ ^ (h7.n q : ℝ)) * ((h7.n q : ℝ) *
    (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)))) := ?_
       _ ≤ h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1)/2) : ℝ) := ?_
  · exact mod_cast ((applylemma82 h7 q hq0 h2mq).choose_spec).2.2 t
  · rw [← pow_two q, q_sq_real q, h7.q_eq_2sqrtmn q h2mq, h7.q_eq_2sqrtmn_real q h2mq]
    have fracmqn := h7.fracmqn q hq0 h2mq
    nth_rw 2 [← Nat.cast_mul] at fracmqn
    rw [fracmqn]; clear fracmqn
    rw [Real.rpow_one, h7.hfrac q hq0 h2mq]
    simp only [mul_eq_mul_left_iff]
    left
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    refine (mul_right_inj' ?_).mpr ?_
    · have : 1 ≤ house.c₁ h7.K := by
        unfold house.c₁
        have : 0 < ↑(Module.finrank ℚ h7.K) := Module.finrank_pos
        refine one_le_mul_of_one_le_of_one_le ?_ ?_
        · exact Nat.one_le_cast.mpr this
        · unfold house.c₂
          refine one_le_mul_of_one_le_of_one_le ?_ ?_
          · apply le_max_left
          apply le_max_left
      refine Ne.symm (ne_of_lt ?_)
      linarith
    · have : ↑(2 * (h7.m * h7.n q)) * (h7.c₃ ^
        ↑(h7.n q : ℝ) * ↑(h7.n q) ^ ((↑(h7.n q: ℝ) - 1) / 2))=
        ↑(2 * h7.m) * (h7.c₃ ^ ↑(h7.n q : ℝ) *
        (h7.n q * ↑(h7.n q) ^ ((↑(h7.n q : ℝ) - 1) / 2))) := by
          nth_rw 4 [← mul_assoc]
          nth_rw 8 [← mul_comm]
          simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
          simp only [mul_assoc]
      rw [this, hfrac h7 q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
  · rw [hfrac h7 q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · unfold c₄
      rw [Real.mul_rpow]
      · refine mul_le_mul_of_nonneg_right ?_ ?_
        · trans
          · apply le_max_right 1 ((house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m)))
          · nth_rw 1 [← Real.rpow_one
              (x := max 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m)))]
            apply Real.rpow_le_rpow_of_exponent_le
            · apply le_max_left
            · simp only [Nat.one_le_cast]; exact one_le_n h7 q hq0 h2mq
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · apply (le_trans zero_le_one (one_leq_c₃ h7))
      · apply (le_trans zero_le_one (le_max_left ..))
      · apply (le_trans zero_le_one (one_leq_c₃ h7))
    · apply Real.rpow_nonneg; simp only [Nat.cast_nonneg]

end Setup
