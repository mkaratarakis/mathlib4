/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAlg

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

lemma decompose_ij (i j : Fin (q * q)) : i = j ↔
  (finProdFinEquiv.symm.1 i).1 = (finProdFinEquiv.symm.1 j).1 ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = (finProdFinEquiv.symm.1 j).2 := by
  apply Iff.intro
  · intro H; rw [H]; constructor <;> rfl
  · intro H
    rcases H with ⟨H1, H2⟩
    have : finProdFinEquiv.symm.1 i = finProdFinEquiv.symm.1 j := by
      rw [← Prod.eta (finProdFinEquiv.symm.toFun i), H1]
      rw [← Prod.eta (finProdFinEquiv.symm.toFun j), H2]
    clear H1 H2
    have := congr_arg finProdFinEquiv.toFun this
    simp only [Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq] at this
    assumption

namespace Setup

omit [DecidableEq (h7.K →+* ℂ)] in
lemma hdist : ∀ (i j : Fin (q * q)), i ≠ j → ρ h7 q i ≠ ρ h7 q j := by
  intros i j hij
  rw [ne_eq, decompose_ij q] at hij
  rw [not_and'] at hij
  unfold ρ
  simp only [not_or, ne_eq, mul_eq_mul_right_iff, not_or]
  constructor
  · by_cases Heq : (finProdFinEquiv.symm.1 i).2 = (finProdFinEquiv.symm.1 j).2
    · unfold a b
      rw [Heq]
      have := hij Heq
      intro H
      apply this
      simp only [Equiv.toFun_as_coe, nsmul_eq_mul, add_left_inj, Nat.cast_inj] at H
      exact Fin.eq_of_val_eq H
    · let i2 : ℕ := (finProdFinEquiv.symm.toFun i).2 + 1
      let j2 : ℕ := (finProdFinEquiv.symm.toFun j).2 + 1
      let i1 : ℕ := (finProdFinEquiv.symm.toFun i).1 + 1
      let j1 : ℕ := (finProdFinEquiv.symm.toFun j).1 + 1
      have hb := h7.hirr (i1 - j1) (j2 - i2)
      rw [← ne_eq]
      change i1 + i2 • h7.β ≠ j1 + j2 • h7.β
      intros H
      have hb := h7.hirr (i1 - j1) (j2 - i2)
      apply hb
      have h1 : i1 + i2 • h7.β = j1 + j2 • h7.β  ↔
        (i1 + i2 • h7.β) - (j1 + j2 • h7.β) = 0 := Iff.symm sub_eq_zero
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • h7.β - (↑j1 + ↑j2 • h7.β) = 0 ↔
         ↑i1 + i2 • h7.β - ↑j1 - ↑j2 • h7.β = 0 := by
          simp_all only [ne_eq, Equiv.toFun_as_coe,
          finProdFinEquiv_symm_apply,
            nsmul_eq_mul, iff_true, sub_self,
            add_sub_cancel_left]
      rw [h2] at H
      have h3 : ↑i1 + i2 • h7.β - ↑j1 - j2 • h7.β = 0 ↔
          ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 := by
        ring_nf
      rw [h3] at H
      have hij2 : i2 ≠ j2 := by
        by_contra HC
        apply Heq
        refine Fin.eq_of_val_eq ?_
        exact Nat.succ_inj.mp HC
      have h4 : ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 := by
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul, add_assoc, ← add_mul]
        simp only [smul_eq_mul]
        rw [← sub_eq_add_neg]
      rw [h4] at H
      have h5 : ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 ↔
       ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) := by
        rw [add_eq_zero_iff_eq_neg]
      rw [h5] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) ↔
          ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β := by
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul]
        simp only [neg_sub]
      rw [h6] at H
      have h7 : ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β ↔
         (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) =  h7.β := by
        rw [div_eq_iff, mul_comm,smul_eq_mul]
        intros HC
        apply hij2
        rw [sub_eq_zero] at HC
        simp only [Nat.cast_inj] at HC
        exact HC.symm
      rw [h7] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast]
  · exact h7.log_zero_zero

abbrev V := vandermonde (fun t => h7.ρ q t)

omit [DecidableEq (h7.K →+* ℂ)] in
lemma vandermonde_det_ne_zero : det (h7.V q) ≠ 0 := by
  by_contra H
  rw [V, det_vandermonde_eq_zero_iff] at H
  rcases H with ⟨i, j, ⟨hij, hij'⟩⟩
  apply h7.hdist q i j hij' hij

open Differentiable Complex

abbrev R : ℂ → ℂ := fun x => ∑ t, (canonicalEmbedding h7.K)
  ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) h7.σ * exp (h7.ρ q t * x)

lemma cexp_mul (c x : ℂ) : deriv (fun x => cexp (c * x)) x = c * cexp (c * x) := by
  change deriv (fun x => exp ((fun x => c * x) x)) x = c * exp (c * x)
  rw [deriv_cexp]
  · rw [deriv_fun_mul]
    · simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
      exact CommMonoid.mul_comm (cexp (c * x)) c
    · fun_prop
    · fun_prop
  · fun_prop

def iteratedDeriv_of_R (k' : ℕ) : deriv^[k'] (fun x => (h7.R q hq0 h2mq) x) =
    fun x => ∑ t, (h7.σ ((h7.η q hq0 h2mq) t)) * exp (h7.ρ q t * x) * (h7.ρ q t)^k' := by
  induction k' with
  | zero => simp only [pow_zero, mul_one]; rfl
  | succ k hk =>
    rw [← iteratedDeriv_eq_iterate] at *
    simp only [iteratedDeriv_succ]
    conv => enter [1]; rw [hk]
    ext x
    rw [deriv, fderiv_fun_sum]
    · simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_eq_smul_deriv,
      deriv_mul_const_field', deriv_const_mul_field', smul_eq_mul, one_mul]
      rw [Finset.sum_congr rfl]
      intros t ht
      · rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff, map_eq_zero]; left
        rw [cexp_mul, mul_assoc, (pow_succ' (h7.ρ q t) k)]
        · rw [mul_comm, mul_assoc, mul_eq_mul_left_iff,
           Eq.symm (pow_succ' (h7.ρ q t) k)]; left; rfl
    · intros i hi
      apply mul (by fun_prop) (differentiable_const (h7.ρ q i ^ k))

lemma iteratedDeriv_of_R_is_zero (hR : h7.R q hq0 h2mq = 0) :
  ∀ z k', deriv^[k'] (fun z => h7.R q hq0 h2mq z) z = 0 := by
intros z k'
rw [hR]
simp only [Pi.zero_apply]
rw [← iteratedDeriv_eq_iterate, iteratedDeriv]
aesop

lemma vecMul_of_R_zero (hR : h7.R q hq0 h2mq = 0) :
  (h7.V q).vecMul (fun t => h7.σ ((h7.η q hq0 h2mq) t)) = 0 := by
  unfold V
  rw [funext_iff]
  intros k
  simp only [Pi.zero_apply]
  have deriv_eq : ∀ k', deriv^[k'] (fun x => (h7.R q hq0 h2mq) x) =
    fun x => ∑ t, (h7.σ (h7.η q hq0 h2mq t)) *
    exp (h7.ρ q t * x) * (h7.ρ q t)^k' := by
      intros k'
      exact h7.iteratedDeriv_of_R q hq0 h2mq k'
  have deriv_eq_0 : ∀ k', deriv^[k'] (fun x => h7.R q hq0 h2mq x) 0 = 0 := by
    intros k'
    apply iteratedDeriv_of_R_is_zero (hR:= hR)
  rw [← deriv_eq_0 k, deriv_eq]
  simp only [mul_zero, exp_zero, mul_one]
  unfold vecMul dotProduct vandermonde
  simp only [of_apply]

lemma ηvec_eq_zero (hVecMulEq0 : (h7.V q).vecMul
  (fun t => h7.σ ((h7.η q hq0 h2mq) t)) = 0) :
    (fun t => h7.σ ((h7.η q hq0 h2mq) t )) = 0 := by
  apply eq_zero_of_vecMul_eq_zero
    (h7.vandermonde_det_ne_zero q) hVecMulEq0

lemma hbound_sigma : h7.η q hq0 h2mq ≠ 0 :=
  ((NumberField.house.exists_ne_zero_int_vec_house_le h7.K (h7.A q hq0 h2mq) (hM_ne_zero h7 q hq0 h2mq)
  (h7.h0m q hq0 h2mq) (h7.hmn q hq0 h2mq) (Fintype.card_fin _) (fun u t ↦ hAkl h7 q hq0 u t h2mq)
  (Fintype.card_fin _)).choose_spec.1)

lemma R_nonzero : h7.R q hq0 h2mq ≠ 0 := by
  by_contra H
  have HC := (ηvec_eq_zero h7 q hq0 h2mq)
    (vecMul_of_R_zero h7 q hq0 h2mq H)
  simp only at HC
  apply hbound_sigma h7 q hq0 h2mq
  rw [funext_iff] at HC
  simp only [Pi.zero_apply, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at HC
  unfold η at *
  ext t
  specialize HC t
  simp only [ne_eq, Pi.zero_apply, map_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  exact HC

variable (hγ : h7.α ^ h7.β = h7.σ h7.γ')

omit [DecidableEq (h7.K →+* ℂ)] in
lemma sys_coe_bar :
  Complex.exp (h7.ρ q t * h7.l q u) * (h7.ρ q t ^ (h7.k q u : ℕ) *
  Complex.log h7.α ^ (-(h7.k q u) : ℤ)) = h7.σ (h7.sys_coe q u t) := by
  calc
      _ = cexp (h7.ρ q t * h7.l q u) *
          (((↑(a q t) + ↑(b q t) • h7.β) *
          Complex.log h7.α) ^ (h7.k q u : ℕ)
          * Complex.log h7.α ^ (-↑(h7.k q u) : ℤ)) := ?_
      _ = cexp (h7.ρ q t * h7.l q u) *
        ( (↑(a q t) + ↑(b q t) • h7.β)^ (h7.k q u : ℕ) *
          ((Complex.log h7.α) ^ (h7.k q u : ℕ)
          * Complex.log h7.α ^ (-(h7.k q u) : ℤ))) := ?_
      _ = cexp (h7.ρ q t * h7.l q u) *
      ( (↑(a q t) + ↑(b q t) • h7.β)^ (h7.k q u : ℕ)) := ?_
      _ = h7.σ (h7.sys_coe q u t) := ?_
  · nth_rw 2 [ρ]
  · rw [mul_pow]
    rw [mul_assoc]
  ·  have  : (Complex.log h7.α ^ (h7.k q u) *
         Complex.log h7.α ^ (-(h7.k q u) : ℤ)) = 1 := by
       simp only [zpow_neg, zpow_natCast]
       refine Complex.mul_inv_cancel ?_
       by_contra H
       apply h7.log_zero_zero
       simp only [pow_eq_zero_iff', ne_eq] at H
       apply H.1
     rw [this]
     rw [mul_one]
  · unfold sys_coe
    have h1 : h7.σ ((↑(a q t)+ ↑(b q t) • h7.β') ^ ((h7.k q u) : ℕ)) =
      (↑(a q t) + ↑(b q t) * h7.β) ^ ((h7.k q u) : ℕ) := by
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      rw [h7.habc.2.1]
    rw [map_mul]
    rw [map_mul]
    unfold a b k at *
    rw [h1]; clear h1
    rw [mul_comm]
    rw [mul_assoc]
    simp only [nsmul_eq_mul, map_pow,
      mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
    left
    have : h7.σ h7.α' ^ (a q t * h7.l q u) * h7.σ h7.γ' ^ (b q t * h7.l q u) =
    h7.α ^ (a q t * h7.l q u) * (h7.σ h7.γ')^ (b q t * h7.l q u) := by rw [h7.habc.1]
    unfold a b l at *
    rw [this]
    have : h7.σ h7.γ' = h7.α^h7.β := by rw [h7.habc.2.2]
    rw [this]
    rw [ρ]
    have : h7.α ^ ((a q t * h7.l q u)) * h7.α ^ (↑(b q t * h7.l q u) * h7.β) =
      h7.α ^ ((a q t * h7.l q u) + (↑(b q t * h7.l q u) * h7.β)) := by
      rw [cpow_add]
      · rw [cpow_nat_mul]
        simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
          cpow_eq_zero_iff, ne_eq, mul_eq_zero, not_or]
        left
        rw [cpow_nat_mul]
        simp only [cpow_natCast]
        exact pow_mul' h7.α (a q t) (h7.l q u)
      · exact h7.htriv.1
    rw [cpow_nat_mul] at this
    unfold a b l at *
    rw [this]; clear this
    · have : Complex.log h7.α * (↑(a q t) * ↑(h7.l q u) + ↑(b q t * (h7.l q u)) * h7.β) =
       (↑(a q t) + b q t • h7.β) * Complex.log h7.α * ↑(h7.l q u) := by
       nth_rw 4 [mul_comm]
       have : ( ↑((h7.l q u) * (b q t)) * h7.β) = (↑(((b q t) * h7.β) * (h7.l q u))) := by
        simp only [Nat.cast_mul, mul_rotate (↑(h7.l q u)) (↑(b q t)) h7.β]
       rw [this]
       have : (↑(a q t) * ↑(h7.l q u) + ((b q t * h7.β) * (h7.l q u))) =
        ((↑(a q t)  + (b q t * h7.β)) * (h7.l q u)) := Eq.symm (RightDistribClass.right_distrib
          (↑(a q t)) (↑(b q t) * h7.β) ↑(h7.l q u))
       rw [this]
       simp only [nsmul_eq_mul];
       nth_rw 1 [← mul_assoc, mul_comm, mul_comm]; nth_rw 5 [mul_comm]
      unfold a b l at *
      rw [cpow_def_of_ne_zero]
      · rw [this]
      exact h7.htriv.1

include hq0 h2mq in
lemma sys_coe_foo :(Complex.log h7.α)^(-(h7.k q u) : ℤ) *
 deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u) =
     ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.sys_coe q u t) := by
  rw [iteratedDeriv_of_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := sys_coe_bar h7 q u t
  unfold l at this
  rw [mul_assoc]
  unfold l
  exact this

lemma deriv_sum_blah :
  h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
  deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) =
    h7.σ ((h7.A q hq0 h2mq *ᵥ (h7.η q hq0 h2mq)) u) := by
    have := sys_coe_foo h7 q hq0 u h2mq
    rw [this]
    unfold Matrix.mulVec
    unfold dotProduct
    simp only [← map_mul, ← map_sum]
    congr
    simp only [map_sum, map_mul]
    rw [mul_sum]
    rw [Finset.sum_congr rfl]
    intros x hx
    simp (config :=  {unfoldPartialApp := true} ) only [A]
    simp only [RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
    simp only [Int.cast_mul, Int.cast_pow]
    simp only [mul_assoc]
    rw [mul_comm  (a:= (↑(h7.η q hq0 h2mq x)))
    (b:=
          ((↑(a q x) + b q x • h7.β') ^ h7.k q u *
           (h7.α' ^ (a q x * h7.l q u) * h7.γ' ^ (b q x * h7.l q u))))]
    simp only [mul_assoc]

lemma deriv_sum_blah_zero :
  h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
  deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) = 0 := by
      rw [deriv_sum_blah]
      have hMt0 := (NumberField.house.exists_ne_zero_int_vec_house_le h7.K (h7.A q hq0 h2mq)
        (hM_ne_zero h7 q hq0 h2mq) (h7.h0m q hq0 h2mq) (h7.hmn q hq0 h2mq) (Fintype.card_fin _)
        (fun u t ↦ hAkl h7 q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec.2.1
      simp only [ne_eq, Nat.cast_mul, Real.rpow_natCast, map_eq_zero,
        FaithfulSMul.algebraMap_eq_zero_iff] at *
      unfold η
      simp_all only [ne_eq, Nat.cast_mul, Real.rpow_natCast, Pi.zero_apply]

lemma iteratedDeriv_vanishes (k : Fin (h7.n q)) (l' : Fin (h7.m)) :
  deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
  let u : Fin (h7.m * h7.n q) := (finProdFinEquiv.toFun ⟨l',k⟩)
  have h1 := deriv_sum_blah_zero h7 q hq0 u h2mq
  unfold Setup.k at *
  unfold Setup.l at *
  unfold u at *
  simp only [Equiv.toFun_as_coe,
    Equiv.symm_apply_apply] at *
  have : (h7.σ (h7.c_coeffs q) *
   (Complex.log h7.α)^(-k : ℤ)) * deriv^[k] (h7.R q hq0 h2mq) (l'+1) =
    (h7.σ (h7.c_coeffs q) *
    (Complex.log h7.α)^(-k : ℤ)) * 0 → deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
      apply mul_left_cancel₀
      by_contra H
      simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow,
        map_intCast, zpow_neg, zpow_natCast,
        mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or, inv_eq_zero] at H
      rcases H with ⟨h1, h2⟩
      · apply h7.c₁_ne_zero; assumption
      ·  apply h7.c₁_ne_zero; rename_i h2; exact h2.1
      · apply h7.c₁_ne_zero; rename_i h2; exact h2.1
      ·  apply h7.log_zero_zero; rename_i h2; exact h2.1
  rw [this]
  rw [mul_zero]
  rw [mul_assoc]
  simp only [mul_assoc] at *
  rw [← h1]
  simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg, zpow_natCast,
    Nat.cast_add, Nat.cast_one]


end Setup
end
