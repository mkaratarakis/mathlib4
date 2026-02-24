/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAlgSetup
public import Mathlib.Analysis.Analytic.Order

/-!
This PR is the third component in the formalization of the Gelfond-Schneider Theorem
(Hilbert's Seventh Problem). It connects the algebraically constructed auxiliary function `R(x)`
to its analytical properties, establishing the exact order of vanishing and the fundamental lower
bound on the norm of its non-zero derivative evaluation.

Following the argument in Loo-Keng Hua's "Introduction to Number Theory"
Chapter 17.9, equations (4) and (5)), we define the minimal non-vanishing derivative
order $r$ and scale the evaluation to an algebraic integer to compute its norm.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)


/-!
Since the numbers `ρ₁, ..., ρₜ` are distinct, the function `R(x)`
is not identically zero. For suppose otherwise, then on expanding the right
hand side of `R` we have `η₁ρ₁ + η₂ρ₂ᵏ + ... + ηₜρₜᵏ = 0`, a contradiction.
-/

lemma eq_iff_finProdFinEquiv_symm_ext (i j : Fin (q * q)) : i = j ↔
    (finProdFinEquiv.symm.1 i).1 = (finProdFinEquiv.symm.1 j).1 ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = (finProdFinEquiv.symm.1 j).2 := by
  rw [← Prod.ext_iff, Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq]

namespace Setup

omit [DecidableEq (h7.K →+* ℂ)] in
lemma hdist : ∀ (i j : Fin (q * q)), i ≠ j → ρ h7 q i ≠ ρ h7 q j := by
  intros i j hij
  rw [ne_eq, eq_iff_finProdFinEquiv_symm_ext q] at hij
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
  · exact mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2

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

/-!
Thus, we see from (2) that

  `R(x) = a_{n,ℓ}(x - ℓ)ⁿ + a_{n+1,ℓ}(x - ℓ)ⁿ⁺¹ + ⋯,    1 ≤ ℓ ≤ m,`

where `a_{n,ℓ}, a_{n+1,ℓ}, ...` are not all zero. Hence, there must be a natural
number `r` such that `R⁽ᵏ⁾(ℓ) = 0, 0 ≤ k ≤ r - 1, 1 ≤ ℓ ≤ m`. But for
`1 ≤ ℓ₀ ≤ m` we have `R⁽ʳ⁾(ℓ₀) ≠ 0` so that we see from (3) that `r ≥ n`.
-/

def iteratedDeriv_R (k' : ℕ) : deriv^[k'] (fun x => (h7.R q hq0 h2mq) x) =
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

lemma iteratedDeriv_R_eq_zero (hR : h7.R q hq0 h2mq = 0) :
  ∀ z k', deriv^[k'] (fun z => h7.R q hq0 h2mq z) z = 0 := by
  intros z k'
  rw [hR, ← iteratedDeriv_eq_iterate, iteratedDeriv]
  simp

lemma vecMul_V_eq_zero (hR : h7.R q hq0 h2mq = 0) :
    (h7.V q).vecMul (fun t => h7.σ ((h7.η q hq0 h2mq) t)) = 0 := by
  ext k
  have hk : deriv^[k] (fun x => h7.R q hq0 h2mq x) 0 = 0 := by
    apply h7.iteratedDeriv_R_eq_zero (hR := hR)
  rw [h7.iteratedDeriv_R q hq0 h2mq k] at hk
  unfold V vecMul dotProduct vandermonde
  simpa [of_apply] using hk

lemma ηvec_eq_zero (hVecMulEq0 : (h7.V q).vecMul (fun t => h7.σ ((h7.η q hq0 h2mq) t)) = 0) :
    (fun t => h7.σ ((h7.η q hq0 h2mq) t )) = 0 := by
  apply eq_zero_of_vecMul_eq_zero
    (h7.vandermonde_det_ne_zero q) hVecMulEq0

lemma hbound_sigma : h7.η q hq0 h2mq ≠ 0 :=
  (house.exists_ne_zero_int_vec_house_le h7.K (h7.A q)
  (h7.hM_ne_zero q hq0 h2mq) (mul_pos (Nat.zero_lt_succ (2 * h7.h + 1))
  (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
  (fun u t ↦ h7.house_matrixA_le q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec.1

lemma R_ne_zero : h7.R q hq0 h2mq ≠ 0 := by
  intro H
  have HC := ηvec_eq_zero h7 q hq0 h2mq (vecMul_V_eq_zero h7 q hq0 h2mq H)
  apply hbound_sigma h7 q hq0 h2mq
  ext t
  simpa [η, FaithfulSMul.algebraMap_eq_zero_iff] using congr_fun HC t

variable (hγ : h7.α ^ h7.β = h7.σ h7.γ')

omit [DecidableEq (h7.K →+* ℂ)] in
lemma systemCoeffs_bar :
  Complex.exp (h7.ρ q t * h7.l q u) * (h7.ρ q t ^ (h7.k q u : ℕ) *
  Complex.log h7.α ^ (-(h7.k q u) : ℤ)) = h7.σ (h7.systemCoeffs q u t) := by
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
      _ = h7.σ (h7.systemCoeffs q u t) := ?_
  · nth_rw 2 [ρ]
  · rw [mul_pow]
    rw [mul_assoc]
  ·  have h_log_ne : Complex.log h7.α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg Complex.exp h) h7.htriv.2
     aesop
  · unfold systemCoeffs
    have h1 : h7.σ ((↑(a q t)+ ↑(b q t) • h7.β') ^ ((h7.k q u) : ℕ)) =
      (↑(a q t) + ↑(b q t) * h7.β) ^ ((h7.k q u) : ℕ) := by
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul, h7.habc.2.1]
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
lemma systemCoeffs_foo :(Complex.log h7.α)^(-(h7.k q u) : ℤ) *
 deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u) =
     ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.systemCoeffs q u t) := by
  rw [iteratedDeriv_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := systemCoeffs_bar h7 q u t
  unfold l at this
  rw [mul_assoc]
  unfold l
  exact this

lemma coeffs_mulVec_A_eq : h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
    deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) =
    h7.σ ((h7.A q *ᵥ (h7.η q hq0 h2mq)) u) := by
  rw [systemCoeffs_foo h7 q hq0 u h2mq]
  unfold Matrix.mulVec dotProduct
  simp only [← map_mul, ← map_sum]
  congr 1
  rw [Finset.mul_sum]
  simp only [Int.cast_mul, Int.cast_pow, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intros x hx
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
  push_cast
  ring

lemma coeffs_mul_deriv_eq_zero : h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
    deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) = 0 := by
  rw [coeffs_mulVec_A_eq]
  have hMt0 := (NumberField.house.exists_ne_zero_int_vec_house_le h7.K (h7.A q)
    (hM_ne_zero h7 q hq0 h2mq) (mul_pos ((Nat.zero_lt_succ (2 * h7.h + 1)))
    (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le h7 q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec.2.1
  simp [η, FaithfulSMul.algebraMap_eq_zero_iff]
  aesop

lemma R_analyt_at_point (point : ℂ) : AnalyticAt ℂ (h7.R q hq0 h2mq) point := by
  fun_prop

lemma anever : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
  fun_prop

/-!After defining the auxiliary function R we consider the
first nonzero derivative at an integer ℓ₀.

  `(log α)⁻ʳ R⁽ʳ⁾(ℓ₀) = ρ`.

where r is the smallest integer such that `R⁽ʳ⁾(ℓ₀) ≠ 0`.-/

lemma exists_min_analyticOrderAt :
  let s : Finset (Fin (h7.m)) := Finset.univ
  ∃ l₀' ∈ s, (∃ y, (analyticOrderAt (h7.R q hq0 h2mq) (l₀' + 1)) = y ∧
   (∀ (l' : Fin (h7.m)), l' ∈ s → y ≤ (analyticOrderAt (h7.R q hq0 h2mq) (l' + 1)))) := by
  intros s
  have Hs : s.Nonempty := by
     refine univ_nonempty_iff.mpr ?_
     refine Fin.pos_iff_nonempty.mp ?_
     exact (Nat.zero_lt_succ (2 * h7.h + 1))
  let f : (Fin (h7.m)) → ℕ∞ := fun x => (analyticOrderAt (h7.R q hq0 h2mq) (x + 1))
  have := Finset.exists_min_image s f Hs
  obtain ⟨x, hx, h1⟩ := this
  use x
  refine ⟨hx, by aesop⟩

abbrev l₀' : Fin (h7.m) := (exists_min_analyticOrderAt h7 q hq0 h2mq).choose

abbrev l₀_prop := (exists_min_analyticOrderAt h7 q hq0 h2mq).choose_spec.2

abbrev r' := (l₀_prop h7 q hq0 h2mq).choose

abbrev r'_prop :
  let s : Finset (Fin (h7.m)) := Finset.univ
  analyticOrderAt (h7.R q hq0 h2mq) ↑↑(h7.l₀' q hq0 h2mq + 1 : ℂ) =
    h7.r' q hq0 h2mq ∧
    ∀ l' ∈ s, h7.r' q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' +1) := by
  exact (h7.l₀_prop q hq0 h2mq).choose_spec

end Setup
end
