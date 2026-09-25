/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Series
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Hermite interpolation with ultrametric bounds

Baker–Masser, *Transcendental Number Theory*, Chapter 2, Lemma 7, over an ultrametric field. For
distinct nodes `σ i` in the closed unit disc, pairwise at distance at least `ϱ`, and a node `r`
with an order `s < S`, there is a polynomial `W` whose derivatives of order `< S` vanish at every
node except for the `s`-th derivative at `σ r`, which is `1`. Its coefficients have norm at most
`‖1 / s!‖ * ϱ ^ (-(card * S))`.

The construction is Baker's:
`W = (X - σ r) ^ s / s! * ∏_{i ≠ r} (X - σ i) ^ S * T`, where `T` is the Taylor expansion at `σ r`,
to order `S - s - 1`, of the inverse of the product. The inverse is the product of the geometric
series `(X + d)⁻¹ = ∑ (-1) ^ k d ^ (-(k + 1)) X ^ k` with `‖d‖ ≥ ϱ`, which gives the bound.

## Main statements

* `PadicBaker.iterate_derivative_eval_eq`: `P^{(j)}(a) = j! * (taylor a P).coeff j`.
* `PadicBaker.exists_hermite`: Lemma 7.
-/

@[expose] public section

open Polynomial Nat

namespace PadicBaker

variable {K : Type*} [NontriviallyNormedField K]

section Taylor

theorem iterate_derivative_eval_eq (P : K[X]) (a : K) (j : ℕ) :
    (derivative^[j] P).eval a = (j ! : K) * (taylor a P).coeff j := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

theorem taylor_X_sub_C_pow (a : K) (s : ℕ) : taylor a ((X - C a) ^ s) = X ^ s := by
  rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]

theorem iterate_derivative_eval_X_sub_C_pow (a : K) (s j : ℕ) :
    (derivative^[j] ((X - C a) ^ s)).eval a = if j = s then (s ! : K) else 0 := by
  rw [iterate_derivative_eval_eq, taylor_X_sub_C_pow, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

end Taylor

section Bounds

variable [IsUltrametricDist K]

theorem norm_coeff_mul_le {P Q : K[X]} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : ∀ i, ‖P.coeff i‖ ≤ A) (hQ : ∀ j, ‖Q.coeff j‖ ≤ B) (n : ℕ) :
    ‖(P * Q).coeff n‖ ≤ A * B := by
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hP _) (hQ _) (norm_nonneg _) hA

theorem norm_coeff_pow_le_one {P : K[X]} (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (m : ℕ) :
    ∀ n, ‖(P ^ m).coeff n‖ ≤ 1 := by
  induction m with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih =>
    intro n; rw [pow_succ]
    simpa using norm_coeff_mul_le zero_le_one zero_le_one ih hP n

theorem norm_coeff_prod_le_one {ι : Type*} (s : Finset ι) {P : ι → K[X]}
    (hP : ∀ i ∈ s, ∀ n, ‖(P i).coeff n‖ ≤ 1) : ∀ n, ‖(∏ i ∈ s, P i).coeff n‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n; rw [Finset.prod_empty, coeff_one]; split_ifs <;> simp
  | insert a s ha ih =>
    intro n
    rw [Finset.prod_insert ha]
    simpa using norm_coeff_mul_le zero_le_one zero_le_one (hP a (Finset.mem_insert_self a s))
      (ih fun i hi => hP i (Finset.mem_insert_of_mem hi)) n

omit [IsUltrametricDist K] in
theorem norm_coeff_X_sub_C_le_one {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖(X - C a).coeff n‖ ≤ 1 := by
  rw [coeff_sub, coeff_X, coeff_C]
  split_ifs with h1 h2 <;> first | omega | simp [ha]

/-- Composition with a polynomial with coefficients of norm at most one does not increase the
largest coefficient. -/
theorem norm_coeff_comp_le {P q : K[X]} {A : ℝ} (hA : 0 ≤ A) (hP : ∀ k, ‖P.coeff k‖ ≤ A)
    (hq : ∀ m, ‖q.coeff m‖ ≤ 1) (n : ℕ) : ‖(P.comp q).coeff n‖ ≤ A := by
  rw [comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hA fun e _ => ?_
  rw [coeff_C_mul, norm_mul]
  calc ‖P.coeff e‖ * ‖(q ^ e).coeff n‖ ≤ A * 1 :=
        mul_le_mul (hP e) (norm_coeff_pow_le_one hq e n) (norm_nonneg _) hA
    _ = A := mul_one A

end Bounds

section Geometric

/-- The power series `(X + d)⁻¹ = ∑ (-1) ^ k d ^ (-(k + 1)) X ^ k`. -/
noncomputable def invLin (d : K) : PowerSeries K :=
  PowerSeries.mk fun k => (-1) ^ k * (d ^ (k + 1))⁻¹

theorem X_add_C_mul_invLin {d : K} (hd : d ≠ 0) :
    (PowerSeries.X + PowerSeries.C d) * invLin d = 1 := by
  ext n
  rw [add_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases n with - | k
  · simp [invLin, hd]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [invLin, PowerSeries.coeff_mk, pow_succ, Nat.succ_ne_zero, ↓reduceIte]
    field_simp
    ring

theorem norm_coeff_invLin_le {d : K} {ϱ : ℝ} (hϱ : 0 < ϱ) (hd : ϱ ≤ ‖d‖) (k : ℕ) :
    ‖PowerSeries.coeff k (invLin d)‖ ≤ (ϱ ^ (1 + k))⁻¹ := by
  simp only [invLin, PowerSeries.coeff_mk, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_inv]
  rw [add_comm]
  gcongr

theorem norm_coeff_one_le_inv_pow {ϱ : ℝ} (hϱ : 0 < ϱ) (k : ℕ) :
    ‖PowerSeries.coeff k (1 : PowerSeries K)‖ ≤ (ϱ ^ (0 + k))⁻¹ := by
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [norm_zero]; positivity

variable [IsUltrametricDist K]

theorem norm_coeff_mul_le_inv_pow {f g : PowerSeries K} {ϱ : ℝ} (hϱ : 0 < ϱ) {E E' : ℕ}
    (hf : ∀ k, ‖PowerSeries.coeff k f‖ ≤ (ϱ ^ (E + k))⁻¹)
    (hg : ∀ k, ‖PowerSeries.coeff k g‖ ≤ (ϱ ^ (E' + k))⁻¹) (k : ℕ) :
    ‖PowerSeries.coeff k (f * g)‖ ≤ (ϱ ^ (E + E' + k))⁻¹ := by
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [norm_mul]
  calc ‖PowerSeries.coeff x.1 f‖ * ‖PowerSeries.coeff x.2 g‖
      ≤ (ϱ ^ (E + x.1))⁻¹ * (ϱ ^ (E' + x.2))⁻¹ :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = (ϱ ^ (E + E' + k))⁻¹ := by
        rw [← mul_inv, ← pow_add, ← hx]; ring_nf

theorem norm_coeff_pow_le_inv_pow {f : PowerSeries K} {ϱ : ℝ} (hϱ : 0 < ϱ) {E : ℕ}
    (hf : ∀ k, ‖PowerSeries.coeff k f‖ ≤ (ϱ ^ (E + k))⁻¹) (m : ℕ) (k : ℕ) :
    ‖PowerSeries.coeff k (f ^ m)‖ ≤ (ϱ ^ (m * E + k))⁻¹ := by
  induction m generalizing k with
  | zero => simpa using norm_coeff_one_le_inv_pow (K := K) hϱ k
  | succ m ih =>
    rw [pow_succ]
    have := norm_coeff_mul_le_inv_pow hϱ ih hf k
    rwa [show m * E + E = (m + 1) * E by ring] at this

theorem norm_coeff_prod_le_inv_pow {ι : Type*} (s : Finset ι) {f : ι → PowerSeries K} {ϱ : ℝ}
    (hϱ : 0 < ϱ) {E : ℕ} (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ (ϱ ^ (E + k))⁻¹)
    (k : ℕ) : ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤ (ϱ ^ (s.card * E + k))⁻¹ := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa using norm_coeff_one_le_inv_pow (K := K) hϱ k
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have := norm_coeff_mul_le_inv_pow hϱ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) k
    rwa [show E + s.card * E = (s.card + 1) * E by ring] at this

end Geometric

section Main

variable [IsUltrametricDist K] [CharZero K]

/-- **Hermite interpolation with ultrametric bounds** (Baker–Masser, Chapter 2, Lemma 7). -/
theorem exists_hermite {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → K)
    (hσ : ∀ i, ‖σ i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ϱ ≤ ‖σ i - σ j‖) (S : ℕ) (r : ι) {s : ℕ} (hs : s < S) :
    ∃ W : K[X], (∀ i, ∀ j < S, (derivative^[j] W).eval (σ i) = if i = r ∧ j = s then 1 else 0) ∧
      ∀ n, ‖W.coeff n‖ ≤ ‖((s ! : ℕ) : K)⁻¹‖ * (ϱ ^ (Fintype.card ι * S))⁻¹ := by
  classical
  set a := σ r with ha
  set t := S - s - 1 with ht
  have hst : s + (t + 1) = S := by omega
  set E := Finset.univ.erase r with hE
  have hEcard : E.card + 1 = Fintype.card ι := by
    rw [hE, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ]
    exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨r⟩)
  have hd : ∀ i ∈ E, a - σ i ≠ 0 := fun i hi =>
    sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hi) (by
      by_contra hne
      have := hsep r i (Ne.symm hne)
      rw [← ha, h, sub_self, norm_zero] at this
      linarith)
  -- the product of the other factors, its Taylor shift and the inverse of the latter
  set V : K[X] := ∏ i ∈ E, (X - C (σ i)) ^ S with hV
  set Vu : K[X] := ∏ i ∈ E, (X + C (a - σ i)) ^ S with hVu
  have hVtaylor : taylor a V = Vu := by
    rw [hV, hVu, ← taylorAlgHom_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, taylorAlgHom_apply, map_sub, taylor_X, taylor_C, C_sub]
    ring
  set G : PowerSeries K := ∏ i ∈ E, (invLin (a - σ i)) ^ S with hG
  have hVG : (Vu : PowerSeries K) * G = 1 := by
    rw [hVu, hG, ← coeToPowerSeries.ringHom_apply, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i hi => ?_
    rw [map_pow, ← mul_pow, coeToPowerSeries.ringHom_apply, coe_add, coe_X, coe_C,
      X_add_C_mul_invLin (hd i hi), one_pow]
  have hGbound : ∀ k, ‖PowerSeries.coeff k G‖ ≤ (ϱ ^ (E.card * S + k))⁻¹ := by
    intro k
    have := norm_coeff_prod_le_inv_pow E hϱ0 (E := S * 1) (f := fun i => (invLin (a - σ i)) ^ S)
      (fun i hi k' => by
        have h1 := norm_coeff_pow_le_inv_pow hϱ0 (norm_coeff_invLin_le hϱ0
          (by simpa [ha] using hsep r i (Finset.ne_of_mem_erase hi).symm)) S k'
        simpa using h1) k
    simpa [hG, mul_comm] using this
  set Tu : K[X] := PowerSeries.trunc (t + 1) G with hTu
  set T : K[X] := taylor (-a) Tu with hT
  -- `V * T ≡ 1` modulo `(X - a) ^ (t + 1)`
  have hdvd : (X - C a) ^ (t + 1) ∣ V * T - 1 := by
    have hX : X ^ (t + 1) ∣ Vu * Tu - 1 := by
      rw [X_pow_dvd_iff]
      intro d hd'
      rw [coeff_sub, coeff_one]
      have hcoe : (Vu * Tu).coeff d = PowerSeries.coeff d ((Vu : PowerSeries K) * G) := by
        rw [coeff_mul, PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        have hlt : x.2 < t + 1 := by omega
        simp [Polynomial.coeff_coe, hTu, PowerSeries.coeff_trunc, hlt]
      rw [hcoe, hVG, PowerSeries.coeff_one, sub_self]
    obtain ⟨H, hH⟩ := hX
    refine ⟨taylor (-a) H, ?_⟩
    have h1 : V = taylor (-a) Vu := by rw [← hVtaylor, taylor_taylor, neg_add_cancel, taylor_zero]
    rw [h1, hT, ← taylor_mul, ← map_one (taylorAlgHom (-a)), taylorAlgHom_apply, ← map_sub, hH,
      taylor_mul, taylor_pow, taylor_X, C_neg, ← sub_eq_add_neg]
  obtain ⟨H, hH⟩ := hdvd
  set W : K[X] := C ((s ! : K)⁻¹) * (X - C a) ^ s * V * T with hW
  have hWsplit : W = C ((s ! : K)⁻¹) * (X - C a) ^ s + (X - C a) ^ S * (C ((s ! : K)⁻¹) * H) := by
    have : V * T = 1 + (X - C a) ^ (t + 1) * H := by rw [← hH]; ring
    rw [hW, mul_assoc _ V T, this, ← hst, pow_add]
    ring
  refine ⟨W, fun i j hj => ?_, fun n => ?_⟩
  · by_cases hi : i = r
    · subst hi
      rw [hWsplit, iterate_map_add, eval_add, iterate_derivative_C_mul, eval_mul, eval_C,
        iterate_derivative_eval_X_sub_C_pow,
        iterate_derivative_eval_eq_zero_of_dvd (dvd_mul_right _ _) hj, add_zero]
      by_cases hjs : j = s
      · have hf : ((s ! : ℕ) : K) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
        simp [hjs, hf]
      · simp [hjs]
    · have hne : ¬ (i = r ∧ j = s) := fun h => hi h.1
      simp only [hne, ↓reduceIte]
      refine iterate_derivative_eval_eq_zero_of_dvd ?_ hj
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) T
      rw [hV]
      exact Finset.dvd_prod_of_mem (fun i => (X - C (σ i)) ^ S) (by simp [hE, hi])
  · -- the coefficients
    have hB : 0 ≤ (ϱ ^ (Fintype.card ι * S))⁻¹ := by positivity
    have hTcoeff : ∀ k, ‖T.coeff k‖ ≤ (ϱ ^ (Fintype.card ι * S))⁻¹ := by
      intro k
      rw [hT, taylor_apply]
      refine norm_coeff_comp_le hB (fun e => ?_) (fun m => ?_) k
      · rw [hTu, PowerSeries.coeff_trunc]
        split_ifs with he
        · refine (hGbound e).trans (inv_anti₀ (pow_pos hϱ0 _)
            (pow_le_pow_of_le_one hϱ0.le hϱ1 ?_))
          rw [← hEcard, add_mul, one_mul]
          omega
        · simpa using hB
      · rw [C_neg, ← sub_eq_add_neg]
        exact norm_coeff_X_sub_C_le_one (by simpa [ha] using hσ r) m
    have hXa : ∀ m, ‖((X - C a) ^ s).coeff m‖ ≤ 1 :=
      norm_coeff_pow_le_one (norm_coeff_X_sub_C_le_one (by simpa [ha] using hσ r)) s
    have hVc : ∀ m, ‖V.coeff m‖ ≤ 1 := norm_coeff_prod_le_one E fun i _ =>
      norm_coeff_pow_le_one (norm_coeff_X_sub_C_le_one (hσ i)) S
    rw [hW, mul_assoc, mul_assoc, coeff_C_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← mul_assoc]
    simpa using norm_coeff_mul_le zero_le_one hB
      (fun m => by simpa using norm_coeff_mul_le zero_le_one zero_le_one hXa hVc m) hTcoeff n

end Main

end PadicBaker
