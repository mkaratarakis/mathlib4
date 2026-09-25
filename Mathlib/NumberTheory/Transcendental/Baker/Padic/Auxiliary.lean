/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Padic.ExpSeries

/-!
# Baker's auxiliary function over `ℂ_[p]`

Baker–Masser, *Transcendental Number Theory*, Chapter 2, §§3–4, transplanted to `ℂ_[p]`. Suppose
`ℓ none = β₀ + ∑_r β r * ℓ (some r)` for logarithms `ℓ o` (`o : Option (Fin k)`, the value `none`
standing for Baker's `log αₙ`). For integers `P (d, e)` Baker's auxiliary function of `k + 1`
variables is `Φ (z₀, z) = ∑ P (d, e) z₀ ^ d exp (e none β₀ z₀) ∏_r exp (γ_r ℓ (some r) z_r)`, with
`γ_r = e (some r) + e none β r` and `z` indexed by `r : Fin k`.
Only its derivatives on the diagonal `z₀ = z_r = z` enter the proof, and these are the functions of
one variable
`f_m (z) = ∑ P (d, e) (∏_r (γ_r ℓ_r) ^ {m_r}) ((D + c) ^ {m₀} X ^ d) (z) exp (ψ_e z)`,
with `γ_r = e_r + e_none β_r`, `c = e_none β₀` and `ψ_e = ∑_o e_o ℓ_o`. We record `f_m` by its
coefficient sequence `PadicBaker.aux`.

## Main statements

* `PadicBaker.seqDeriv_aux`: `D f_m = ∑_o f_{m + e_o}` (the chain rule on the diagonal), which
  uses the relation.
* `PadicBaker.norm_aux_mul_pow_le`: the coefficients of `f_m` at radius `r₀`.
* `PadicBaker.seqEval_iterate_seqDeriv_aux_eq_zero`: vanishing of the `f_m` at a point propagates to
  their derivatives.
* `PadicBaker.seqEval_aux_natCast`: the value of `f_m` at an integer, a product of powers of the
  `ℓ` and an algebraic expression in the `α = exp ℓ`, `β` and `P`.
* `PadicBaker.sum_coeff_mul_factorial_aux_zero`: the identity behind Baker's final step (§5).
-/

@[expose] public section

open Polynomial Nat

namespace PadicBaker

variable {p : ℕ} [hp : Fact p.Prime] {k : ℕ}

section Defs

variable (ℓ : Option (Fin k) → ℂ_[p]) (β₀ : ℂ_[p]) (β : Fin k → ℂ_[p])

/-- `ψ_e = ∑_o e_o ℓ_o`. -/
noncomputable def psi (e : Option (Fin k) → ℕ) : ℂ_[p] := ∑ o, (e o : ℂ_[p]) * ℓ o

/-- `γ_r = e_r + e_none β_r`. -/
noncomputable def gam (e : Option (Fin k) → ℕ) (r : Fin k) : ℂ_[p] :=
  (e (some r) : ℂ_[p]) + (e none : ℂ_[p]) * β r

/-- `c = e_none β₀`. -/
noncomputable def cc (e : Option (Fin k) → ℕ) : ℂ_[p] := (e none : ℂ_[p]) * β₀

/-- Baker's polynomial `(∏_r (γ_r ℓ_r) ^ {m_r}) • (D + c) ^ {m₀} X ^ d`. -/
noncomputable def Qpoly (m : Option (Fin k) → ℕ) (d : ℕ) (e : Option (Fin k) → ℕ) :
    ℂ_[p][X] :=
  (∏ r, (gam β e r * ℓ (some r)) ^ m (some r)) • derivAdd (cc β₀ e) (m none) (X ^ d)

/-- The derivative `f_m` of Baker's auxiliary function on the diagonal, as a coefficient sequence.
The index `(d, e)` runs over `d ≤ L` and `e o ≤ L`. -/
noncomputable def aux (L : ℕ) (P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p])
    (m : Option (Fin k) → ℕ) : ℕ → ℂ_[p] :=
  ∑ x, P x • expPolySeq (Qpoly ℓ β₀ β m x.1 fun o => x.2 o) (psi ℓ fun o => x.2 o)

end Defs

section Algebra

variable {ℓ : Option (Fin k) → ℂ_[p]} {β₀ : ℂ_[p]} {β : Fin k → ℂ_[p]}

theorem psi_eq (hrel : ℓ none = β₀ + ∑ r, β r * ℓ (some r)) (e : Option (Fin k) → ℕ) :
    psi ℓ e = cc β₀ e + ∑ r, gam β e r * ℓ (some r) := by
  rw [psi, cc, Fintype.sum_option, hrel]
  simp only [gam, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_assoc]
  ring

theorem prod_pow_add_single {M : Type*} [CommMonoid M] (f : Fin k → M)
    (m : Option (Fin k) → ℕ) (r : Fin k) :
    ∏ r', f r' ^ (m + (Pi.single (some r) 1 : Option (Fin k) → ℕ)) (some r') =
      f r * ∏ r', f r' ^ m (some r') := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
    ← Finset.mul_prod_erase Finset.univ (fun r' => f r' ^ m (some r')) (Finset.mem_univ r)]
  have hr : (m + (Pi.single (some r) 1 : Option (Fin k) → ℕ)) (some r) = m (some r) + 1 := by simp
  rw [hr, pow_succ, mul_comm (f r ^ m (some r)) (f r), mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun r' hr' => ?_
  have hne : (some r' : Option (Fin k)) ≠ some r := by
    simpa using Finset.ne_of_mem_erase hr'
  simp [hne]

/-- **The chain rule on the diagonal.** -/
theorem derivative_add_Qpoly (hrel : ℓ none = β₀ + ∑ r, β r * ℓ (some r))
    (m : Option (Fin k) → ℕ) (d : ℕ) (e : Option (Fin k) → ℕ) :
    derivative (Qpoly ℓ β₀ β m d e) + C (psi ℓ e) * Qpoly ℓ β₀ β m d e =
      ∑ o, Qpoly ℓ β₀ β (m + (Pi.single o 1 : Option (Fin k) → ℕ)) d e := by
  classical
  set Pr := ∏ r, (gam β e r * ℓ (some r)) ^ m (some r) with hPr
  set D := derivAdd (cc β₀ e) (m none) (X ^ d) with hD
  have hnone : Qpoly ℓ β₀ β (m + (Pi.single none 1 : Option (Fin k) → ℕ)) d e =
      Pr • (derivative D + C (cc β₀ e) * D) := by
    have h1 : ∏ r, (gam β e r * ℓ (some r)) ^
        (m + (Pi.single none 1 : Option (Fin k) → ℕ)) (some r) = Pr := by
      refine Finset.prod_congr rfl fun r _ => ?_
      simp
    have h2 : (m + (Pi.single none 1 : Option (Fin k) → ℕ)) none = m none + 1 := by simp
    simp only [Qpoly]
    rw [h1, h2, derivAdd_succ]
  have hsome : ∀ r, Qpoly ℓ β₀ β (m + (Pi.single (some r) 1 : Option (Fin k) → ℕ)) d e =
      (gam β e r * ℓ (some r) * Pr) • D := by
    intro r
    have h2 : (m + (Pi.single (some r) 1 : Option (Fin k) → ℕ)) none = m none := by simp
    simp only [Qpoly]
    rw [prod_pow_add_single, h2]
  have hsum : ∑ r, (gam β e r * ℓ (some r) * Pr) • D =
      C Pr * (C (∑ r, gam β e r * ℓ (some r)) * D) := by
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_eq_C_mul, map_mul, map_mul]
    ring
  rw [Fintype.sum_option, hnone, Finset.sum_congr rfl fun r _ => hsome r, hsum, psi_eq hrel]
  simp only [Qpoly, ← hPr, ← hD, smul_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add,
    map_add]
  ring

theorem expPolySeq_sum {ι : Type*} (s : Finset ι) (Q : ι → ℂ_[p][X]) (ψ : ℂ_[p]) :
    expPolySeq (∑ i ∈ s, Q i) ψ = ∑ i ∈ s, expPolySeq (Q i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expPolySeq_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, expPolySeq_add, ih]

theorem seqDeriv_sum {ι : Type*} (s : Finset ι) (c : ι → ℕ → ℂ_[p]) :
    seqDeriv (∑ i ∈ s, c i) = ∑ i ∈ s, seqDeriv (c i) := by
  funext j; simp [seqDeriv, Finset.mul_sum]

theorem seqDeriv_smul (a : ℂ_[p]) (c : ℕ → ℂ_[p]) : seqDeriv (a • c) = a • seqDeriv c := by
  funext j; simp only [seqDeriv, Pi.smul_apply, smul_eq_mul]; ring

/-- **`D f_m = ∑_o f_{m + e_o}`.** -/
theorem seqDeriv_aux (hrel : ℓ none = β₀ + ∑ r, β r * ℓ (some r)) (L : ℕ)
    (P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p]) (m : Option (Fin k) → ℕ) :
    seqDeriv (aux ℓ β₀ β L P m) =
      ∑ o, aux ℓ β₀ β L P (m + (Pi.single o 1 : Option (Fin k) → ℕ)) := by
  simp only [aux, seqDeriv_sum, seqDeriv_smul, seqDeriv_expPolySeq, derivative_add_Qpoly hrel,
    expPolySeq_sum, Finset.smul_sum]
  exact Finset.sum_comm

end Algebra

section Analysis

variable {ℓ : Option (Fin k) → ℂ_[p]} {β₀ : ℂ_[p]} {β : Fin k → ℂ_[p]}

theorem norm_psi_le {R : ℝ} (hR : 0 ≤ R) (hℓ : ∀ o, ‖ℓ o‖ ≤ R)
    (e : Option (Fin k) → ℕ) : ‖psi ℓ e‖ ≤ R := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR fun o _ => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
    (hℓ o)

/-- **The coefficients of `f_m`** at a radius `r₀ ≥ 1` with `‖ℓ o‖ r₀` inside the disc of
convergence of `exp`. -/
theorem norm_aux_mul_pow_le {L : ℕ} {r₀ B : ℝ} (hr₀ : 1 ≤ r₀) (hB : 1 ≤ B)
    (hℓ : ∀ o, ‖ℓ o‖ * r₀ ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (hℓ1 : ∀ o, ‖ℓ o‖ ≤ 1)
    (hβ : ∀ r, ‖β r‖ ≤ B) (hβ₀ : ‖β₀‖ ≤ B)
    {P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p]} (hP : ∀ x, ‖P x‖ ≤ 1)
    (m : Option (Fin k) → ℕ) (j : ℕ) :
    ‖aux ℓ β₀ β L P m j‖ * r₀ ^ j ≤ B ^ (∑ o, m o) * r₀ ^ L := by
  classical
  have hr0 : 0 < r₀ := zero_lt_one.trans_le hr₀
  have hBd : 0 ≤ B ^ (∑ o, m o) * r₀ ^ L := by positivity
  rw [← le_div_iff₀ (pow_pos hr0 j), aux, Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, le_div_iff₀ (pow_pos hr0 j)]
  set e : Option (Fin k) → ℕ := fun o => x.2 o with he
  have hρ : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  -- the bound for `ψ`
  have hψ : ∀ j', ‖((j' ! : ℕ) : ℂ_[p])⁻¹‖ * (‖psi ℓ e‖ * r₀) ^ j' ≤ 1 := by
    intro j'
    have hψr : ‖psi ℓ e‖ * r₀ ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [← le_div_iff₀ hr0]
      exact norm_psi_le (by positivity) (fun o => by rw [le_div_iff₀ hr0]; exact hℓ o) e
    calc ‖((j' ! : ℕ) : ℂ_[p])⁻¹‖ * (‖psi ℓ e‖ * r₀) ^ j'
        ≤ ‖((j' ! : ℕ) : ℂ_[p])⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ j' := by gcongr
      _ ≤ 1 := PadicComplex.norm_factorial_inv_mul_pow_le j'
  -- the bound for the polynomial
  have hγ : ∀ r, ‖gam β e r * ℓ (some r)‖ ≤ B := by
    intro r
    rw [norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) (hℓ1 _)).trans ?_
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (IsUltrametricDist.norm_natCast_le_one _ _).trans hB
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (IsUltrametricDist.norm_natCast_le_one _ _)).trans (hβ r)
  have hc : max 1 ‖cc β₀ e‖ ≤ B := by
    refine max_le hB ?_
    rw [cc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
      hβ₀
  have hQ : ∀ i, ‖(Qpoly ℓ β₀ β m x.1 e).coeff i‖ * r₀ ^ i ≤ B ^ (∑ o, m o) * r₀ ^ L := by
    intro i
    rw [Qpoly, coeff_smul, smul_eq_mul, norm_mul, norm_prod]
    by_cases hi : i ≤ (x.1 : ℕ)
    · have hD := norm_coeff_derivAdd_le (cc β₀ e) (P := (X ^ (x.1 : ℕ) : ℂ_[p][X]))
        (B := 1) (fun i' => by rw [coeff_X_pow]; split_ifs <;> simp) (m none) i
      have hprod : ∏ r, ‖(gam β e r * ℓ (some r)) ^ m (some r)‖ ≤ B ^ (∑ r, m (some r)) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        simp only [norm_pow]
        gcongr with r
        exact hγ r
      have hD' : ‖(derivAdd (cc β₀ e) (m none) (X ^ (x.1 : ℕ))).coeff i‖ ≤ B ^ m none := by
        refine hD.trans ?_
        rw [mul_one]
        exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hc _
      have hri : r₀ ^ i ≤ r₀ ^ L := pow_le_pow_right₀ hr₀ (hi.trans (Nat.lt_succ_iff.mp x.1.2))
      rw [Fintype.sum_option, pow_add, mul_comm (B ^ m none)]
      exact mul_le_mul (mul_le_mul hprod hD' (norm_nonneg _) (by positivity)) hri (by positivity)
        (by positivity)
    · have hlt : (derivAdd (cc β₀ e) (m none) (X ^ (x.1 : ℕ) : ℂ_[p][X])).natDegree < i :=
        (natDegree_derivAdd_le _ _ _).trans_lt (by rw [natDegree_X_pow]; omega)
      rw [coeff_eq_zero_of_natDegree_lt hlt, norm_zero, mul_zero, zero_mul]
      exact hBd
  calc ‖P x‖ * ‖expPolySeq (Qpoly ℓ β₀ β m x.1 e) (psi ℓ e) j‖ * r₀ ^ j
      ≤ 1 * (‖expPolySeq (Qpoly ℓ β₀ β m x.1 e) (psi ℓ e) j‖ * r₀ ^ j) := by
        rw [mul_assoc]; gcongr; exact hP x
    _ ≤ 1 * (B ^ (∑ o, m o) * r₀ ^ L) :=
        mul_le_mul_of_nonneg_left (norm_expPolySeq_mul_pow_le hr0 hBd hQ hψ j) zero_le_one
    _ = B ^ (∑ o, m o) * r₀ ^ L := one_mul _

theorem seqEval_sum {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℂ_[p]} {x : ℂ_[p]}
    (hc : ∀ i ∈ s, Summable fun n => c i n * x ^ n) :
    seqEval (∑ i ∈ s, c i) x = ∑ i ∈ s, seqEval (c i) x := by
  simp only [seqEval, Finset.sum_apply, Finset.sum_mul]
  exact Summable.tsum_finsetSum hc

/-- **Vanishing propagates to derivatives.** If `f_m (x) = 0` whenever `∑ m ≤ S'`, then the
`j`-th formal derivative of `f_m` vanishes at `x` whenever `∑ m + j ≤ S'`. -/
theorem seqEval_iterate_seqDeriv_aux_eq_zero (hrel : ℓ none = β₀ + ∑ r, β r * ℓ (some r))
    {L : ℕ} {P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p]} {x : ℂ_[p]}
    (hsum : ∀ m j, Summable fun n => (seqDeriv^[j] (aux ℓ β₀ β L P m)) n * x ^ n) {S' : ℕ}
    (h0 : ∀ m, ∑ o, m o ≤ S' → seqEval (aux ℓ β₀ β L P m) x = 0) :
    ∀ j m, ∑ o, m o + j ≤ S' → seqEval (seqDeriv^[j] (aux ℓ β₀ β L P m)) x = 0 := by
  intro j
  induction j with
  | zero => intro m hm; simpa using h0 m (by simpa using hm)
  | succ j ih =>
    intro m hm
    rw [Function.iterate_succ_apply, seqDeriv_aux hrel, iterate_seqDeriv_sum,
      seqEval_sum _ fun o _ => hsum _ _]
    refine Finset.sum_eq_zero fun o _ => ih _ ?_
    have : ∑ o', (m + (Pi.single o 1 : Option (Fin k) → ℕ)) o' = ∑ o', m o' + 1 := by
      simp [Finset.sum_add_distrib]
    omega

/-- **The value of `f_m` at an integer.** -/
theorem seqEval_aux_natCast (hsmall : ∀ o, ‖ℓ o‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (L : ℕ)
    (P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p]) (m : Option (Fin k) → ℕ)
    (l : ℕ) :
    seqEval (aux ℓ β₀ β L P m) (l : ℂ_[p]) = (∏ r, ℓ (some r) ^ m (some r)) *
      ∑ x : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)), P x *
        ((∏ r, gam β (fun o => x.2 o) r ^ m (some r)) *
          (derivAdd (cc β₀ fun o => x.2 o) (m none) (X ^ (x.1 : ℕ))).eval (l : ℂ_[p])) *
        ∏ o, NormedSpace.exp (ℓ o) ^ ((x.2 o : ℕ) * l) := by
  classical
  have hρ : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  set R := Finset.univ.sup' Finset.univ_nonempty fun o => ‖ℓ o‖ with hRdef
  have hR : ∀ o, ‖ℓ o‖ ≤ R := fun o => Finset.le_sup' (fun o => ‖ℓ o‖) (Finset.mem_univ o)
  have hRlt : R < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    (Finset.sup'_lt_iff _).mpr fun o _ => hsmall o
  have hl : ‖(l : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hterm : ∀ x : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)),
      HasSum (fun n => (P x • expPolySeq (Qpoly ℓ β₀ β m x.1 fun o => x.2 o)
        (psi ℓ fun o => x.2 o)) n * (l : ℂ_[p]) ^ n)
        (P x * ((Qpoly ℓ β₀ β m x.1 fun o => x.2 o).eval (l : ℂ_[p]) *
          NormedSpace.exp (psi ℓ (fun o => x.2 o) * l))) := by
    intro x
    have hψl : ‖psi ℓ (fun o => x.2 o) * l‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hl).trans_lt
        ((norm_psi_le ((norm_nonneg _).trans (hR none)) hR _).trans_lt hRlt)
    have := (hasSum_expPolySeq (Qpoly ℓ β₀ β m x.1 fun o => x.2 o) hψl).mul_left (P x)
    refine this.congr_fun fun n => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hall := hasSum_sum (s := Finset.univ) fun x _ => hterm x
  rw [seqEval, aux]
  simp only [Finset.sum_apply, Finset.sum_mul] at hall ⊢
  rw [hall.tsum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- `exp (ψ_e l) = ∏_o exp (ℓ_o) ^ (e_o l)`
  have hexp : NormedSpace.exp (psi ℓ (fun o => x.2 o) * l) =
      ∏ o, NormedSpace.exp (ℓ o) ^ ((x.2 o : ℕ) * l) := by
    have hsplit : psi ℓ (fun o => x.2 o) * l = ∑ o, ((x.2 o : ℕ) * l) • ℓ o := by
      simp only [psi, Finset.sum_mul, nsmul_eq_mul]
      refine Finset.sum_congr rfl fun o _ => ?_
      push_cast; ring
    rw [hsplit, PadicComplex.exp_sum _ fun o _ => PadicComplex.norm_nsmul_lt_expRadius
      (hsmall o) _]
    exact Finset.prod_congr rfl fun o _ => PadicComplex.exp_nsmul (hsmall o) _
  rw [hexp, Qpoly, eval_smul, smul_eq_mul]
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

/-- `n! * [z ^ n] (z ^ d exp (ψ z)) = (D ^ d X ^ n) (ψ)`. -/
theorem factorial_mul_expPolySeq_X_pow (d n : ℕ) (ψ : ℂ_[p]) :
    (n ! : ℂ_[p]) * expPolySeq (X ^ d) ψ n = (derivative^[d] (X ^ n : ℂ_[p][X])).eval ψ := by
  rw [expPolySeq_apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iterate_derivative_X_pow_eq_smul, eval_smul, eval_X_pow, smul_eq_mul]
  by_cases hdn : d ≤ n
  · rw [Finset.sum_eq_single d]
    · simp only [coeff_X_pow, ↓reduceIte, one_mul]
      have hf : ((n - d)! : ℂ_[p]) ≠ 0 := by exact_mod_cast (n - d).factorial_ne_zero
      rw [← Nat.factorial_mul_descFactorial hdn]
      push_cast
      field_simp
    · intro b _ hb
      simp [coeff_X_pow, hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Finset.sum_eq_zero, (Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
    · simp
    · intro b hb
      rw [Finset.mem_range] at hb
      have : ¬ (b = d) := by omega
      simp [coeff_X_pow, this]

/-- **The identity behind Baker's final step.** For every polynomial `W`,
`∑ n, W_n n! [z ^ n] f_0 = ∑_{(d, e)} P (d, e) W^{(d)} (ψ_e)`. -/
theorem sum_coeff_mul_factorial_aux_zero (L : ℕ)
    (P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p]) (W : ℂ_[p][X]) :
    ∑ n ∈ Finset.range (W.natDegree + 1), W.coeff n * (n ! : ℂ_[p]) * aux ℓ β₀ β L P 0 n =
      ∑ x : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)),
        P x * (derivative^[(x.1 : ℕ)] W).eval (psi ℓ fun o => x.2 o) := by
  have hQ0 : ∀ (d : ℕ) (e : Option (Fin k) → ℕ), Qpoly ℓ β₀ β 0 d e = X ^ d := by
    intro d e; simp [Qpoly, derivAdd]
  simp only [aux, hQ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hW : (derivative^[(x.1 : ℕ)] W).eval (psi ℓ fun o => x.2 o) =
      ∑ n ∈ Finset.range (W.natDegree + 1),
        W.coeff n * (derivative^[(x.1 : ℕ)] (X ^ n : ℂ_[p][X])).eval (psi ℓ fun o => x.2 o) := by
    conv_lhs => rw [W.as_sum_range_C_mul_X_pow]
    rw [← Module.End.pow_apply, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.End.pow_apply, iterate_derivative_C_mul, eval_mul, eval_C]
  rw [hW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← factorial_mul_expPolySeq_X_pow]
  ring

end Analysis

end PadicBaker
