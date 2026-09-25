/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Exp
public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Series
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Exponential polynomials as power series

The function `Q (z) * exp (ψ z)`, for a polynomial `Q` and a number `ψ`, is recorded by the
coefficients `PadicBaker.expPolySeq Q ψ` of the formal power series `Q * exp (ψ X)`, built from
Mathlib's `PowerSeries.exp`. The formal derivative acts by `Q ↦ Q' + ψ Q`
(`PadicBaker.seqDeriv_expPolySeq`), the coefficients inherit the bounds of those of `Q` at any
radius `r` with `‖ψ‖ r` inside the disc of convergence of the exponential
(`PadicBaker.norm_expPolySeq_mul_pow_le`), and over `ℂ_[p]` the series sums to
`Q (x) * exp (ψ x)` (`PadicBaker.hasSum_expPolySeq`).

The polynomials that occur in Baker's auxiliary function are iterates of `Q ↦ Q' + c Q` applied to a
monomial; `PadicBaker.norm_coeff_iterate_derivAdd_le` bounds their coefficients.
-/

@[expose] public section

open Nat

namespace PadicBaker

section Poly

variable {R : Type*} [CommRing R]

/-- The polynomial `(Q ↦ Q' + c Q)^[m] P`. -/
noncomputable def derivAdd (c : R) (m : ℕ) (P : Polynomial R) : Polynomial R :=
  (fun Q => Polynomial.derivative Q + Polynomial.C c * Q)^[m] P

theorem derivAdd_succ (c : R) (m : ℕ) (P : Polynomial R) :
    derivAdd c (m + 1) P = Polynomial.derivative (derivAdd c m P) +
      Polynomial.C c * derivAdd c m P := by
  simp only [derivAdd, Function.iterate_succ_apply']

theorem derivAdd_smul (c a : R) (m : ℕ) (P : Polynomial R) :
    derivAdd c m (a • P) = a • derivAdd c m P := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [derivAdd_succ, derivAdd_succ, ih, Polynomial.derivative_smul, smul_add, mul_smul_comm]

theorem natDegree_derivAdd_le (c : R) (m : ℕ) (P : Polynomial R) :
    (derivAdd c m P).natDegree ≤ P.natDegree := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [derivAdd_succ]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans ih)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans ih

theorem map_derivAdd {S : Type*} [CommRing S] (f : R →+* S) (c : R) (m : ℕ) (P : Polynomial R) :
    (derivAdd c m P).map f = derivAdd (f c) m (P.map f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [derivAdd_succ, derivAdd_succ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map, ih]

end Poly

section Formal

variable {K : Type*} [NontriviallyNormedField K] [CharZero K]

/-- The formal power series of `exp (ψ z)`. -/
noncomputable def expSer (ψ : K) : PowerSeries K := PowerSeries.rescale ψ (PowerSeries.exp K)

theorem coeff_expSer (ψ : K) (n : ℕ) :
    PowerSeries.coeff n (expSer ψ) = ψ ^ n * ((n ! : ℕ) : K)⁻¹ := by
  simp [expSer, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

theorem derivative_expSer (ψ : K) :
    PowerSeries.derivative (R := K) (expSer ψ) = PowerSeries.C ψ * expSer ψ := by
  ext n
  have h1 : ((n ! : ℕ) : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : K) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [PowerSeries.coeff_derivative, coeff_expSer, PowerSeries.coeff_C_mul, coeff_expSer,
    Nat.factorial_succ, Nat.cast_mul, pow_succ]
  push_cast
  field_simp

/-- The coefficients of `Q (z) * exp (ψ z)`. -/
noncomputable def expPolySeq (Q : Polynomial K) (ψ : K) : ℕ → K :=
  fun k => PowerSeries.coeff k ((Q : PowerSeries K) * expSer ψ)

theorem expPolySeq_apply (Q : Polynomial K) (ψ : K) (k : ℕ) :
    expPolySeq Q ψ k =
      ∑ x ∈ Finset.antidiagonal k, Q.coeff x.1 * (ψ ^ x.2 * ((x.2 ! : ℕ) : K)⁻¹) := by
  simp [expPolySeq, PowerSeries.coeff_mul, Polynomial.coeff_coe, coeff_expSer]

theorem expPolySeq_add (Q₁ Q₂ : Polynomial K) (ψ : K) :
    expPolySeq (Q₁ + Q₂) ψ = expPolySeq Q₁ ψ + expPolySeq Q₂ ψ := by
  funext k; simp [expPolySeq, add_mul]

theorem expPolySeq_smul (a : K) (Q : Polynomial K) (ψ : K) :
    expPolySeq (a • Q) ψ = a • expPolySeq Q ψ := by
  funext k
  simp [expPolySeq, Polynomial.smul_eq_C_mul, mul_assoc, PowerSeries.coeff_C_mul]

theorem expPolySeq_zero (ψ : K) : expPolySeq (0 : Polynomial K) ψ = 0 := by
  funext k; simp [expPolySeq]

/-- The formal derivative of `Q (z) * exp (ψ z)` is `(Q' (z) + ψ Q (z)) * exp (ψ z)`. -/
theorem seqDeriv_expPolySeq (Q : Polynomial K) (ψ : K) :
    seqDeriv (expPolySeq Q ψ) =
      expPolySeq (Polynomial.derivative Q + Polynomial.C ψ * Q) ψ := by
  funext k
  have h : PowerSeries.derivative (R := K) ((Q : PowerSeries K) * expSer ψ) =
      ((Polynomial.derivative Q + Polynomial.C ψ * Q : Polynomial K) : PowerSeries K) *
        expSer ψ := by
    rw [Derivation.leibniz, derivative_expSer, PowerSeries.derivative_coe, smul_eq_mul, smul_eq_mul,
      Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C]
    ring
  simp only [seqDeriv, expPolySeq]
  rw [← h, PowerSeries.coeff_derivative, mul_comm, Nat.cast_succ]

end Formal

section Normed

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Coefficients of an exponential polynomial.** If `‖Q.coeff i‖ * r ^ i ≤ B` and `‖ψ‖ r` lies in
the disc where `‖ψ ^ j / j!‖ r ^ j ≤ 1`, then `‖expPolySeq Q ψ k‖ * r ^ k ≤ B`. -/
theorem norm_expPolySeq_mul_pow_le [CharZero K] {Q : Polynomial K} {ψ : K} {r B : ℝ} (hr : 0 < r)
    (hB : 0 ≤ B) (hQ : ∀ i, ‖Q.coeff i‖ * r ^ i ≤ B)
    (hψ : ∀ j, ‖((j ! : ℕ) : K)⁻¹‖ * (‖ψ‖ * r) ^ j ≤ 1) (k : ℕ) :
    ‖expPolySeq Q ψ k‖ * r ^ k ≤ B := by
  rw [← le_div_iff₀ (pow_pos hr k), expPolySeq_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [le_div_iff₀ (pow_pos hr k), ← hx, pow_add, norm_mul, norm_mul, norm_pow]
  calc ‖Q.coeff x.1‖ * (‖ψ‖ ^ x.2 * ‖((x.2 ! : ℕ) : K)⁻¹‖) * (r ^ x.1 * r ^ x.2)
      = (‖Q.coeff x.1‖ * r ^ x.1) * (‖((x.2 ! : ℕ) : K)⁻¹‖ * (‖ψ‖ * r) ^ x.2) := by ring
    _ ≤ B * 1 := by
        gcongr
        · exact hQ _
        · exact hψ _
    _ = B := mul_one B

/-- **Coefficients of the iterates of `Q ↦ Q' + c Q`.** -/
theorem norm_coeff_derivAdd_le (c : K) {P : Polynomial K} {B : ℝ}
    (hP : ∀ i, ‖P.coeff i‖ ≤ B) (m : ℕ) (i : ℕ) :
    ‖(derivAdd c m P).coeff i‖ ≤ max 1 ‖c‖ ^ m * B := by
  induction m generalizing i with
  | zero => simpa [derivAdd] using hP i
  | succ m ih =>
    rw [derivAdd_succ, Polynomial.coeff_add, Polynomial.coeff_derivative, Polynomial.coeff_C_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      have hB : 0 ≤ max 1 ‖c‖ ^ m * B := (norm_nonneg _).trans (ih 0)
      have hi1 : ‖(i : K) + 1‖ ≤ 1 := by
        exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (i + 1)
      calc ‖(derivAdd c m P).coeff (i + 1)‖ * ‖(i : K) + 1‖
          ≤ max 1 ‖c‖ ^ m * B * 1 := mul_le_mul (ih _) hi1 (norm_nonneg _) hB
        _ ≤ max 1 ‖c‖ ^ (m + 1) * B := by
            rw [mul_one, pow_succ, mul_right_comm]
            exact le_mul_of_one_le_right hB (le_max_left _ _)
    · rw [norm_mul]
      calc ‖c‖ * ‖(derivAdd c m P).coeff i‖ ≤ max 1 ‖c‖ * (max 1 ‖c‖ ^ m * B) :=
            mul_le_mul (le_max_right _ _) (ih _) (norm_nonneg _)
              (zero_le_one.trans (le_max_left _ _))
        _ = max 1 ‖c‖ ^ (m + 1) * B := by ring

end Normed

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The value of an exponential polynomial.** Over `ℂ_[p]`, the series with coefficients
`expPolySeq Q ψ` sums to `Q (x) * exp (ψ x)` when `ψ x` lies in the disc of convergence of `exp`. -/
theorem hasSum_expPolySeq (Q : Polynomial ℂ_[p]) {ψ x : ℂ_[p]}
    (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun k => expPolySeq Q ψ k * x ^ k) (Q.eval x * NormedSpace.exp (ψ * x)) := by
  classical
  have hexp := NormedSpace.expSeries_div_hasSum_exp_of_mem_ball ℂ_[p] (ψ * x)
    (PadicComplex.mem_eball_radius_expSeries h)
  -- the monomial case
  have hmono : ∀ i (a : ℂ_[p]), HasSum (fun k => expPolySeq (Polynomial.monomial i a) ψ k * x ^ k)
      (a * x ^ i * NormedSpace.exp (ψ * x)) := by
    intro i a
    have hshift : HasSum (fun j => expPolySeq (Polynomial.monomial i a) ψ (j + i) * x ^ (j + i))
        (a * x ^ i * NormedSpace.exp (ψ * x)) := by
      refine (hexp.mul_left (a * x ^ i)).congr_fun fun j => ?_
      rw [expPolySeq_apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_eq_single i]
      · simp only [Polynomial.coeff_monomial, ↓reduceIte, show j + i - i = j by omega]
        rw [mul_pow, pow_add, div_eq_mul_inv]
        ring
      · intro b _ hb
        simp [Polynomial.coeff_monomial, Ne.symm hb]
      · intro hi
        exact absurd (Finset.mem_range.mpr (by omega)) hi
    have hzero : ∑ k ∈ Finset.range i, expPolySeq (Polynomial.monomial i a) ψ k * x ^ k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [expPolySeq_apply, Finset.sum_eq_zero, zero_mul]
      intro y hy
      rw [Finset.mem_antidiagonal] at hy
      have : ¬ (i = y.1) := by omega
      simp [Polynomial.coeff_monomial, this]
    have := (hasSum_nat_add_iff' (f := fun k => expPolySeq (Polynomial.monomial i a) ψ k * x ^ k)
      i).mp (by rwa [hzero, sub_zero])
    exact this
  -- sum over the monomials of `Q`
  have hQ : Q = ∑ i ∈ Finset.range (Q.natDegree + 1), Polynomial.monomial i (Q.coeff i) :=
    Q.as_sum_range
  have hlin : ∀ k, expPolySeq Q ψ k =
      ∑ i ∈ Finset.range (Q.natDegree + 1), expPolySeq (Polynomial.monomial i (Q.coeff i)) ψ k := by
    intro k
    conv_lhs => rw [hQ]
    induction (Finset.range (Q.natDegree + 1)) using Finset.induction_on with
    | empty => simp [expPolySeq_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, expPolySeq_add, Pi.add_apply, ih,
        Finset.sum_insert ha]
  have hsum := hasSum_sum (s := Finset.range (Q.natDegree + 1)) fun i _ => hmono i (Q.coeff i)
  rw [← Finset.sum_mul, ← Q.eval_eq_sum_range] at hsum
  refine hsum.congr_fun fun k => ?_
  rw [hlin, Finset.sum_mul]

end Padic

end PadicBaker
