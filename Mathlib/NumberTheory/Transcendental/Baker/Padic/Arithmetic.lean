/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.Transcendental.Baker.AlgSize
public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Auxiliary
public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Liouville

/-!
# The arithmetic of Baker's auxiliary function over `ℂ_[p]`

The values `f_m (l)` of the auxiliary function at integers are, up to the transcendental factor
`∏ ℓ ^ m`, the images of elements `PadicBaker.Aval` of a number field `K` containing the
`α = exp ℓ` and the `β`. This file computes their sizes (Baker–Masser, Chapter 2, Lemma 3),
constructs the auxiliary function by Siegel's lemma over `K` (Lemma 2, with Mathlib's
`NumberField.house.exists_ne_zero_int_vec_house_le`), and turns sizes into lower bounds at the
`p`-adic place (`NumberField.one_le_pow_mul_norm_embedding`).

## Main statements

* `PadicBaker.seqEval_aux_natCast_eq`: `f_m (l) = (∏ ℓ ^ m) * ι (Aval m l)`.
* `PadicBaker.algSize_Aval`: the size of `Aval m l`.
* `PadicBaker.exists_siegel`: Siegel's lemma with a constant depending only on the field.
* `PadicBaker.exists_aux_vanishing`: Baker's Lemma 2 over `ℂ_[p]`.
-/

@[expose] public section

open Polynomial NumberField Nat

namespace NumberField.AlgSize

variable {K : Type*} [Field K] [NumberField K] {δ : ℕ} {α : K} {a b : ℕ} {H G : ℝ}

/-- Raising the exponent of the denominator when `δ ≤ G`. -/
lemma raise_le (h : AlgSize δ α a H) (hab : a ≤ b) (hδG : (δ : ℝ) ≤ G) :
    AlgSize δ α b (G ^ (b - a) * H) :=
  (h.raise hab).mono (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg δ) hδG _)
    h.nonneg)

lemma natCast_one (n : ℕ) : AlgSize δ (n : K) 1 ((δ : ℝ) * n) := by
  simpa using (natCast (δ := δ) (K := K) n).raise (Nat.zero_le 1)

end NumberField.AlgSize

namespace PadicBaker

variable {p : ℕ} [hp : Fact p.Prime] {k : ℕ}

section Field

variable {K : Type*} [Field K] [NumberField K] (αK : Option (Fin k) → K) (βK₀ : K)
  (βK : Fin k → K)

/-- `γ_r = e_r + e_none β_r` in `K`. -/
def gamK (e : Option (Fin k) → ℕ) (r : Fin k) : K := (e (some r) : K) + (e none : K) * βK r

/-- `c = e_none β₀` in `K`. -/
def ccK (e : Option (Fin k) → ℕ) : K := (e none : K) * βK₀

/-- The algebraic part of `(∏_r (γ_r ℓ_r) ^ {m_r}) ((D + c) ^ {m₀} X ^ d) (l)`. -/
noncomputable def evalK (m : Option (Fin k) → ℕ) (d : ℕ) (e : Option (Fin k) → ℕ) (l : ℕ) : K :=
  (∏ r, gamK βK e r ^ m (some r)) * (derivAdd (ccK βK₀ e) (m none) (X ^ d)).eval (l : K)

/-- `∏_o α_o ^ (e_o l)`, the value of `exp (ψ_e l)`. -/
def alphaPow (e : Option (Fin k) → ℕ) (l : ℕ) : K := ∏ o, αK o ^ (e o * l)

/-- The algebraic number `ι⁻¹ (f_m (l) / ∏ ℓ ^ m)`. -/
noncomputable def Aval (L : ℕ) (P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → K)
    (m : Option (Fin k) → ℕ) (l : ℕ) : K :=
  ∑ x, P x * (evalK βK₀ βK m x.1 (fun o => x.2 o) l * alphaPow αK (fun o => x.2 o) l)

end Field

section Compat

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ_[p])
  {ℓ : Option (Fin k) → ℂ_[p]} {β₀ : ℂ_[p]} {β : Fin k → ℂ_[p]}
  {αK : Option (Fin k) → K} {βK₀ : K} {βK : Fin k → K}

/-- **The values of the auxiliary function at integers are algebraic up to `∏ ℓ ^ m`.** -/
theorem seqEval_aux_natCast_eq (hsmall : ∀ o, ‖ℓ o‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hα : ∀ o, ι (αK o) = NormedSpace.exp (ℓ o)) (hβ : ∀ r, ι (βK r) = β r) (hβ₀ : ι βK₀ = β₀)
    (L : ℕ) (P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → K) (m : Option (Fin k) → ℕ)
    (l : ℕ) :
    seqEval (aux ℓ β₀ β L (fun x => ι (P x)) m) (l : ℂ_[p]) =
      (∏ r, ℓ (some r) ^ m (some r)) * ι (Aval αK βK₀ βK L P m l) := by
  rw [seqEval_aux_natCast hsmall]
  congr 1
  rw [Aval, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  set e : Option (Fin k) → ℕ := fun o => x.2 o with he
  have hgam : ∀ r, ι (gamK βK e r) = gam β e r := fun r => by simp [gamK, gam, hβ]
  have hcc : ι (ccK βK₀ e) = cc β₀ e := by simp [ccK, cc, hβ₀]
  have hD : ι ((derivAdd (ccK βK₀ e) (m none) (X ^ (x.1 : ℕ))).eval (l : K)) =
      (derivAdd (cc β₀ e) (m none) (X ^ (x.1 : ℕ))).eval (l : ℂ_[p]) := by
    rw [← map_natCast ι l, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, map_derivAdd,
      Polynomial.map_pow, map_X, hcc]
  simp only [evalK, alphaPow, map_mul, map_prod, map_pow, hα, hgam, hD]
  ring

end Compat

section Sizes

variable {K : Type*} [Field K] [NumberField K]
  {αK : Option (Fin k) → K} {βK₀ : K} {βK : Fin k → K} {δ : ℕ} {G : ℝ} {L : ℕ}

theorem algSize_gamK (hG : (δ : ℝ) ≤ G) (hβs : ∀ r, AlgSize δ (βK r) 1 G)
    {e : Option (Fin k) → ℕ} (he : ∀ o, e o ≤ L) (r : Fin k) :
    AlgSize δ (gamK βK e r) 1 (2 * L * G) := by
  have h1 := AlgSize.natCast_one (δ := δ) (K := K) (e (some r))
  have h2 := (AlgSize.natCast (δ := δ) (K := K) (e none)).mul (hβs r)
  refine ((h1.add (h2.congr_exp (by ring))).mono ?_)
  have hG0 : 0 ≤ G := (Nat.cast_nonneg δ).trans hG
  have hr : ((e (some r) : ℕ) : ℝ) ≤ L := by exact_mod_cast he _
  have hn : ((e none : ℕ) : ℝ) ≤ L := by exact_mod_cast he _
  nlinarith [Nat.cast_nonneg (α := ℝ) (e (some r)), Nat.cast_nonneg (α := ℝ) (e none),
    Nat.cast_nonneg (α := ℝ) δ]

theorem algSize_ccK (hβ₀s : AlgSize δ βK₀ 1 G) {e : Option (Fin k) → ℕ}
    (he : ∀ o, e o ≤ L) : AlgSize δ (ccK βK₀ e) 1 (L * G) := by
  refine (((AlgSize.natCast (δ := δ) (K := K) (e none)).mul hβ₀s).congr_exp (by ring)).mono ?_
  have hn : ((e none : ℕ) : ℝ) ≤ L := by exact_mod_cast he _
  exact mul_le_mul_of_nonneg_right hn hβ₀s.nonneg

/-- The coefficients of `(D + c) ^ m X ^ d`. -/
theorem algSize_coeff_derivAdd (hG : (δ : ℝ) ≤ G) (hG1 : 1 ≤ G) (hL : 1 ≤ L) {c : K}
    (hc : AlgSize δ c 1 (L * G)) {d : ℕ} (hd : d ≤ L) (m : ℕ) (i : ℕ) :
    AlgSize δ ((derivAdd c m (X ^ d)).coeff i) m ((2 * L * G) ^ m) := by
  induction m generalizing i with
  | zero =>
    rw [derivAdd, Function.iterate_zero, id, coeff_X_pow]
    split_ifs
    · simpa using (AlgSize.natCast (δ := δ) (K := K) 1)
    · exact AlgSize.zero.mono (by simp)
  | succ m ih =>
    rw [derivAdd_succ, coeff_add, coeff_derivative, coeff_C_mul]
    have hLG : (0 : ℝ) ≤ L * G := by positivity
    have hB : (0 : ℝ) ≤ (2 * L * G) ^ m := by positivity
    have h1 : AlgSize δ ((derivAdd c m (X ^ d)).coeff (i + 1) * ((i : K) + 1)) (m + 1)
        (L * G * (2 * L * G) ^ m) := by
      by_cases hi : i + 1 ≤ L
      · have hi' : (i : ℝ) + 1 ≤ L := by exact_mod_cast hi
        have := (ih (i + 1)).mul (AlgSize.natCast_one (δ := δ) (K := K) (i + 1))
        push_cast at this
        refine this.mono ?_
        calc (2 * L * G) ^ m * ((δ : ℝ) * ((i : ℝ) + 1))
            ≤ (2 * L * G) ^ m * (G * L) := by
              gcongr
          _ = L * G * (2 * L * G) ^ m := by ring
      · have hz : (derivAdd c m (X ^ d)).coeff (i + 1) = 0 := coeff_eq_zero_of_natDegree_lt
          ((natDegree_derivAdd_le c m (X ^ d)).trans_lt (by rw [natDegree_X_pow]; omega))
        rw [hz, zero_mul]
        exact AlgSize.zero.mono (by positivity)
    have h2 : AlgSize δ (c * (derivAdd c m (X ^ d)).coeff i) (m + 1) (L * G * (2 * L * G) ^ m) :=
      (hc.mul (ih i)).congr_exp (by ring)
    refine (h1.add h2).mono (le_of_eq ?_)
    ring

/-- The value of `(D + c) ^ m X ^ d` at a positive integer. -/
theorem algSize_eval_derivAdd (hG : (δ : ℝ) ≤ G) (hG1 : 1 ≤ G) (hL : 1 ≤ L) {c : K}
    (hc : AlgSize δ c 1 (L * G)) {d : ℕ} (hd : d ≤ L) (m : ℕ) {l : ℕ} (hl : 1 ≤ l) :
    AlgSize δ ((derivAdd c m (X ^ d)).eval (l : K)) m
      ((L + 1) * (l : ℝ) ^ L * (2 * L * G) ^ m) := by
  have hdeg : (derivAdd c m (X ^ d)).natDegree < L + 1 :=
    (natDegree_derivAdd_le c m (X ^ d)).trans_lt (by rw [natDegree_X_pow]; omega)
  rw [eval_eq_sum_range' hdeg]
  have hsum := AlgSize.sum (Finset.range (L + 1)) (a := m) (f := fun i =>
      (derivAdd c m (X ^ d)).coeff i * (l : K) ^ i)
      (F := fun _ => (2 * L * G) ^ m * (l : ℝ) ^ L) fun i hi => by
    have := (algSize_coeff_derivAdd hG hG1 hL hc hd m i).mul
      ((AlgSize.natCast (δ := δ) (K := K) (l ^ i)))
    rw [add_zero] at this
    refine (by simpa using this : AlgSize δ ((derivAdd c m (X ^ d)).coeff i * (l : K) ^ i) m
      ((2 * L * G) ^ m * ((l ^ i : ℕ) : ℝ))).mono ?_
    rw [Finset.mem_range] at hi
    have : ((l ^ i : ℕ) : ℝ) ≤ (l : ℝ) ^ L := by
      push_cast
      exact pow_le_pow_right₀ (by exact_mod_cast hl) (by omega)
    gcongr
  refine hsum.mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

theorem algSize_prod_gamK (hG : (δ : ℝ) ≤ G) (hβs : ∀ r, AlgSize δ (βK r) 1 G)
    {e : Option (Fin k) → ℕ} (he : ∀ o, e o ≤ L) (m : Option (Fin k) → ℕ) :
    AlgSize δ (∏ r, gamK βK e r ^ m (some r)) (∑ r, m (some r))
      ((2 * L * G) ^ (∑ r, m (some r))) := by
  have := AlgSize.prod Finset.univ (f := fun r => gamK βK e r ^ m (some r))
    (e := fun r => 1 * m (some r)) (F := fun r => (2 * L * G) ^ (m (some r)))
    fun r _ => (algSize_gamK hG hβs he r).pow _
  simpa [Finset.prod_pow_eq_pow_sum] using this

theorem algSize_evalK (hG : (δ : ℝ) ≤ G) (hG1 : 1 ≤ G) (hL : 1 ≤ L)
    (hβs : ∀ r, AlgSize δ (βK r) 1 G) (hβ₀s : AlgSize δ βK₀ 1 G) {e : Option (Fin k) → ℕ}
    (he : ∀ o, e o ≤ L) {d : ℕ} (hd : d ≤ L) (m : Option (Fin k) → ℕ) {l : ℕ} (hl : 1 ≤ l) :
    AlgSize δ (evalK βK₀ βK m d e l) (∑ o, m o)
      ((L + 1) * (l : ℝ) ^ L * (2 * L * G) ^ (∑ o, m o)) := by
  have h := (algSize_prod_gamK hG hβs he m).mul
    (algSize_eval_derivAdd hG hG1 hL (algSize_ccK hβ₀s he) hd (m none) hl)
  refine (h.congr_exp (by rw [Fintype.sum_option]; ring)).mono (le_of_eq ?_)
  rw [Fintype.sum_option, pow_add]
  ring

theorem algSize_alphaPow (hG : (δ : ℝ) ≤ G) (hαs : ∀ o, AlgSize δ (αK o) 1 G)
    {e : Option (Fin k) → ℕ} (he : ∀ o, e o ≤ L) (l : ℕ) :
    AlgSize δ (alphaPow αK e l) ((k + 1) * L * l) (G ^ ((k + 1) * L * l)) := by
  have h := AlgSize.prod Finset.univ (f := fun o => αK o ^ (e o * l))
    (e := fun o => 1 * (e o * l)) (F := fun o => G ^ (e o * l)) fun o _ => (hαs o).pow _
  have hle : ∑ o, 1 * (e o * l) ≤ (k + 1) * L * l := by
    calc ∑ o, 1 * (e o * l) ≤ ∑ _o : Option (Fin k), L * l :=
          Finset.sum_le_sum fun o _ => by rw [one_mul]; exact Nat.mul_le_mul_right _ (he o)
      _ = (k + 1) * L * l := by simp [Finset.card_univ, Fintype.card_option]; ring
  refine (h.raise_le hle hG).mono (le_of_eq ?_)
  have hs : ∑ o, 1 * (e o * l) = ∑ o, e o * l := by simp
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← hs, Nat.sub_add_cancel hle]

/-- **The size of `Aval m l`.** -/
theorem algSize_Aval (hG : (δ : ℝ) ≤ G) (hG1 : 1 ≤ G) (hL : 1 ≤ L)
    (hαs : ∀ o, AlgSize δ (αK o) 1 G) (hβs : ∀ r, AlgSize δ (βK r) 1 G)
    (hβ₀s : AlgSize δ βK₀ 1 G) {P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → K} {PH : ℝ}
    (hP : ∀ x, AlgSize δ (P x) 0 PH) (m : Option (Fin k) → ℕ) {l : ℕ} (hl : 1 ≤ l) :
    AlgSize δ (Aval αK βK₀ βK L P m l) (∑ o, m o + (k + 1) * L * l)
      ((L + 1) ^ (k + 2) * (PH * ((L + 1) * (l : ℝ) ^ L * (2 * L * G) ^ (∑ o, m o) *
        G ^ ((k + 1) * L * l)))) := by
  have he : ∀ x : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)), ∀ o, (x.2 o : ℕ) ≤ L :=
    fun x o => Nat.lt_succ_iff.mp (x.2 o).2
  have hd : ∀ x : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)), (x.1 : ℕ) ≤ L :=
    fun x => Nat.lt_succ_iff.mp x.1.2
  have h := AlgSize.sum Finset.univ (a := ∑ o, m o + (k + 1) * L * l)
    (f := fun x => P x * (evalK βK₀ βK m x.1 (fun o => x.2 o) l * alphaPow αK (fun o => x.2 o) l))
    (F := fun _ => PH * ((L + 1) * (l : ℝ) ^ L * (2 * L * G) ^ (∑ o, m o) *
      G ^ ((k + 1) * L * l))) fun x _ =>
    ((hP x).mul ((algSize_evalK hG hG1 hL hβs hβ₀s (he x) (hd x) m hl).mul
      (algSize_alphaPow hG hαs (he x) l))).congr_exp (by ring)
  refine h.mono (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_option, nsmul_eq_mul]
  push_cast
  ring

end Sizes

section Siegel

open Matrix

/-- **Siegel's lemma over a number field**, with a constant depending only on the field. -/
theorem exists_siegel (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α β : Type) [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)) (A : ℝ),
      1 ≤ A → 0 < Fintype.card α → 2 * Fintype.card α ≤ Fintype.card β →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
        ∀ l, house (ξ l : K) ≤ C * (Fintype.card β * A) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ (α β : Type) [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)),
      a ≠ 0 → ∀ (A : ℝ), (∀ i j, house (algebraMap (𝓞 K) K (a i j)) ≤ A) →
      0 < Fintype.card α → Fintype.card α < Fintype.card β →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ l, house (ξ l : K) ≤
        c * ((c * Fintype.card β * A) ^ ((Fintype.card α : ℝ) /
          (Fintype.card β - Fintype.card α))) :=
    ⟨_, fun α β _ _ a ha A habs h0 hpq =>
      NumberField.house.exists_ne_zero_int_vec_house_le K a ha h0 hpq rfl habs rfl⟩
  refine ⟨(|c| + 1) ^ 2, by nlinarith [abs_nonneg c], fun α β _ _ a A hA h0 h2 habs => ?_⟩
  have hβpos : 0 < Fintype.card β := by omega
  have hqA : (1 : ℝ) ≤ Fintype.card β * A :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hβpos) hA
  by_cases ha : a = 0
  · have : Nonempty β := Fintype.card_pos_iff.mp hβpos
    refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h (Classical.arbitrary β)), ?_, fun l => ?_⟩
    · rw [ha]; exact Matrix.zero_mulVec _
    · have h1 : house (1 : K) = 1 := by simpa using house_intCast (K := K) 1
      simp only [map_one, h1]
      nlinarith [abs_nonneg c]
  obtain ⟨ξ, hξ0, hξ, hbound⟩ := hc α β a ha A habs h0 (by omega)
  refine ⟨ξ, hξ0, hξ, fun l => (hbound l).trans ?_⟩
  set e : ℝ := (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) with he
  have he0 : 0 ≤ e := div_nonneg (Nat.cast_nonneg _) (by
    have : (Fintype.card α : ℝ) ≤ Fintype.card β := by exact_mod_cast (by omega : _ ≤ _)
    linarith)
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by
      have : (Fintype.card α : ℝ) < Fintype.card β := by exact_mod_cast (by omega : _ < _)
      linarith)]
    have : (2 * Fintype.card α : ℝ) ≤ Fintype.card β := by exact_mod_cast h2
    linarith
  set x := |c| * (Fintype.card β * A) with hx
  have hx0 : 0 ≤ x := by positivity
  have hpow : x ^ e ≤ x + 1 := by
    rcases le_or_gt x 1 with h | h
    · exact (Real.rpow_le_one hx0 h he0).trans (by linarith)
    · calc x ^ e ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le he1
        _ = x := Real.rpow_one x
        _ ≤ x + 1 := by linarith
  calc c * (c * Fintype.card β * A) ^ e ≤ |c| * |(c * Fintype.card β * A) ^ e| :=
        (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ |c| * |c * Fintype.card β * A| ^ e := by
        gcongr; exact Real.abs_rpow_le_abs_rpow _ _
    _ = |c| * x ^ e := by
        congr 2
        rw [hx, abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg (by linarith : (0 : ℝ) ≤ A),
          mul_assoc]
    _ ≤ |c| * (x + 1) := by gcongr
    _ ≤ (|c| + 1) ^ 2 * (Fintype.card β * A) := by
        rw [hx]; nlinarith [abs_nonneg c]

end Siegel

section Lower

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ_[p]) {δ : ℕ}

/-- **Liouville's inequality at `p`**, for a number of known size. -/
theorem inv_pow_le_norm_of_algSize {x : K} {a : ℕ} {H : ℝ} (h : AlgSize δ x a H)
    (hδ : δ ≠ 0) (hx : x ≠ 0) : (H ^ Module.finrank ℚ K)⁻¹ ≤ ‖ι x‖ := by
  have key := NumberField.one_le_pow_mul_norm_embedding
    (fun n hn => PadicComplex.one_le_abs_mul_norm_intCast hn) h.1 h.2 hδ hx ι
  have hH : 0 < H ^ Module.finrank ℚ K := by
    rcases (pow_nonneg h.nonneg (Module.finrank ℚ K)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at key; linarith
  rw [inv_le_iff_one_le_mul₀' hH]
  exact key

end Lower

section Construction

open Matrix

variable {K : Type*} [Field K] [NumberField K]
  {αK : Option (Fin k) → K} {βK₀ : K} {βK : Fin k → K} {δ : ℕ} {G : ℝ}

/-- The bound for the entries of Baker's linear system (after clearing denominators). -/
noncomputable def entryBound (k L h : ℕ) (G : ℝ) : ℝ :=
  G ^ ((k + 1) * h ^ 2 + (k + 1) * L * h) *
    ((L + 1) * (h : ℝ) ^ L * (2 * L * G) ^ ((k + 1) * h ^ 2) * G ^ ((k + 1) * L * h))

theorem one_le_entryBound {L h : ℕ} (hL : 1 ≤ L) (hh : 1 ≤ h) (hG1 : 1 ≤ G) :
    1 ≤ entryBound k L h G := by
  have h2LG : (1 : ℝ) ≤ 2 * L * G := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  unfold entryBound
  refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hG1) ?_
  refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
      (one_le_pow₀ hh1)) (one_le_pow₀ h2LG)) (one_le_pow₀ hG1)

/-- **Baker's Lemma 2 over `ℂ_[p]`.** Siegel's lemma gives algebraic integers `P`, not all zero
and of controlled house, such that `Aval m l = 0` for `m o ≤ h ^ 2` and `1 ≤ l ≤ h`. -/
theorem exists_aux_vanishing (hδ : 1 ≤ δ) (hG : (δ : ℝ) ≤ G) (hG1 : 1 ≤ G)
    (hαs : ∀ o, AlgSize δ (αK o) 1 G) (hβs : ∀ r, AlgSize δ (βK r) 1 G)
    (hβ₀s : AlgSize δ βK₀ 1 G) {C : ℝ}
    (hsiegel : ∀ (α β : Type) [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)) (A : ℝ),
      1 ≤ A → 0 < Fintype.card α → 2 * Fintype.card α ≤ Fintype.card β →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ l, house (ξ l : K) ≤ C * (Fintype.card β * A))
    {L h : ℕ} (hL : 1 ≤ L) (hh : 1 ≤ h)
    (hcount : 2 * ((h ^ 2 + 1) ^ (k + 1) * h) ≤ (L + 1) ^ (k + 2)) :
    ∃ P : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → 𝓞 K, P ≠ 0 ∧
      (∀ x, house (P x : K) ≤ C * ((L + 1) ^ (k + 2) * entryBound k L h G)) ∧
      ∀ m : Option (Fin k) → ℕ, (∀ o, m o ≤ h ^ 2) → ∀ l, 1 ≤ l → l ≤ h →
        Aval αK βK₀ βK L (fun x => (P x : K)) m l = 0 := by
  classical
  set E := (k + 1) * h ^ 2 + (k + 1) * L * h with hE
  -- the entries of the system, indexed by `m o ≤ h ^ 2` and `l = j + 1 ≤ h`
  let ent : ((Option (Fin k) → Fin (h ^ 2 + 1)) × Fin h) →
      (Fin (L + 1) × (Option (Fin k) → Fin (L + 1))) → K := fun i x =>
    evalK βK₀ βK (fun o => (i.1 o : ℕ)) x.1 (fun o => x.2 o) (i.2 + 1) *
      alphaPow αK (fun o => x.2 o) (i.2 + 1)
  have hent : ∀ i x, AlgSize δ (ent i x) E (entryBound k L h G) := by
    intro i x
    have he : ∀ o, (x.2 o : ℕ) ≤ L := fun o => Nat.lt_succ_iff.mp (x.2 o).2
    have hl : 1 ≤ (i.2 : ℕ) + 1 := by omega
    have hlh : (i.2 : ℕ) + 1 ≤ h := i.2.2
    have hm : ∑ o, (i.1 o : ℕ) ≤ (k + 1) * h ^ 2 := by
      calc ∑ o, (i.1 o : ℕ) ≤ ∑ _o : Option (Fin k), h ^ 2 :=
            Finset.sum_le_sum fun o _ => Nat.lt_succ_iff.mp (i.1 o).2
        _ = (k + 1) * h ^ 2 := by simp [Fintype.card_option]
    have h0 := (algSize_evalK hG hG1 hL hβs hβ₀s he (Nat.lt_succ_iff.mp x.1.2)
      (fun o => (i.1 o : ℕ)) hl).mul (algSize_alphaPow hG hαs he ((i.2 : ℕ) + 1))
    have hexp : ∑ o, (i.1 o : ℕ) + (k + 1) * L * ((i.2 : ℕ) + 1) ≤ E := by
      rw [hE]; have := Nat.mul_le_mul_left ((k + 1) * L) hlh; omega
    refine (h0.raise_le hexp hG).mono ?_
    have h2LG : (1 : ℝ) ≤ 2 * L * G := by
      have : (1 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    have hl' : (((i.2 : ℕ) + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hlh
    have hG0 : 0 ≤ G := zero_le_one.trans hG1
    have h1 : G ^ (E - (∑ o, (i.1 o : ℕ) + (k + 1) * L * ((i.2 : ℕ) + 1))) ≤ G ^ E :=
      pow_le_pow_right₀ hG1 (Nat.sub_le _ _)
    have h2 : ((((i.2 : ℕ) + 1 : ℕ) : ℝ)) ^ L ≤ (h : ℝ) ^ L :=
      pow_le_pow_left₀ (by positivity) hl' L
    have h3 : (2 * L * G) ^ (∑ o, (i.1 o : ℕ)) ≤ (2 * L * G) ^ ((k + 1) * h ^ 2) :=
      pow_le_pow_right₀ h2LG hm
    have h4 : G ^ ((k + 1) * L * ((i.2 : ℕ) + 1)) ≤ G ^ ((k + 1) * L * h) :=
      pow_le_pow_right₀ hG1 (Nat.mul_le_mul_left _ hlh)
    unfold entryBound
    rw [← hE]
    refine mul_le_mul h1 ?_ (by positivity) (by positivity)
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h3
      (by positivity) (by positivity)) h4 (by positivity) (by positivity)
  -- the integral matrix
  let a : Matrix ((Option (Fin k) → Fin (h ^ 2 + 1)) × Fin h)
      (Fin (L + 1) × (Option (Fin k) → Fin (L + 1))) (𝓞 K) :=
    fun i x => ⟨(δ : K) ^ E * ent i x, (hent i x).1⟩
  have hcardα : Fintype.card ((Option (Fin k) → Fin (h ^ 2 + 1)) × Fin h) =
      (h ^ 2 + 1) ^ (k + 1) * h := by
    simp [Fintype.card_option]
  have hcardβ :
      Fintype.card (Fin (L + 1) × (Option (Fin k) → Fin (L + 1))) = (L + 1) ^ (k + 2) := by
    simp [Fintype.card_option, pow_succ]; ring
  obtain ⟨ξ, hξ0, hξ, hbound⟩ := hsiegel _ _ a (entryBound k L h G)
    (one_le_entryBound hL hh hG1) (by rw [hcardα]; positivity)
    (by rw [hcardα, hcardβ]; exact hcount)
    (fun i x => (hent i x).2)
  refine ⟨ξ, hξ0, fun x => by simpa [hcardβ] using hbound x, fun m hm l hl1 hlh => ?_⟩
  set i : (Option (Fin k) → Fin (h ^ 2 + 1)) × Fin h :=
    (fun o => ⟨m o, Nat.lt_succ_iff.mpr (hm o)⟩, ⟨l - 1, by omega⟩) with hi
  have hrow := congrFun hξ i
  simp only [mulVec, dotProduct, Pi.zero_apply] at hrow
  have hrowK := congrArg (algebraMap (𝓞 K) K) hrow
  simp only [map_sum, map_mul, map_zero] at hrowK
  have hδE : (δ : K) ^ E ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : δ ≠ 0))
  have hsum : ∑ x, (ξ x : K) * ent i x = 0 := by
    have : (δ : K) ^ E * ∑ x, (ξ x : K) * ent i x = 0 := by
      rw [Finset.mul_sum, ← hrowK]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [a]
      change _ = ((δ : K) ^ E * ent i x) * (ξ x : K)
      ring
    exact (mul_eq_zero.mp this).resolve_left hδE
  have hl : (i.2 : ℕ) + 1 = l := by simp [hi]; omega
  rw [Aval, ← hsum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ent]
  rw [hl]

end Construction

section Separation

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ_[p])
  {αK : Option (Fin k) → K} {δ : ℕ} {G : ℝ} {ℓ : Option (Fin k) → ℂ_[p]}

theorem norm_psi_lt (hsmall : ∀ o, ‖ℓ o‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (e : Option (Fin k) → ℕ) : ‖psi ℓ e‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  obtain ⟨j, -, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Option (Fin k))) fun o => (e o : ℂ_[p]) * ℓ o
  refine hj.trans_lt ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans_lt
    (hsmall j)

/-- **Baker's Lemma 6 over `ℂ_[p]`.** Distinct frequencies `ψ_e` are far apart. -/
theorem inv_pow_le_norm_psi_sub (hli : LinearIndependent ℚ ℓ)
    (hsmall : ∀ o, ‖ℓ o‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hα : ∀ o, ι (αK o) = NormedSpace.exp (ℓ o)) (hδ : 1 ≤ δ) (hG : (δ : ℝ) ≤ G)
    (hαs : ∀ o, AlgSize δ (αK o) 1 G) {L : ℕ} {e e' : Option (Fin k) → ℕ}
    (he : ∀ o, e o ≤ L) (he' : ∀ o, e' o ≤ L) (hne : e ≠ e') :
    ((2 * G ^ ((k + 1) * L)) ^ Module.finrank ℚ K)⁻¹ ≤ ‖psi ℓ e - psi ℓ e'‖ := by
  classical
  set x := psi ℓ e - psi ℓ e' with hx
  -- `x ≠ 0` by linear independence
  have hx0 : x ≠ 0 := by
    intro h0
    have hcomb : ∑ o, (((((e o : ℚ) - (e' o : ℚ)) : ℚ) : ℂ_[p]) * ℓ o) = 0 := by
      rw [← h0, hx, psi, psi, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun o _ => ?_
      push_cast; ring
    have := Fintype.linearIndependent_iff.mp hli (fun o => (e o : ℚ) - (e' o : ℚ))
      (by simpa [Rat.smul_def] using hcomb)
    exact hne (funext fun o => by exact_mod_cast sub_eq_zero.mp (this o))
  have hxsmall : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rw [hx, sub_eq_add_neg]
    exact PadicComplex.norm_add_lt_expRadius (norm_psi_lt hsmall e)
      (by rw [norm_neg]; exact norm_psi_lt hsmall e')
  -- `‖x‖ = ‖exp ψ_e - exp ψ_{e'}‖`
  have hnorm : ‖x‖ = ‖NormedSpace.exp (psi ℓ e) - NormedSpace.exp (psi ℓ e')‖ := by
    have hsum : psi ℓ e = psi ℓ e' + x := by rw [hx]; ring
    rw [hsum, PadicComplex.exp_add (norm_psi_lt hsmall e') hxsmall, ← _root_.mul_sub_one, norm_mul,
      PadicComplex.norm_exp (norm_psi_lt hsmall e'), one_mul, PadicComplex.norm_exp_sub_one hxsmall]
  have hexp : ∀ e'' : Option (Fin k) → ℕ,
      NormedSpace.exp (psi ℓ e'') = ι (alphaPow αK e'' 1) := by
    intro e''
    have := exp_psi_mul_natCast hsmall e'' 1
    simp only [Nat.cast_one, mul_one] at this
    simp [this, alphaPow, map_prod, map_pow, hα]
  rw [hnorm, hexp, hexp, ← map_sub]
  have hsize : AlgSize δ (alphaPow αK e 1 - alphaPow αK e' 1) ((k + 1) * L * 1)
      (G ^ ((k + 1) * L * 1) + 1 * G ^ ((k + 1) * L * 1)) := by
    have h1 := algSize_alphaPow hG hαs he 1
    have h2 := ((AlgSize.intCast (δ := δ) (K := K) (-1)).mul
      (algSize_alphaPow hG hαs he' 1)).congr_exp (zero_add _)
    simp only [Int.cast_neg, Int.cast_one, abs_neg, abs_one, Int.cast_one] at h2
    simpa [sub_eq_add_neg] using h1.add h2
  have hne0 : alphaPow αK e 1 - alphaPow αK e' 1 ≠ 0 := by
    intro h0
    apply hx0
    rw [← norm_eq_zero, hnorm, hexp, hexp, ← map_sub, h0, map_zero, norm_zero]
  have := inv_pow_le_norm_of_algSize ι hsize (by omega) hne0
  simpa [two_mul] using this

end Separation

end PadicBaker
