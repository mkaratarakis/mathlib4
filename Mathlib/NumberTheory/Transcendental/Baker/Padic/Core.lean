/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Arithmetic
public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Hermite

/-!
# The transcendence argument over `ℂ_[p]`

Baker–Masser, *Transcendental Number Theory*, Chapter 2, Lemmas 4, 5 and §5, transplanted to
`ℂ_[p]`. Starting from the auxiliary function of Lemma 2 (`PadicBaker.exists_aux_vanishing`),
the vanishing of the `f_m` at the integers `1, …, R J` for `∑ m ≤ S J` is extrapolated to the
integers up to `R (J + 1)` for `∑ m ≤ S (J + 1)`: the Strassmann-type bound
`PadicBaker.norm_seqEval_le_of_iterate_seqDeriv_eq_zero` makes the new values small, and
Liouville's inequality at `p` makes them zero. At the end `f_0` has so many zeros that all its
coefficients are tiny, and Baker's Hermite interpolation (`PadicBaker.exists_hermite`) turns this
into a nonzero algebraic integer `P t` of `p`-adic norm smaller than Liouville allows.

The choice of the parameters is `PadicBaker.core`'s hypotheses `hcount`, `hext` and `hfin`.
-/

@[expose] public section

open Polynomial NumberField Nat

namespace PadicBaker

variable {p : ℕ} [hp : Fact p.Prime] {k : ℕ}

theorem norm_factorial_inv_le (s : ℕ) : ‖((s ! : ℕ) : ℂ_[p])⁻¹‖ ≤ (p : ℝ) ^ s := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  rw [norm_inv, PadicComplex.norm_natCast_factorial, zpow_neg, inv_inv, zpow_natCast]
  refine pow_le_pow_right₀ hp1 ?_
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) hs.ne'
    have hp2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
    nlinarith

/-- **The core of the proof of the `p`-adic Baker theorem**: the numeric hypotheses `hcount`,
`hext` and `hfin` on the parameters are incompatible with a relation
`ℓ none = β₀ + ∑ β r ℓ (some r)` between `ℚ`-linearly independent `p`-adic logarithms of algebraic
numbers. -/
theorem core {ℓ : Option (Fin k) → ℂ_[p]} {β₀ : ℂ_[p]} {β : Fin k → ℂ_[p]}
    (hrel : ℓ none = β₀ + ∑ r, β r * ℓ (some r))
    (hsmall : ∀ o, ‖ℓ o‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (hli : LinearIndependent ℚ ℓ)
    {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ_[p])
    {αK : Option (Fin k) → K} {βK₀ : K} {βK : Fin k → K}
    (hα : ∀ o, ι (αK o) = NormedSpace.exp (ℓ o)) (hβ : ∀ r, ι (βK r) = β r) (hβ₀ : ι βK₀ = β₀)
    {δ : ℕ} {G : ℝ} (hδ : 1 ≤ δ) (hG : (δ : ℝ) ≤ G) (hG1 : 1 ≤ G)
    (hαs : ∀ o, AlgSize δ (αK o) 1 G) (hβs : ∀ r, AlgSize δ (βK r) 1 G)
    (hβ₀s : AlgSize δ βK₀ 1 G) {C : ℝ} (hC : 1 ≤ C)
    (hsiegel : ∀ (α β : Type) [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)) (A : ℝ),
      1 ≤ A → 0 < Fintype.card α → 2 * Fintype.card α ≤ Fintype.card β →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a.mulVec ξ = 0 ∧ ∀ l, house (ξ l : K) ≤ C * (Fintype.card β * A))
    {r₀ B lmin : ℝ} (hr₀ : 1 < r₀) (hℓr : ∀ o, ‖ℓ o‖ * r₀ ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hB : 1 ≤ B) (hβB : ∀ r, ‖β r‖ ≤ B) (hβ₀B : ‖β₀‖ ≤ B)
    (hlmin0 : 0 < lmin) (hlmin1 : lmin ≤ 1) (hlmin : ∀ o, lmin ≤ ‖ℓ o‖)
    {L h Kmax : ℕ} {S R : ℕ → ℕ} (hL : 1 ≤ L) (hh : 1 ≤ h)
    (hcount : 2 * ((h ^ 2 + 1) ^ (k + 1) * h) ≤ (L + 1) ^ (k + 2))
    (hS0 : S 0 ≤ h ^ 2) (hR0 : R 0 ≤ h) (hSstep : ∀ J < Kmax, 2 * S (J + 1) ≤ S J)
    (hext : ∀ J < Kmax, B ^ S (J + 1) * r₀ ^ L *
        ((L + 1) ^ (k + 2) * (C * ((L + 1) ^ (k + 2) * entryBound k L h G) *
          ((L + 1) * (R (J + 1) : ℝ) ^ L * (2 * L * G) ^ S (J + 1) *
            G ^ ((k + 1) * L * R (J + 1))))) ^ Module.finrank ℚ K <
      lmin ^ S (J + 1) * r₀ ^ (R J * S (J + 1)))
    (hfin : (C * ((L + 1) ^ (k + 2) * entryBound k L h G)) ^ Module.finrank ℚ K *
        (p : ℝ) ^ L *
        ((2 * G ^ ((k + 1) * L)) ^ Module.finrank ℚ K) ^ ((L + 1) ^ (k + 1) * (L + 1)) *
        r₀ ^ L < r₀ ^ (R Kmax * S Kmax)) :
    False := by
  classical
  set D := Module.finrank ℚ K with hD
  set PH := C * ((L + 1) ^ (k + 2) * entryBound k L h G) with hPH
  have hρ1 : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.out.one_le)
      (neg_nonpos.mpr (inv_nonneg.mpr (by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
        linarith)))
  have hℓ1 : ∀ o, ‖ℓ o‖ ≤ 1 := fun o => (hsmall o).le.trans hρ1
  have hPH1 : 1 ≤ PH := one_le_mul_of_one_le_of_one_le hC (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])) (one_le_entryBound hL hh hG1))
  have hD1 : 1 ≤ D := Module.finrank_pos
  -- Lemma 2: the auxiliary function
  obtain ⟨P, hP0, hPH, hPvan⟩ := exists_aux_vanishing (αK := αK) (βK₀ := βK₀) (βK := βK) hδ hG
    hG1 hαs hβs hβ₀s hsiegel hL hh hcount
  set Pc : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)) → ℂ_[p] := fun x => ι (P x : K) with hPc
  have hPc1 : ∀ x, ‖Pc x‖ ≤ 1 := fun x => by
    refine IsUltrametricDist.norm_le_one_of_isIntegral ?_
    obtain ⟨g, hgm, hg⟩ := (P x).isIntegral_coe
    refine ⟨g, hgm, ?_⟩
    have h1 := congrArg ι hg
    rw [map_zero, Polynomial.hom_eval₂] at h1
    convert h1 using 2
    exact RingHom.ext_int _ _
  have hPs : ∀ x, AlgSize δ (P x : K) 0 PH := fun x => ⟨by simpa using (P x).isIntegral_coe,
    by simpa using hPH x⟩
  set f := aux ℓ β₀ β L Pc with hf
  have hdec : ∀ m j, ‖f m j‖ * r₀ ^ j ≤ B ^ (∑ o, m o) * r₀ ^ L := fun m j =>
    norm_aux_mul_pow_le hr₀.le hB hℓr hℓ1 hβB hβ₀B hPc1 m j
  have hsum : ∀ (x : ℂ_[p]), ‖x‖ ≤ 1 → ∀ m j,
      Summable fun n => (seqDeriv^[j] (f m)) n * x ^ n := fun x hx m j =>
    summable_of_decay hr₀ (iterate_seqDeriv_decay hr₀.le (hdec m) j) hx
  have hval : ∀ m (l : ℕ), seqEval (f m) (l : ℂ_[p]) =
      (∏ r, ℓ (some r) ^ m (some r)) * ι (Aval αK βK₀ βK L (fun x => (P x : K)) m l) :=
    fun m l => seqEval_aux_natCast_eq ι hsmall hα hβ hβ₀ L (fun x => (P x : K)) m l
  have hnat : ∀ l : ℕ, ‖(l : ℂ_[p])‖ ≤ 1 := fun l => IsUltrametricDist.norm_natCast_le_one _ l
  -- the extrapolation
  have hZ : ∀ J ≤ Kmax, ∀ m : Option (Fin k) → ℕ, ∑ o, m o ≤ S J → ∀ l : ℕ, 1 ≤ l → l ≤ R J →
      seqEval (f m) (l : ℂ_[p]) = 0 := by
    intro J
    induction J with
    | zero =>
      intro _ m hm l hl1 hl
      rw [hval, hPvan m (fun o => (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ o)).trans (hm.trans hS0)) l hl1 (hl.trans hR0), map_zero, mul_zero]
    | succ J ih =>
      intro hJ m hm l hl1 hl
      have hJ' : J < Kmax := by omega
      have ihJ := ih hJ'.le
      -- the derivatives of `f m` vanish at the old integers
      have hvan : ∀ a ∈ Finset.Icc 1 (R J), ∀ j < S (J + 1),
          seqEval (seqDeriv^[j] (f m)) (a : ℂ_[p]) = 0 := by
        intro a ha j hj
        rw [Finset.mem_Icc] at ha
        refine seqEval_iterate_seqDeriv_aux_eq_zero hrel (hsum _ (hnat a)) (S' := S J)
          (fun m' hm' => ihJ m' hm' a ha.1 ha.2) j m ?_
        have := hSstep J hJ'
        omega
      have hupper := norm_seqEval_le_of_iterate_seqDeriv_eq_zero hr₀ (hdec m) _ _ hvan (hnat l)
      rw [Nat.card_Icc, Nat.add_sub_cancel] at hupper
      by_contra hne
      have hA : Aval αK βK₀ βK L (fun x => (P x : K)) m l ≠ 0 := by
        intro h0; apply hne; rw [hval, h0, map_zero, mul_zero]
      have hsize := algSize_Aval hG hG1 hL hαs hβs hβ₀s hPs m hl1
      have hlow := inv_pow_le_norm_of_algSize ι hsize (by omega) hA
      -- compare the two bounds
      have hRl : (l : ℝ) ≤ R (J + 1) := by exact_mod_cast hl
      have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hl1
      have h2LG : (1 : ℝ) ≤ 2 * L * G := by
        have : (1 : ℝ) ≤ L := by exact_mod_cast hL
        nlinarith
      set Hm := (L + 1 : ℝ) ^ (k + 2) * (PH * ((L + 1) * (l : ℝ) ^ L *
        (2 * L * G) ^ (∑ o, m o) * G ^ ((k + 1) * L * l))) with hHm
      set Hx := (L + 1 : ℝ) ^ (k + 2) * (PH * ((L + 1) * (R (J + 1) : ℝ) ^ L *
        (2 * L * G) ^ S (J + 1) * G ^ ((k + 1) * L * R (J + 1)))) with hHx
      have hG0 : 0 < G := zero_lt_one.trans_le hG1
      have hHm0 : 0 < Hm := by positivity
      have hHmx : Hm ≤ Hx := by
        rw [hHm, hHx]
        gcongr
      have hprod : lmin ^ S (J + 1) ≤ ‖∏ r, ℓ (some r) ^ m (some r)‖ := by
        rw [norm_prod]
        calc lmin ^ S (J + 1) ≤ lmin ^ (∑ o, m o) := pow_le_pow_of_le_one hlmin0.le hlmin1 hm
          _ ≤ lmin ^ (∑ r, m (some r)) := pow_le_pow_of_le_one hlmin0.le hlmin1 (by
              rw [Fintype.sum_option]; omega)
          _ = ∏ r, lmin ^ m (some r) := (Finset.prod_pow_eq_pow_sum _ _ _).symm
          _ ≤ ∏ r, ‖ℓ (some r) ^ m (some r)‖ := by
              gcongr with r
              rw [norm_pow]
              exact pow_le_pow_left₀ hlmin0.le (hlmin _) _
      have hlower : lmin ^ S (J + 1) / Hx ^ D ≤ ‖seqEval (f m) (l : ℂ_[p])‖ := by
        rw [hval, norm_mul, div_eq_mul_inv]
        refine mul_le_mul hprod ((inv_anti₀ (pow_pos hHm0 D)
          (pow_le_pow_left₀ hHm0.le hHmx D)).trans hlow) (by positivity) (norm_nonneg _)
      have hup' : ‖seqEval (f m) (l : ℂ_[p])‖ ≤
          B ^ S (J + 1) * r₀ ^ L / r₀ ^ (R J * S (J + 1)) := by
        refine hupper.trans ?_
        rw [div_eq_mul_inv]
        gcongr
      have key := (div_le_div_iff₀ (pow_pos (hHm0.trans_le hHmx) D)
        (pow_pos (zero_lt_one.trans hr₀) _)).mp (hlower.trans hup')
      have := hext J hJ'
      linarith
  -- the final step
  have hvan0 : ∀ a ∈ Finset.Icc 1 (R Kmax), ∀ j < S Kmax + 1,
      seqEval (seqDeriv^[j] (f 0)) (a : ℂ_[p]) = 0 := by
    intro a ha j hj
    rw [Finset.mem_Icc] at ha
    refine seqEval_iterate_seqDeriv_aux_eq_zero hrel (hsum _ (hnat a)) (S' := S Kmax)
      (fun m' hm' => hZ Kmax le_rfl m' hm' a ha.1 ha.2) j 0 ?_
    simp; omega
  have hcoeff : ∀ n, ‖f 0 n‖ ≤ r₀ ^ L * (r₀ ^ (R Kmax * S Kmax))⁻¹ := by
    intro n
    have h := norm_le_of_iterate_seqDeriv_eq_zero hr₀ (by simpa using hdec 0) _ _ hvan0 n
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    refine h.trans ?_
    gcongr
    · exact hr₀.le
    · omega
  obtain ⟨t, ht⟩ : ∃ t, P t ≠ 0 := by
    by_contra h0; push Not at h0; exact hP0 (funext h0)
  set ϱ : ℝ := ((2 * G ^ ((k + 1) * L)) ^ D)⁻¹ with hϱ
  have h2G : (1 : ℝ) ≤ 2 * G ^ ((k + 1) * L) := by
    have := one_le_pow₀ (n := (k + 1) * L) hG1; linarith
  have hϱ0 : 0 < ϱ := by positivity
  have hϱ1 : ϱ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h2G)
  set σ : (Option (Fin k) → Fin (L + 1)) → ℂ_[p] := fun e => psi ℓ fun o => e o with hσ
  have hσ1 : ∀ e, ‖σ e‖ ≤ 1 := fun e => (norm_psi_lt hsmall _).le.trans hρ1
  have hsep : ∀ e e', e ≠ e' → ϱ ≤ ‖σ e - σ e'‖ := by
    intro e e' hne
    refine inv_pow_le_norm_psi_sub ι hli hsmall hα hδ hG hαs
      (fun o => Nat.lt_succ_iff.mp (e o).2) (fun o => Nat.lt_succ_iff.mp (e' o).2) ?_
    intro heq
    exact hne (funext fun o => Fin.ext (congrFun heq o))
  obtain ⟨W, hWh, hWc⟩ := exists_hermite σ hσ1 hϱ0 hϱ1 hsep (L + 1) t.2 t.1.2
  have hid := sum_coeff_mul_factorial_aux_zero (ℓ := ℓ) (β₀ := β₀) (β := β) L Pc W
  have hPt : ∑ x : Fin (L + 1) × (Option (Fin k) → Fin (L + 1)),
      Pc x * (derivative^[(x.1 : ℕ)] W).eval (psi ℓ fun o => x.2 o) = Pc t := by
    rw [Finset.sum_eq_single t]
    · rw [show (psi ℓ fun o => t.2 o) = σ t.2 from rfl, hWh _ _ t.1.2]; simp
    · intro x _ hxt
      rw [show (psi ℓ fun o => x.2 o) = σ x.2 from rfl, hWh _ _ x.1.2]
      have : ¬ (x.2 = t.2 ∧ (x.1 : ℕ) = t.1) := fun h' => hxt (Prod.ext (Fin.ext h'.2) h'.1)
      simp [this]
    · simp
  rw [hPt] at hid
  -- the upper bound for `P t`
  have hWn : ∀ n, ‖W.coeff n‖ ≤ (p : ℝ) ^ L * (ϱ ^ ((L + 1) ^ (k + 1) * (L + 1)))⁻¹ := by
    intro n
    refine (hWc n).trans ?_
    simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right ((norm_factorial_inv_le _).trans (pow_le_pow_right₀
      (by exact_mod_cast hp.out.one_le) (Nat.lt_succ_iff.mp t.1.2)))
      (inv_nonneg.mpr (pow_nonneg hϱ0.le _))
  have hup : ‖Pc t‖ ≤ (p : ℝ) ^ L * (ϱ ^ ((L + 1) ^ (k + 1) * (L + 1)))⁻¹ *
      (r₀ ^ L * (r₀ ^ (R Kmax * S Kmax))⁻¹) := by
    rw [← hid]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n _ => ?_
    rw [norm_mul, norm_mul]
    have hn1 : ‖((n ! : ℕ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    calc ‖W.coeff n‖ * ‖((n ! : ℕ) : ℂ_[p])‖ * ‖f 0 n‖
        ≤ ((p : ℝ) ^ L * (ϱ ^ ((L + 1) ^ (k + 1) * (L + 1)))⁻¹) * 1 *
          (r₀ ^ L * (r₀ ^ (R Kmax * S Kmax))⁻¹) :=
          mul_le_mul (mul_le_mul (hWn n) hn1 (norm_nonneg _) (by positivity)) (hcoeff n)
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- the lower bound for `P t`
  have hlow := inv_pow_le_norm_of_algSize ι (hPs t) (by omega)
    (fun h0 => ht (RingOfIntegers.ext (by simpa using h0)))
  have hϱinv : (ϱ ^ ((L + 1) ^ (k + 1) * (L + 1)))⁻¹ =
      ((2 * G ^ ((k + 1) * L)) ^ D) ^ ((L + 1) ^ (k + 1) * (L + 1)) := by
    rw [hϱ, inv_pow, inv_inv]
  rw [hϱinv] at hup
  have hPHpos : 0 < PH ^ D := pow_pos (zero_lt_one.trans_le hPH1) D
  have hr0pos : 0 < r₀ ^ (R Kmax * S Kmax) := pow_pos (zero_lt_one.trans hr₀) _
  have key : 1 / PH ^ D ≤ (p : ℝ) ^ L * ((2 * G ^ ((k + 1) * L)) ^ D) ^
      ((L + 1) ^ (k + 1) * (L + 1)) * r₀ ^ L / r₀ ^ (R Kmax * S Kmax) := by
    rw [one_div]
    refine hlow.trans (hup.trans (le_of_eq ?_))
    rw [div_eq_mul_inv]; ring
  rw [div_le_div_iff₀ hPHpos hr0pos, one_mul] at key
  linarith

end PadicBaker
