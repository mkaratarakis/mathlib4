/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module
public import Mathlib.Tactic
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalyticBounds

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt Differentiable Complex


noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup
/-
We formalize the existence of a function R' : ℂ → ℂ,
analytic in a neighborhood of l' + 1,
such that R(z) = (z - (l' + 1))^r * R'(z) in a neighborhood of l' + 1.
so this o is (I hope) R_order l' -/
lemma exists_R'_at_l'_plus_one (l' : Fin (h7.m))  :
  ∃ (R' : ℂ → ℂ) (U : Set ℂ), (U ∈ nhds (l' + 1 : ℂ)) ∧ (l' + 1 : ℂ) ∈ U ∧
    (∀ z ∈ U, (h7.R q hq0 h2mq) z = (z - (l' + 1))^(h7.r q hq0 h2mq) * R' z) ∧
    AnalyticOn ℂ R' U  := by
  have hA := h7.anever q hq0 h2mq (l' + 1)
  have (z : ℂ) := h7.R_order_eq q hq0 h2mq z
  have := this (l' + 1)
  rw [AnalyticAt.analyticOrderAt_eq_natCast] at this
  obtain ⟨R'', ⟨horder, ⟨hRneq0, hfilter⟩⟩⟩ := this
  let o : ℕ := h7.R_order q hq0 h2mq (↑↑l' + 1)
  have : o ≥ h7.r q hq0 h2mq := by
    simp only [ge_iff_le]
    unfold o
    have HR := r_prop h7 q hq0 h2mq
    simp only [Finset.mem_univ, forall_const] at HR
    have := R_order_eq h7 q hq0 h2mq (l' + 1)
    obtain ⟨hr1,hr2⟩  := HR
    have hr2 := hr2 (l')
    rw [this] at hr2
    simp only [Nat.cast_le] at hr2
    exact hr2

  let R' (z : ℂ) := ((z - (l' + 1))^(o - h7.r q hq0 h2mq)) * R'' z
  use R'
  rw [Filter.eventually_iff_exists_mem] at hfilter
  obtain ⟨U, ⟨hU, hU_prop⟩⟩ := hfilter
  have := AnalyticAt.exists_mem_nhds_analyticOnNhd horder
  obtain ⟨U2, hU2, hU2prop⟩ := this
  rw [mem_nhds_iff] at hU2
  obtain ⟨U'', hU'', hU''prop1, hU''prop2⟩ := hU2
  have hU''hprop3 : U'' ∈ nhds (↑↑l' + 1) := by
    exact IsOpen.mem_nhds hU''prop1 hU''prop2

  use (U ∩ U'')
  constructor
  · simp only [Filter.inter_mem_iff]; exact ⟨hU, hU''hprop3⟩
  · constructor
    · simp only [mem_inter_iff]
      constructor
      · apply mem_of_mem_nhds hU
      · apply mem_of_mem_nhds hU''hprop3
    · constructor
      · intros z hz
        unfold R'
        have : (z - (l' + 1)) ^ (h7.r q hq0 h2mq : ℕ) *
           (z - (l' + 1)) ^ (o - h7.r q hq0 h2mq) = (z - (l' + 1)) ^ (o) := by
            rw [← pow_add]
            rw [sub_eq_add_neg]
            congr
            simp_all only [ne_eq, ge_iff_le, smul_eq_mul, add_tsub_cancel_of_le, o]

        rw [← mul_assoc, this]
        unfold R o
        simp only [smul_eq_mul] at hU_prop z hz
        simp only [mem_inter_iff] at hz
        exact  hU_prop z hz.1
      ·
        · intros x hx
          simp only [mem_inter_iff] at hx
          obtain ⟨hx1,hx2⟩ := hx
          refine analyticWithinAt ?_
          unfold R'
          refine fun_mul ?_ ?_
          · apply Differentiable.analyticAt
            · apply Differentiable.fun_pow
              · simp only [differentiable_fun_id,
                 differentiable_const, Differentiable.fun_sub]
          · apply AnalyticOn.analyticAt (𝕜  := ℂ) (f:= R'') (z := x) (s:=U'') ?_
            rw [IsOpen.analyticOn_iff_analyticOnNhd]
            · exact fun x a ↦ hU2prop x (hU'' a)
            · exact hU''prop1
            · rw [IsOpen.mem_nhds_iff]
              · exact hx2
              · exact hU''prop1
  · fun_prop

def R'U (l' : Fin (h7.m)) : ℂ → ℂ := (exists_R'_at_l'_plus_one h7 q hq0 h2mq l').choose

def U (l' : Fin (h7.m)) : Set ℂ :=
  (exists_R'_at_l'_plus_one h7 q hq0 h2mq l').choose_spec.choose

def R'prop (l' : Fin (h7.m)) :
  ((U h7 q hq0 h2mq l') ∈ nhds (l' + 1 : ℂ)) ∧ ↑↑l' + 1 ∈ (U h7 q hq0 h2mq l') ∧
  (∀ z ∈ (U h7 q hq0 h2mq l'), (h7.R q hq0 h2mq) z =
    (z - (↑↑l' + 1)) ^ h7.r q hq0 h2mq * (R'U h7 q hq0 h2mq l') z)
   ∧ AnalyticOn ℂ (R'U h7 q hq0 h2mq l') (U h7 q hq0 h2mq l') := by
  exact (exists_R'_at_l'_plus_one h7 q hq0 h2mq l').choose_spec.choose_spec

def R'R (l' : Fin (h7.m)) : ℂ → ℂ := fun z =>
  (h7.R q hq0 h2mq) z * (z - (↑l' + 1))^(-(h7.r q hq0 h2mq) : ℤ)

def R' (l' : Fin (h7.m)) : ℂ → ℂ :=
  let R'U := R'U h7 q hq0 h2mq l'
  let R'R := R'R h7 q hq0 h2mq l'
  let U := U h7 q hq0 h2mq l'
  letI : ∀ z, Decidable (z ∈ U) := by
    intros z
    exact Classical.propDecidable (z ∈ U)
  fun z =>
    if z = l' + 1 then
      R'U z
    else
      R'R z

-- lemma: R' is equal to R'_nhd on U
lemma R'_eq_R'U (l' : Fin (h7.m)) :
  let R' := h7.R' l'
  let R'U := R'U h7 q hq0 h2mq l'
  let U := h7.U q hq0 h2mq l'
  ∀ z ∈ U, h7.R' q hq0 h2mq l' z = h7.R'U q hq0 h2mq l' z := by
    intros R' R'U U z hz
    unfold Setup.R'
    split_ifs
    · rfl
    · unfold R'R
      have R'prop := (R'prop h7 q hq0 h2mq l').2.2.1 z hz
      rw [R'prop]
      unfold Setup.R'U
      rw [mul_comm, ← mul_assoc]
      have : (z - (↑↑l' + 1)) ^ (-(h7.r q hq0 h2mq) : ℤ) *
          (z - (↑↑l' + 1)) ^ (h7.r q hq0 h2mq) = 1 := by
        rw [← zpow_natCast]
        simp only [zpow_neg]
        refine inv_mul_cancel₀ ?_
        intro H
        simp only [zpow_natCast, pow_eq_zero_iff', ne_eq] at H
        have : ¬z = ↑↑l' + 1 := by simp_all only [not_false_eq_true, U]
        apply this
        obtain ⟨H1,H2⟩ := H
        rw [sub_eq_zero] at H1
        exact H1
      rw [this]
      simp only [one_mul]

lemma R'_eq_R'R (l' : Fin (h7.m)) :
  let R' := h7.R' q hq0 h2mq l'
  let R'R := h7.R'R q hq0 h2mq l'
  ∀ z ∈ {z : ℂ| z ≠ l' + 1}, R' z = R'R z := by
    intros R' R'R z hz
    unfold R'
    unfold Setup.R' Setup.R'R
    simp only [mem_setOf_eq] at hz
    split
    · rename_i h
      subst h
      simp_all only [ne_eq, not_true_eq_false]
    · rfl

lemma R'R_analytic (l' : Fin (h7.m)) :
  let R'R := h7.R'R q hq0 h2mq l'
  AnalyticOn ℂ R'R {z : ℂ | z ≠ l' + 1} := by
    unfold R'R
    simp only
    refine AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mono
      apply analyticOn_univ.mpr fun x a ↦ (h7.anever q hq0 h2mq) x
      simp only [Set.subset_univ]
    · apply AnalyticOn.fun_zpow ?_
      intros z hz
      simp only [mem_setOf_eq] at hz
      exact sub_ne_zero_of_ne hz
      apply AnalyticOn.sub analyticOn_id analyticOn_const

lemma R'analytic (l' : Fin (h7.m)) :
  ∀ z : ℂ, AnalyticAt ℂ (R' h7 q hq0 h2mq l') z := by
    intros z
    by_cases H : z = l' + 1
    · have R'prop := (R'prop h7 q hq0 h2mq l')
      have hAnalyticOn :
          AnalyticOn ℂ (R' h7 q hq0 h2mq l') (h7.U q hq0 h2mq l') := by
        have hs :
            EqOn (R'U h7 q hq0 h2mq l') (R' h7 q hq0 h2mq l') (h7.U q hq0 h2mq l') := by
          have := (R'_eq_R'U h7 q hq0 h2mq l')
          simp only at this
          intro z' hz'
          subst H
          simp_all only
        exact (analyticOn_congr hs).1 R'prop.2.2.2
      have hU : (h7.U q hq0 h2mq l') ∈ nhds z := by
        simpa [H] using R'prop.1
      exact
        AnalyticOn.analyticAt (f := R' h7 q hq0 h2mq l') (z := z) (s := h7.U q hq0 h2mq l')
          hAnalyticOn (hU := hU)
    ·
      have hAnalyticOn :
          AnalyticOn ℂ (R' h7 q hq0 h2mq l') {z : ℂ | z ≠ l' + 1} := by
        have hs :
            EqOn (R'R h7 q hq0 h2mq l') (R' h7 q hq0 h2mq l') {z : ℂ | z ≠ l' + 1} := by
          have := R'_eq_R'R h7 q hq0 h2mq l'
          simp only at this
          intros z' hz'
          aesop
        exact (analyticOn_congr hs).1 (R'R_analytic h7 q hq0 h2mq l')
      have hU : ({z : ℂ | z ≠ l' + 1} : Set ℂ) ∈ nhds z := by
        refine IsOpen.mem_nhds isOpen_ne ?_
        simpa [Set.mem_setOf_eq] using H
      exact
        AnalyticOn.analyticAt (f := R' h7 q hq0 h2mq l') (z := z) (s := {z : ℂ | z ≠ l' + 1})
          hAnalyticOn (hU := hU)
      -- have := R'_eq_R'R h7 q hq0 h2mq l'
      --   simp only at this
      --   intros z' hz'
      --   aesop
      -- exact (analyticOn_congr hs).1 (R'R_analytic h7 q hq0 h2mq l')
      -- apply IsOpen.mem_nhds isOpen_ne
      -- simp only [ne_eq, mem_setOf_eq, H, not_false_eq_true]

lemma R'onC (l' : Fin (h7.m)) :
  let R' := R' h7 q hq0 h2mq l'
  ∀ z : ℂ, (h7.R q hq0 h2mq) z = (z - (l' + 1))^(h7.r q hq0 h2mq) * R' z := by
  intros R' z
  let U := (exists_R'_at_l'_plus_one
    h7 q hq0 h2mq l').choose_spec.choose
  unfold R'
  unfold Setup.R'
  split
  · have R'prop := (R'prop h7 q hq0 h2mq l')
    simp only at R'prop
    apply R'prop.2.2.1
    have : z = ↑↑l' + 1 := by
      rename_i H
      subst H
      simp_all only
    rw [this]
    apply R'prop.2.1
  · unfold R'R
    rw [mul_comm, mul_assoc]
    have : (z - (↑↑l' + 1)) ^ (-(h7.r q hq0 h2mq) : ℤ) *
        (z - (↑↑l' + 1)) ^ (h7.r q hq0 h2mq) = 1 := by
      rw [← zpow_natCast]
      simp only [zpow_neg]
      refine inv_mul_cancel₀ ?_
      intros H
      simp only [zpow_natCast, pow_eq_zero_iff', ne_eq] at H
      obtain ⟨H1,H2⟩ := H
      have : ¬z = ↑↑l' + 1 := by simp_all only [not_false_eq_true]
      apply this
      rwa [sub_eq_zero] at H1
    rw [this]
    simp only [mul_one]

def ks : Finset ℂ := Finset.image (fun (k': ℕ) => (k' + 1 : ℂ)) (Finset.range h7.m)

omit [DecidableEq (h7.K →+* ℂ)] in
lemma z_in_ks {z : ℂ} : z ∈ (h7.ks) ↔ ∃ k': Fin (h7.m), z = k' + 1 := by
  apply Iff.intro
  · intros hz
    dsimp [ks] at hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k',hk'⟩ := hz
    refine Fin.exists_iff.mpr ?_
    use k', hk'.1
    simp_all only
  · intros hk
    obtain ⟨k, hk⟩ := hk
    dsimp [ks]
    rw [hk]
    subst hk
    simp_all only [Finset.mem_image, Finset.mem_range,
      add_left_inj, Nat.cast_inj, exists_eq_right, Fin.is_lt]

def S.U : Set ℂ := (h7.ks)ᶜ

omit [DecidableEq (h7.K →+* ℂ)] in
lemma S.U_ne_of_mem {z : ℂ} (hz : z ∈ (S.U h7)) (k' : Fin (h7.m)) : z ≠ (k' + 1 : ℂ) := by
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
  intro H
  apply hz k' k'.isLt H.symm

lemma S.U_is_open : IsOpen (S.U h7) := by
  unfold S.U
  rw [EMetric.isOpen_iff]
  intros z hz
  have : (Finset.image (dist z) (ks h7)).Nonempty := by
    dsimp [ks]
    simp only [Finset.image_nonempty, nonempty_range_iff, ne_eq]
    exact Nat.add_one_ne_zero (2 * h7.h + 1)
  let ε := Finset.min' (Finset.image (dist z) (ks h7)) this
  use ENNReal.ofReal ε
  refine ⟨by aesop, ?_⟩
  · simp only [Metric.emetric_ball]
    dsimp [ε]
    rw [Set.compl_def]
    refine subset_setOf.mpr ?_
    intros x hx
    simp only [mem_coe]
    rw [Metric.mem_ball] at hx
    intros H
    rw [lt_min'_iff] at hx
    simp only [Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at hx
    have := hx x H
    rw [dist_comm z x] at this
    apply lt_irrefl (dist x z) this

lemma S.U_nhds :
  ∀ z, z ∈ U h7 → (S.U h7) ∈ nhds z :=
  fun z hz => IsOpen.mem_nhds (U_is_open h7) hz

omit [DecidableEq (h7.K →+* ℂ)] in
lemma zneq0 : ∀ {z : ℂ} (_ : z ∈ S.U h7) (k' : Fin (h7.m)), (z - (k' + 1 : ℂ)) ≠ 0 := by
  intros z hz k'
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  intros H
  apply hz k' k'.isLt
  symm
  rw [sub_eq_zero] at H
  exact H

lemma z_in_ks' (z : ℂ) : z ∈ (h7.ks) ↔ ∃ k': Fin (h7.m), z = k' + 1 := by
  apply Iff.intro
  · intros hz
    dsimp [ks] at hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k', hk'⟩ := hz
    refine Fin.exists_iff.mpr ?_
    use k', hk'.1
    simp_all only
  · intros hk
    obtain ⟨k, hk⟩:=hk
    dsimp [ks]
    rw [hk]
    subst hk
    simp_all only [Finset.mem_image, Finset.mem_range,
      add_left_inj, Nat.cast_inj, exists_eq_right, Fin.is_lt]

lemma S.U_ne_of_mem' {z : ℂ} (hz : z ∈ (S.U h7)) (k' : Fin (h7.m)) : z ≠ (k' + 1 : ℂ) := by
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
  intro H
  apply hz k' k'.isLt H.symm

def SR : ℂ → ℂ := fun z =>
  (h7.R q hq0 h2mq) z * (h7.r q hq0 h2mq).factorial *
    ((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
      (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq))

lemma SR_analytic_S.U : AnalyticOn ℂ (h7.SR q hq0 h2mq) (S.U h7) := by
  unfold Setup.SR
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := h7.anever q hq0 h2mq
        apply AnalyticOn.mono (f:=(h7.R q hq0 h2mq)) (s:=(S.U h7))
        apply analyticOn_univ.mpr fun x a ↦ this x
        simp only [Set.subset_univ]
      · exact analyticOn_const
    · apply AnalyticOn.fun_zpow
      · apply AnalyticOn.mono
        · refine analyticOn_univ_iff_differentiable.mpr ?_
          refine (fun_sub_iff_left ?_).mpr ?_
          simp only [differentiable_const]
          simp only [differentiable_fun_id]
        · have : (S.U h7) ⊆ Set.univ := by exact fun ⦃a⦄ a ↦ trivial
          exact this
      · intros z hz
        dsimp [S.U, ks] at hz
        simp only [coe_image, coe_range, mem_compl_iff,
          Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
        have := hz (h7.l₀' q hq0 h2mq)
        intros HC
        apply this
        simp only [Fin.is_lt]
        rw [sub_eq_zero] at HC
        rw [HC]
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    refine AnalyticOn.div (analyticOn_const) ?_ ?_
    · refine DifferentiableOn.analyticOn ?_ (S.U_is_open h7)
      fun_prop
    · intros x hx
      dsimp [S.U, ks] at hx
      simp only [coe_image, coe_range, mem_compl_iff,
        Set.mem_image, Set.mem_Iio, not_exists, not_and] at hx
      have := hx u hu.1
      intros H
      apply this
      rw [sub_eq_zero] at H
      exact id (Eq.symm H)

lemma SR_Analytic (z : ℂ) (hz : z ∈ S.U h7) : AnalyticAt ℂ (h7.SR q hq0 h2mq) z :=
  AnalyticOn.analyticAt (f:=(h7.SR q hq0 h2mq)) (z:=z) (s:=S.U h7)
    (SR_analytic_S.U h7 q hq0 h2mq) (hU:= S.U_nhds h7 z hz)

def SRl0 : ℂ → ℂ := fun z =>
  (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq)) z * ((h7.r q hq0 h2mq).factorial)  *
    (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
    (((h7.l₀' q hq0 h2mq +1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq))

def SRl (l' : Fin (h7.m)) : ℂ → ℂ := fun z =>
  (h7.R' q hq0 h2mq l') z *
    (h7.r q hq0 h2mq).factorial *
    ((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ (Finset.range (h7.m) \ ({↑(h7.l₀' q hq0 h2mq : ℕ)} ∪ {↑(l' : ℕ)})),
      (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) *
    (((h7.l₀' q hq0 h2mq + 1)- (l' + 1)) ^ (h7.r q hq0 h2mq))

def S : ℂ → ℂ :=
  fun z =>
    if H : ∃ (k' : Fin (h7.m)), z = (k' : ℂ) + 1 then
      if z = (h7.l₀' q hq0 h2mq + 1) then
        h7.SRl0 q hq0 h2mq z
      else
        h7.SRl q hq0 h2mq (H.choose) z
    else
      h7.SR q hq0 h2mq z

lemma SR_eq_SRl0 {z : ℂ} :
  z ∈ (S.U h7) → (h7.SRl0 q hq0 h2mq) z = (h7.SR q hq0 h2mq) z := by
  intros hz
  unfold S.U at *
  unfold SRl0
  dsimp [SR]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast]
  dsimp [ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := h7.R'onC q hq0 h2mq (h7.l₀' q hq0 h2mq) z
  simp only at this
  rw [this]; clear this
  simp only [← mul_assoc]
  nth_rw 6 [mul_comm]
  rw [mul_assoc  (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq) z)
    ((z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ h7.r q hq0 h2mq)]
  rw [mul_comm ((z - (↑↑(h7.l₀' q hq0 h2mq) + 1))
     ^ h7.r q hq0 h2mq) ↑(h7.r q hq0 h2mq).factorial]
  simp only [mul_assoc]
  congr
  rw [← one_mul (a:= ∏ k' ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
    ((↑↑(h7.l₀' q hq0 h2mq) + 1 - (↑k' + 1)) / (z - (↑k' + 1))) ^ h7.r q hq0 h2mq)]
  simp only [← mul_assoc]
  have H : ((z - ↑↑(h7.l₀' q hq0 h2mq)) ^ (h7.r q hq0 h2mq) )⁻¹ =
      (z - ↑↑(h7.l₀' q hq0 h2mq)) ^ (- (h7.r q hq0 h2mq) : ℤ) := by
      simp only [zpow_neg, zpow_natCast]
  have : 1 =  (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ ↑(h7.r q hq0 h2mq) *
      (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ (-↑((h7.r q hq0 h2mq) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
    symm
    apply Complex.mul_inv_cancel
    intros Hz
    simp only [pow_eq_zero_iff', ne_eq] at Hz
    have : (h7.l₀' q hq0 h2mq) < h7.m :=  by simp only [Fin.is_lt]
    have H := hz  ↑((h7.l₀' q hq0 h2mq)) this
    apply H
    rw [sub_eq_add_neg] at Hz
    rw [add_eq_zero_iff_eq_neg] at Hz
    simp only [neg_neg] at Hz
    symm
    rw [Hz.1]
  simp only [zpow_neg, zpow_natCast] at this
  nth_rw 1 [this]
  simp only [mul_one]

--fix l+1
lemma SR_eq_SRl {z : ℂ} (l' : Fin (h7.m)) (hl : l' ≠ h7.l₀' q hq0 h2mq) :
    z ∈ (S.U h7) → (h7.SRl q hq0 h2mq l') z = (h7.SR q hq0 h2mq) z := by
  intros hz
  unfold Setup.S.U at *
  dsimp [Setup.SR, Setup.SRl]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast]
  dsimp [ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := R'onC h7 q hq0 h2mq l' z
  simp only at this
  rw [this]; clear this
  simp only [← mul_assoc]
  nth_rw 8 [mul_comm]
  rw [mul_assoc  (h7.R' q hq0 h2mq (l') z) ((z - (↑↑(l') + 1)) ^ h7.r q hq0 h2mq)]
  rw [mul_comm ((z - (↑↑(l') + 1)) ^ h7.r q hq0 h2mq) ↑(h7.r q hq0 h2mq).factorial]
  unfold R'
  simp only [mul_assoc]
  have : l' < h7.m := by simp only [Fin.is_lt]
  have H := (hz l' this)
  simp only at H
  have : 1 =  (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ ↑(h7.r q hq0 h2mq) *
      (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ (-↑((h7.r q hq0 h2mq) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
    symm
    apply Complex.mul_inv_cancel
    intros Hz
    simp only [pow_eq_zero_iff', ne_eq] at Hz
    have : (h7.l₀' q hq0 h2mq) < h7.m :=  by simp only [Fin.is_lt]
    have H := hz  ↑((h7.l₀' q hq0 h2mq)) this
    apply H
    rw [sub_eq_add_neg] at Hz
    rw [add_eq_zero_iff_eq_neg] at Hz
    simp only [neg_neg] at Hz
    symm
    rw [Hz.1]
  split
  · rename_i H
    rw [H]
    simp only [add_sub_add_right_eq_sub, sub_self,
      mul_eq_mul_left_iff, Nat.cast_eq_zero]
    left; left
    rw [zero_pow]
    simp only [zero_mul, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', ne_eq]
    right
    right
    constructor
    by_contra HR
    apply hl
    (expose_names; exact False.elim (hz (↑l') this_1 (id (Eq.symm H))))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
  · nth_rw 6 [← mul_assoc]
    nth_rw 5 [← mul_assoc]
    nth_rw 8 [mul_comm]
    simp only [mul_assoc]
    simp only [mul_eq_mul_left_iff, inv_eq_zero,
      pow_eq_zero_iff', ne_eq, Nat.cast_eq_zero]
    left
    left
    left
    rw [mul_comm]
    nth_rw 2 [mul_comm]
    clear this
    have H :=  Finset.prod_union
      (s₁:= Finset.range h7.m \ ({↑(h7.l₀' q hq0 h2mq) }∪ {↑l'}))
      (s₂:= {↑l'})
      (f:= fun k' => ((↑↑(h7.l₀' q hq0 h2mq) + 1 -
       (↑k' + 1)) / (z - (↑k' + 1))) ^ h7.r q hq0 h2mq)
      (by aesop)
    have : Finset.range h7.m \ ({↑(h7.l₀' q hq0 h2mq) }∪ {↑l'}) ∪ {↑l'}
     = Finset.range h7.m \ {(↑(h7.l₀' q hq0 h2mq))} := by grind

    simp only [Finset.prod_singleton] at H
    rw [this] at H
    rw [H]; clear H this
    rw [mul_comm]
    simp only [mul_assoc]
    congr
    simp only [add_sub_add_right_eq_sub]
    rw [← inv_mul_eq_div, mul_pow, mul_comm]
    simp only [← mul_assoc]
    rw [← mul_pow, mul_inv_cancel₀]
    · simp only [one_pow, one_mul]
    grind only


lemma S_eq_SR {z : ℂ} :
  z ∈ (S.U h7) → h7.SR q hq0 h2mq z = h7.S q hq0 h2mq z := by
  intros hz
  unfold S.U at *
  unfold S
  split
  · rename_i H1
    unfold ks at hz
    simp only [coe_image, mem_compl_iff,
    Set.mem_image, not_exists,
      not_and] at hz
    obtain ⟨x1,hx1⟩ := H1
    have := hz x1
    simp only [coe_range, Set.mem_Iio, Fin.is_lt, forall_const] at this
    rw [hx1] at this
    subst hx1
    simp_all only [not_true_eq_false]
  · rfl


lemma dist_lt_zero (n m : ℕ) : dist (n : ℂ) (m : ℂ) < 1 ↔  n = m := by
  apply Iff.intro
  rw [Complex.dist_eq]
  by_cases H : m ≤ n
  · have : norm (((n : ℂ)) - (m : ℂ)) = (n - m : ℕ) := by
     norm_cast
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    grind
  · have : norm (((n : ℂ)) - (m : ℂ)) = norm ((m : ℂ) - (n : ℂ)) := by
      calc _ = norm (-((m : ℂ) - (n : ℂ))) := ?_
           _ = norm (((m : ℂ)) - (n : ℂ)) := ?_
      · simp only [neg_sub]
      · symm
        rw [← norm_neg]
    rw [this]
    have : norm (((m : ℂ)) - (n : ℂ)) = (m - n : ℕ) := by
     simp only [not_le] at H
     have : n ≤ m := by grind
     norm_cast
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    grind
  · aesop


--SR_analytic_S.U follow this for srl0 too
lemma SRl_is_analytic_at_ball_of_radius_one (l' : Fin (h7.m)) (hl : l' ≠ h7.l₀' q hq0 h2mq) :
  AnalyticOn ℂ (h7.SRl q hq0 h2mq l') (Metric.ball ((l' : ℂ) + 1) 1) := by
  unfold Setup.SRl
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := h7.R'analytic q hq0 h2mq
        simp only at this
        apply AnalyticOn.mul ?_ ?_
        · exact AnalyticOnNhd.analyticOn fun x a ↦ this l' x
        · exact analyticOn_const
      · apply AnalyticOn.fun_zpow
        · apply AnalyticOn.mono
          · refine analyticOn_univ_iff_differentiable.mpr ?_
            refine (fun_sub_iff_left ?_).mpr ?_
            simp only [differentiable_const]
            simp only [differentiable_fun_id]
          · have : (Metric.ball ((l' : ℂ) + 1) 1) ⊆ Set.univ := by exact fun ⦃a⦄ a ↦ trivial
            exact this
        · intros z hz
          simp only [Metric.mem_ball] at hz
          apply sub_ne_zero_of_ne
          intro H
          rw [H] at hz
          simp only [dist_add_right] at hz
          have : ((h7.l₀' q hq0 h2mq : ℕ) : ℂ)≠ ((l' : ℕ) : ℂ) := by
            intros HC
            apply hl
            simp only [Nat.cast_inj] at HC
            symm
            aesop

          rw [← dist_pos] at this
          have Hdist := (dist_lt_zero ((h7.l₀' q hq0 h2mq)) ↑↑l').1
          have Hdist := Hdist hz
          rw [Hdist] at this
          aesop
    ·
      apply Finset.analyticOn_fun_prod
      intros u hu
      simp only at hu
      apply AnalyticOn.fun_pow
      refine AnalyticOn.div ?_ ?_ ?_
      · exact analyticOn_const
      · refine DifferentiableOn.analyticOn ?_ ?_
        · simp only [differentiableOn_const,
            DifferentiableOn.fun_sub_iff_left]
          refine differentiableOn ?_
          exact differentiable_fun_id
        · exact Metric.isOpen_ball
      · intros x hx
        simp only [Metric.mem_ball] at hx
        simp only [Finset.mem_union, mem_sdiff,
          Finset.mem_range, Finset.mem_singleton] at hu
        cases' hu with h1 h2
        · intros HC
          simp only [not_or] at h2
          obtain ⟨hu, hul0⟩ := h2
          rw [sub_eq_zero] at HC
          rw [HC] at hx
          simp only [dist_add_right] at hx
          rw [← ne_eq] at *
          have Hdist := (dist_lt_zero u ↑↑l').1
          have Hdist := Hdist hx
          rw [Hdist] at hx
          simp only [dist_self, zero_lt_one] at hx
          exact hul0 Hdist
  · exact analyticOn_const

lemma SRl0_is_analytic_at_ball_of_radius_one  :
  AnalyticOn ℂ (h7.SRl0 q hq0 h2mq) (Metric.ball (h7.l₀' q hq0 h2mq + 1) 1) := by
  unfold Setup.SRl0
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · have := h7.R'analytic q hq0 h2mq
      simp only at this
      exact AnalyticOnNhd.analyticOn fun x a ↦ this (h7.l₀' q hq0 h2mq) x
    · exact analyticOn_const
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    refine AnalyticOn.div ?_ ?_ ?_
    · exact analyticOn_const
    · refine DifferentiableOn.analyticOn ?_ ?_
      · simp only [differentiableOn_const, DifferentiableOn.fun_sub_iff_left]
        refine differentiableOn ?_
        exact differentiable_fun_id
      · exact Metric.isOpen_ball
    · intros x hx
      simp only [Metric.mem_ball] at hx
      obtain ⟨hu, hul0⟩ := hu
      have : ((u : ℕ) : ℂ)≠ ((h7.l₀' q hq0 h2mq : ℕ) : ℂ) := by
        intros HC
        apply hul0
        simp only [Nat.cast_inj] at HC
        symm
        aesop
      rw [← dist_pos] at this
      intros HC
      rw [sub_eq_zero] at HC
      rw [HC] at hx
      simp only [dist_add_right] at hx
      have Hdist := (dist_lt_zero u  ↑↑(h7.l₀' q hq0 h2mq)).1
      have Hdist := Hdist hx
      rw [Hdist] at hx
      simp only [dist_self, zero_lt_one] at hx
      exact hul0 Hdist

lemma AnalyticAtEq (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ) :
  (hU : U ∈ nhds z) → z ∈ U → (∀ z ∈ U, f z = g z) → AnalyticAt ℂ f z → AnalyticAt ℂ g z := by
    intros hU _ hfg hf
    exact hf.congr (Filter.eventually_of_mem hU hfg)

lemma holS :
  --∀ x ∈ Metric.ball 0 (m K *(1 + (r/q))) \ (l₀ : ℂ),
  ∀ z, AnalyticAt ℂ (h7.S q hq0 h2mq) z := by
  intros z
  by_cases H : ∃ (k' : Fin (h7.m)), z = (k' : ℂ) + 1
  by_cases Hzl0 : z = h7.l₀' q hq0 h2mq + 1
  · clear H
   -- obtain ⟨l', hl'⟩ := H
    apply AnalyticAtEq (f := h7.SRl0 q hq0 h2mq)
      (U := (Metric.ball (h7.l₀' q hq0 h2mq + 1) 1))
    · rw [Hzl0]
      refine IsOpen.mem_nhds ?_ ?_
      simp only [Metric.isOpen_ball]
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · rw [Hzl0]
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    ·
      intros z hz
      by_cases H : z = ↑↑(h7.l₀' q hq0 h2mq) + 1
      ·
        unfold S
        let H1 : ∃ (k' : Fin h7.m), z = ↑↑k' + 1 := by
          use (h7.l₀' q hq0 h2mq)


        simp only [H1]
        dsimp
        simp only [H]
        dsimp
      ·
        have: z ∈ S.U h7 := by
          unfold S.U ks
          simp only [coe_image, mem_compl_iff,
            Set.mem_image, not_exists, not_and]
          intros k hk

          by_cases H1 :  k = (h7.l₀' q hq0 h2mq)
          · rw [H1];
            subst H1 Hzl0
            simp_all only [Metric.mem_ball, coe_range,
              Set.mem_Iio, Fin.is_lt]
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only [dist_self, zero_lt_one, not_true_eq_false]
          · intros HC
            simp only [Metric.mem_ball] at hz
            rw [← HC] at hz
            simp only [dist_add_right] at hz
            rw [dist_lt_zero] at hz
            apply H1
            exact hz
        have HS1 := h7.SR_eq_SRl0 q hq0 h2mq this
        have HS := h7.S_eq_SR q hq0 h2mq this
        rw [HS] at HS1
        exact HS1


    · apply AnalyticOn.analyticAt (f:= h7.SRl0 q hq0 h2mq)
      · change (Metric.ball (↑↑(h7.l₀' q hq0 h2mq) + 1) 1) ∈ nhds z
        rw [Hzl0]
        apply Metric.ball_mem_nhds
        simp only [zero_lt_one]
      · exact (h7.SRl0_is_analytic_at_ball_of_radius_one q hq0 h2mq)

  ·
    obtain ⟨l', hl'⟩ := H
    -- rw [hl'] at Hzl0
    -- simp only [add_left_inj, Nat.cast_inj] at Hzl0
    -- have : ¬l' = (h7.l₀' q hq0 h2mq) := by
    --     intros HL
    --     rw [HL] at Hzl0
    --     apply Hzl0
    --     rfl
    --
    --clear Hzl0
    --by_cases H' : z = l' + 1
    apply AnalyticAtEq  (f := h7.SRl q hq0 h2mq l')
       (U:= (Metric.ball ((l' : ℂ) + 1) 1))
    · rw [hl']
      refine IsOpen.mem_nhds ?_ ?_
      simp only [Metric.isOpen_ball]
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · rw [hl']
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · intros z hzz
      by_cases H1 :  (z : ℂ) = ↑↑l' + 1
      · unfold S
        have H1 : ∃ (k' : Fin h7.m), z = ↑↑k' + 1 := by
          use l'


        simp only [H1]
        dsimp
        rename_i Hz2
        have : z ≠ ↑↑(h7.l₀' q hq0 h2mq) + 1 := by
          rw [Hz2]
          rw [← hl']
          exact Hzl0

        simp only [this]
        dsimp
        have := H1.choose_spec
        have : H1.choose = l' := by
          have := Eq.trans  Hz2.symm this
          simp only [add_left_inj, Nat.cast_inj] at this
          exact Fin.eq_of_val_eq (id (Eq.symm this))

        -- note: violent transitivity


        conv => enter [1] ; rw [← this]








        --simp only [Hzl0]
      · have HZ : z ∈ S.U h7 := by
          unfold S.U ks
          simp only [coe_image, mem_compl_iff,
            Set.mem_image, not_exists, not_and]
          intros k hk
          intros HC
          rw [← HC] at hzz
          simp only [Metric.mem_ball] at hzz
          simp only [dist_add_right] at hzz
          rw [dist_lt_zero] at hzz
          apply H1
          rw [← hzz]
          symm
          exact HC
        have :  l' ≠ h7.l₀' q hq0 h2mq := by
          intro Hcontra
          apply Hzl0
          rw [hl', Hcontra]
        have HS1 := h7.SR_eq_SRl q hq0 h2mq l'  this HZ
        have HS := h7.S_eq_SR q hq0 h2mq HZ
        rw [HS] at HS1
        exact HS1

    · apply AnalyticOn.analyticAt (f:= h7.SRl q hq0 h2mq l')
      · change (Metric.ball (↑↑(l') + 1) 1) ∈ nhds z
        rw [hl']
        apply Metric.ball_mem_nhds
        simp only [zero_lt_one]
      · have :  l' ≠ h7.l₀' q hq0 h2mq := by
          intro Hcontra
          apply Hzl0
          rw [hl', Hcontra]

        exact (h7.SRl_is_analytic_at_ball_of_radius_one q hq0 h2mq l' this)

  ·
    apply AnalyticAtEq (U := S.U h7) (f := h7.SR q hq0 h2mq)
    · have : z ∈ S.U h7 := by
        unfold S.U ks
        simp only [coe_image, coe_range, mem_compl_iff,
          Set.mem_image, Set.mem_Iio, not_exists, not_and]
        simp only [not_exists] at H
        intros x hx
        have := H ⟨x,hx⟩
        simp only at this
        intros HC
        apply this
        rw [HC]

      have := S.U_nhds h7 z this
      exact this
    · have : z ∈ S.U h7 := by
        unfold S.U ks
        simp only [coe_image, coe_range, mem_compl_iff,
          Set.mem_image, Set.mem_Iio, not_exists, not_and]
        simp only [not_exists] at H
        intros x hx
        have := H ⟨x,hx⟩
        simp only at this
        intros HC
        apply this
        rw [HC]

      exact this
    · intros z hz
      apply h7.S_eq_SR q hq0 h2mq
      simp only [not_exists] at H
      · exact hz
    · apply h7.SR_Analytic q hq0 h2mq z ?_
      have : z ∈ S.U h7 := by
        unfold S.U ks
        simp only [coe_image, coe_range, mem_compl_iff, Set.mem_image,
          Set.mem_Iio, not_exists,
          not_and]
        simp only [not_exists] at H
        intros x hx
        have := H ⟨x,hx⟩
        simp only at this
        intros HC
        apply this
        rw [HC]
      exact this

lemma hcauchy :
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(0, h7.m *(1 + (h7.r q hq0 h2mq / q))),
  (z - (h7.l₀' q hq0 h2mq + 1 : ℂ))⁻¹ * (h7.S q hq0 h2mq) z) =
    (h7.S q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) := by
  apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  · exact countable_empty
  · have : (h7.l₀' q hq0 h2mq + 1 : ℂ) ∈
       Metric.ball 0 (h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)) := by
      simp only [Metric.mem_ball, dist_zero_right]

      have H1 : (h7.l₀' q hq0 h2mq + 1: ℝ) ≤ h7.m := by
        have:= ((h7.l₀' q hq0 h2mq)).isLt
        norm_cast

      have H2 : 1 < (↑h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)) := by
        refine Nat.one_lt_mul_iff.mpr ?_
        · refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), ?_⟩
          · constructor
            simp only [add_pos_iff, zero_lt_one, Nat.div_pos_iff, true_or]
            left
            exact Nat.one_lt_succ_succ (2 * h7.h)

    --a< c and b < d iff a*b< c*d
      norm_cast at *
      simp only [Nat.cast_add, Nat.cast_one, gt_iff_lt]
      rw [← mul_one (a:=(h7.l₀' q hq0 h2mq : ℝ) + 1)]
      apply mul_lt_mul'
      · norm_cast
      · simp only [lt_add_iff_pos_right]
        refine div_pos ?_ ?_
        · simp only [Nat.cast_pos];exact r_qt_0 h7 q hq0 h2mq
        · simp only [Nat.cast_pos];exact hq0
      · simp only [zero_le_one]
      · simp only [Nat.cast_pos];exact Nat.zero_lt_succ (2 * h7.h + 1)

    exact this
  · intros x hx
    apply @DifferentiableWithinAt.continuousWithinAt ℂ _ _ _ _ _ _ _ _ _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact AnalyticAt.differentiableAt (holS h7 q hq0 h2mq x)
  · intros x hx
    apply AnalyticAt.differentiableAt (holS h7 q hq0 h2mq x)

-- use k=r
-- use z0= l0'+1
-- R is R
-- for the application
-- one of R1 is R'

-- (hz : z ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))))
--#check systemCoeffs_bar

def systemCoeffsff_foo_S : ρᵣ h7 q hq0 h2mq =
  Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ)) *
   (h7.S q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1) := by
  dsimp [ρᵣ]
  congr
  have HAE : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
    intros z
    exact anever h7 q hq0 h2mq z
  let R₁ : ℂ → ℂ := R' h7 q hq0 h2mq ((h7.l₀' q hq0 h2mq))
  have HR1 : ∀ (z : ℂ), AnalyticAt ℂ R₁ z := by
    unfold R₁
    intros z
    apply R'analytic h7 q hq0 h2mq (h7.l₀' q hq0 h2mq) z
  have hR₁ : ∀ (z : ℂ), (h7.R q hq0 h2mq) z =
    ((z - (h7.l₀' q hq0 h2mq + 1)) ^ (h7.r q hq0 h2mq)) * (R₁ z) := by
    intros z
    rw [h7.R'onC]
  have hr : h7.r q hq0 h2mq ≤ h7.r q hq0 h2mq := by rfl
  have :
   ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧
    (∀ z, deriv^[(h7.r q hq0 h2mq)] (R h7 q hq0 h2mq) z =
   (z - ( l₀' h7 q hq0 h2mq + 1))^((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)) *
    ((h7.r q hq0 h2mq).factorial/((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)).factorial * R₁ z +
       (z - ( l₀' h7 q hq0 h2mq + 1))* R₂ z)) := by
    apply iterated_deriv_mul_pow_sub_of_analytic (z₀ := l₀' h7 q hq0 h2mq + 1)
        --HAE
        HR1 hR₁ (r := r h7 q hq0 h2mq) (k := r h7 q hq0 h2mq) hr
  simp only [tsub_self, pow_zero, Nat.factorial_zero,
  Nat.cast_one, div_one, one_mul] at this
  have := this
  obtain ⟨R2,hR⟩ := this
  clear this
  obtain ⟨hR1, hR2⟩ := hR
  rw [hR2]
  unfold R₁
  symm
  dsimp [S]
  simp only [add_left_inj, Nat.cast_inj, exists_apply_eq_apply', ↓reduceDIte]
  dsimp
  · unfold SRl0
    simp only [add_sub_add_right_eq_sub]
    rw [mul_comm   ↑(h7.r q hq0 h2mq).factorial
      (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1))]
    nth_rw 2 [← mul_one
      (a := (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1)) *
      ↑(h7.r q hq0 h2mq).factorial) ]
    congr
    simp only [mul_one, sub_self, zero_mul, add_zero]
    nth_rw 2 [← mul_one (a:= h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq)
      ((h7.l₀' q hq0 h2mq : ℂ) + 1) * ↑(h7.r q hq0 h2mq).factorial)]
    congr
    have H1 :  ∏ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}, 1 = (1 : ℂ) := by
      simp only [prod_const_one]
    congr
    rw [← H1]
    apply Finset.prod_congr
    rfl
    intros x hx
    rw [div_self]
    simp only [one_pow]
    have : ∀ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      ↑↑(h7.l₀' q hq0 h2mq) ≠ x := by
        intros x hx
        grind only [= mem_sdiff, = Finset.mem_singleton]
    have := this x hx
    intros HC
    rw [sub_eq_zero] at HC
    norm_cast at HC

lemma S_eq_SR_on_circle :
  ∀ (z : ℂ) (hz : z ∈ Metric.sphere 0
    (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))),
  h7.S q hq0 h2mq z = h7.SR q hq0 h2mq z := by
  intros z hz
  unfold S
  split
  · rename_i H1
    obtain ⟨k',hk'⟩ := H1
    have : norm z ≤ h7.m := by
      rw [hk']
      norm_cast
      apply Fin.isLt
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz] at this
    by_contra HC
    apply absurd (this)
    simp only [not_le]
    nth_rw 1 [← mul_one (a:=(h7.m:ℝ))]
    apply mul_lt_mul' (le_refl _)
    · simp only [lt_add_iff_pos_right]
      refine div_pos ?_ ?_
      · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
      · simp only [Nat.cast_pos]; exact hq0
    · simp only [zero_le_one]
    · simp only [Nat.cast_pos];exact Nat.zero_lt_succ (2 * h7.h + 1)
  · rfl

end Setup

end
