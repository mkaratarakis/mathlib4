/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
These are some auxiliary lemmata covering the algebraic part of the proof of the
Gelfond–Schneider theorem.
-/
@[expose] public section

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars true

open BigOperators Module.Free Fintype NumberField FiniteDimensional
  Matrix Set Polynomial Finset IntermediateField Complex

noncomputable section

lemma ExistsAlgInt {K : Type*} [Field K] [NumberField K] (α : K) :
  ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

def c'_both {K : Type*} [Field K] [NumberField K] (α : K) :
   {c : ℤ | c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(ExistsAlgInt α).choose, (ExistsAlgInt α).choose_spec⟩

lemma adjoin_le_adjoin_more (α β : ℂ) (_ : IsAlgebraic ℚ α) (_ : IsAlgebraic ℚ β) :
  (adjoin _ {α} ≤ adjoin ℚ {α, β}) ∧ (adjoin _ {β} ≤ adjoin ℚ {α, β}) :=
  ⟨by apply adjoin.mono; intros x hx; left; exact hx,
   by apply adjoin.mono; intros x hx; right; exact hx⟩

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

lemma getElemsInNF (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
      ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (σ : K →+* ℂ) (_ : DecidableEq (K →+* ℂ)),
    ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have  hab := adjoin.mono ℚ {α, β} {α, β, γ}
    fun x hxab => by
      rcases hxab with ⟨hxa, hxb⟩; left;
      simp only
      rename_i h
      simp only [mem_singleton_iff] at h
      subst h
      simp_all only [mem_insert_iff, mem_singleton_iff, true_or, or_true]
  have hac := adjoin.mono ℚ {α, γ} {α, β, γ}
    fun x hx => by rcases hx with ⟨hsf, hff⟩; left; rfl ; rename_i h; aesop;
  use adjoin ℚ {α, β, γ}
  constructor
  use isNumberField_adjoin_alg_numbers α β γ hα hβ hγ
  use { toFun := fun x => x.1, map_one' := rfl, map_mul' := fun x y => rfl
        map_zero' := rfl, map_add' := fun x y => rfl}
  use Classical.typeDecidableEq (↥ℚ⟮α, β, γ⟯ →+* ℂ)
  simp only [exists_and_left, exists_and_right, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.exists, exists_prop, exists_eq_right']
  exact ⟨adjoin_simple_le_iff.1 fun _ hx =>
     hab ((adjoin_le_adjoin_more α β hα hβ).1 hx),
    adjoin_simple_le_iff.1 fun _ hx =>  hab (by
    apply adjoin.mono; intros x hx;
    · right; exact hx;
    · exact hx),
    adjoin_simple_le_iff.1 fun _ hx =>
    hac ((adjoin_le_adjoin_more α γ hα hγ).2 hx)⟩

lemma IsIntegral_assoc (K : Type) [Field K]
{x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
  IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  have : ((x * y * z : ℤ) • α) = (x * y) • (z • α) := by
    simp only [Int.cast_mul, zsmul_eq_mul, mul_assoc (↑x * ↑y : K) z α]
  conv => enter [2]; rw [this]
  apply IsIntegral.smul _ ha

lemma IsIntegral.Cast (K : Type) [Field K] (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
 ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

lemma triple_comm_int (a b c : ℤ) (x y z : ℤ) :
 ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

lemma triple_comm_real (a b c : ℝ) (x y z : ℝ) :
 ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [smul_eq_mul]
  ring

variable [Field K] [NumberField K]

/-- Let α be a non-zero algebraic integer. Then α has a conjugate α(i) with |α(i)| ≥ 1. -/
lemma exists_conjugate_abs_gt_one {α : 𝓞 K} (hα0 : α ≠ 0) :
    ∃ σ : K →+* ℂ, 1 ≤ norm (σ α) := by
  have h_exists_w : ∃ w : InfinitePlace K, 1 ≤ w α := by
    by_contra h_neg; push_neg at h_neg
    let w₀ := (inferInstance : Nonempty (InfinitePlace K)).some
    have h_ge_one : 1 ≤ w₀ α :=
      NumberField.InfinitePlace.one_le_of_lt_one hα0 (fun z _ => h_neg z)
    linarith [h_neg w₀, h_ge_one]
  rcases h_exists_w with ⟨w, hw⟩
  use w.embedding
  rw [← InfinitePlace.norm_embedding_eq] at hw
  exact hw

lemma house_gt_one_of_isIntegral {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    1 ≤ house α := by
  have ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, 1 ≤ ‖σ α‖ := by
    let a : 𝓞 K := ⟨α, hα⟩
    have hα_int_0 : a ≠ 0 := by
      intros H
      apply hα0
      injection H
    apply _root_.exists_conjugate_abs_gt_one (K := K) hα_int_0
  rw [house_eq_sup']
  have h_le_sup := Finset.le_sup' (fun φ : K →+* ℂ ↦ ‖φ α‖₊) (Finset.mem_univ σ)
  exact le_trans hσ h_le_sup

lemma house_alg_int_leq_pow (α : K) (n m : ℕ) (h : n ≤ m) (hα0 : α ≠ 0) (H : IsIntegral ℤ α) :
  house α ^ n ≤ house α ^ m :=
Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨_root_.house_gt_one_of_isIntegral H hα0, h⟩)

lemma house_alg_int_leq_pow' (α : K) (n m : Int) (h_exp : n ≤ m)
    (hα0 : α ≠ 0) (h_int : IsIntegral ℤ α) :
  house α ^ n ≤ house α ^ m := by
  have h_base : 1 ≤ house α := _root_.house_gt_one_of_isIntegral h_int hα0
  exact zpow_le_zpow_right₀ h_base h_exp

lemma house_alg_int_leq_pow_real (α : K) (r s : ℝ) (h_exp : r ≤ s)
    (hα0 : α ≠ 0) (h_int : IsIntegral ℤ α) :
  house α ^ r ≤ house α ^ s := by
  have h_base : 1 ≤ house α := _root_.house_gt_one_of_isIntegral h_int hα0
  exact Real.rpow_le_rpow_of_exponent_le h_base h_exp

lemma house_leq_pow_pow (α : K) (n : ℕ) (hn : n ≠ 0) (hα0 : α ≠ 0)
  (H : IsIntegral ℤ α) : house α ≤ house α ^ n :=
le_self_pow₀ (_root_.house_gt_one_of_isIntegral H hα0) hn

lemma house_leq_one_pow (α : K) (n : ℕ) (hn : n ≠ 0) (hα0 : α ≠ 0)
  (H : IsIntegral ℤ α) :
  1 ≤ house α ^ n :=
(_root_.house_gt_one_of_isIntegral H hα0).trans (_root_.house_leq_pow_pow α n hn hα0 H)

lemma rho_norm_le_house_rho (α : K) :
    ‖((canonicalEmbedding K) α)‖ ≤ house (α) := by
  unfold house
  simp only [le_refl]

instance : DecidableEq (K →ₐ[ℚ] ℂ) := by {
  apply Classical.typeDecidableEq
  }

lemma house_prod_le (s : Finset K) :
    house (∏ x ∈ s, x) ≤ ∏ x ∈ s, house x := by
  classical
  refine Finset.induction_on (s := s) ?_ ?_
  · simp [house]
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    calc
      house (a * ∏ x ∈ s, x)
        ≤ house a * house (∏ x ∈ s, x) := house_mul_le a _
      _ ≤ house a * ∏ x ∈ s, house x := by
        apply mul_le_mul
        · simp only [le_refl]
        · exact ih
        · exact house_nonneg (∏ x ∈ s, x)
        · exact house_nonneg a

omit [NumberField K] in
lemma etc [Field L] [Field E] [Algebra K L] [Algebra K E]
 [Fintype (L →ₐ[K] E)] [DecidableEq (L →ₐ[K] E)] (x : L) (σ0 : L →ₐ[K] E) :
  (∏ σ : L →ₐ[K] E, σ x) =
  σ0 x * ∏ σ ∈ (Finset.univ.erase σ0), σ x := by
  have hmem : σ0 ∈ (Finset.univ : Finset (L →ₐ[K] E)) :=
    Finset.mem_univ _
  exact (Finset.mul_prod_erase (Finset.univ : Finset (L →ₐ[K] E))
    (fun σ => σ x) hmem).symm

lemma abs_norm_eq_prod_embeddings_norm (α : K) :
    ‖Algebra.norm ℚ (α)‖ = ‖∏ σ : K →ₐ[ℚ] ℂ, σ (α)‖ := by
    rw [← Algebra.norm_eq_prod_embeddings]
    simp only [eq_ratCast, norm_ratCast]
    congr

lemma alg_int_emb_norm (α : K) (σ : K →+* ℂ) : ‖σ α‖ ≤ house (α) := by {
  rw [house_eq_sup']
  rw [Finset.sup'_eq_sup]
  let s1 : Finset (K →+* ℂ) := by {exact Finset.univ}
  let f :  (K →+* ℂ) → NNReal := fun φ => ‖φ α‖₊
  have:= Finset.le_sup (f:=f ) (b := σ) (s:=s1) (Finset.mem_univ σ)
  simp only at this
  unfold f at this
  unfold s1 at this
  simp_all only [ge_iff_le]
  exact this
}

lemma test (α : K) (σ : K →+* ℂ) : σ.toRatAlgHom α = σ α := by
   {simp only [RingHom.toRatAlgHom_apply]}

lemma norm_le_house_norm (α : K) (σ : K →+* ℂ) :
  ‖Algebra.norm ℚ (α)‖ ≤ ‖σ α‖ * (house (α)) ^ (Module.finrank ℚ K -1) := by
  have hcard := NumberField.Embeddings.card K ℂ
  have := abs_norm_eq_prod_embeddings_norm α
  rw [etc (σ0 := σ.toRatAlgHom)] at this
  calc _ = ‖(σ α) * ∏ σ ∈ (Finset.univ.erase σ.toRatAlgHom), σ α‖ := ?_
       _ = ‖σ α‖ * ‖∏ σ ∈ (Finset.univ.erase σ.toRatAlgHom), σ α‖ := ?_
       _ ≤ ‖σ α‖ * ∏ σ ∈ (Finset.univ.erase σ.toRatAlgHom), ‖σ α‖ := ?_
       _ ≤ ‖σ α‖ * ∏ σ ∈ (Finset.univ.erase σ.toRatAlgHom), house (α) := ?_
       _ = ‖σ α‖ * (house (α)) ^ (Module.finrank ℚ K -1) := ?_
  · rw [this]
    simp only [RingHom.toRatAlgHom_apply, Complex.norm_mul, norm_prod]
  · rw [Complex.norm_mul]
  · apply mul_le_mul_of_nonneg_left
    exact Finset.norm_prod_le (Finset.univ.erase σ.toRatAlgHom) fun i ↦ i α
    exact norm_nonneg _
  · apply mul_le_mul_of_nonneg_left
    refine prod_le_prod ?_ ?_
    · intros i hi
      simp only [Finset.mem_erase] at hi
      exact norm_nonneg (i α)
    · intros i hi
      let i' : K →+* ℂ := i.toRingHom
      calc  _  =  ‖i' α‖ := ?_
            _  ≤ house (α) := ?_
      · unfold i'
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      · apply _root_.alg_int_emb_norm
    · exact norm_nonneg (σ α)
  · congr
    simp only [prod_const, Finset.mem_univ, card_erase_of_mem, card_univ, AlgHom.card]

def shift {w : ℕ} (s : Fin w) : ℕ := s + 1

lemma foo'' {w : ℕ} (s : Fin w) : 1 ≤ s.val + 1 := by {
  simp_all only [le_add_iff_nonneg_left, zero_le]}

lemma bar' {w : ℕ} (s : Fin w) : s + 1 ≤ w := s.isLt

lemma fin_n_plus_1_le_n_plus1 {w} (s : Fin w) : s + 1 ≤ w + 1 := by
  simp only [add_le_add_iff_right, Fin.is_le']

abbrev c' [Field K] [NumberField K] (α : K) : ℤ := (c'_both α : ℤ)

lemma c'_IsIntegral (α : K) :
  IsIntegral ℤ ((c' ) α • α) := (c'_both α).2.2

lemma c'_neq0 (α : K) : (c'_both α : ℤ) ≠ 0 := (c'_both α).2.1
