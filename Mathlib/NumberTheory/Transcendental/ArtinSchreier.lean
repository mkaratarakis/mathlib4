/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Order.Zorn
import Mathlib.Algebra.Order.Ring.Cone

/-!
# The easy direction of the Artin–Schreier theorem

Let `F` be a formally real field (`IsSemireal F`). We show that an element which is **not** a sum of
squares is strictly negative in some ordering of `F`:

* `RingPreordering.exists_isOrdering_neg_mem` :
  if `¬ IsSumSq a` then there is an ordering `O` of `F` with `-a ∈ O` (so `a ≤ 0` in `O`).

This is exactly the input needed for Lemma 4 of Hillar–Nie (Hilbert's 17th problem for matrices,
see `Mathlib/NumberTheory/Transcendental/Hilbert17Matrices.lean`): if a coefficient of the minimal
polynomial were not a sum of squares, it would be negative in some ordering, contradicting its
nonnegativity in the real closure.

## Main constructions

* `RingPreordering.sumSq F` : the preordering of sums of squares of a formally real field.
* `RingPreordering.adjoin P a ha` : the preordering `P + a·P`, defined when `-a ∉ P`; it contains
  `a` and extends `P`.
* `RingPreordering.exists_isOrdering_ge` : every preordering of a field is contained in an ordering
  (Zorn's lemma; a maximal preordering is an ordering).
-/

namespace RingPreordering

variable {F : Type*} [Field F]

/-! ### The sum-of-squares preordering -/

variable (F) in
/-- The preordering of sums of squares of a formally real field. -/
def sumSq [IsSemireal F] : RingPreordering F :=
  mk' {x : F | IsSumSq x}
    (fun hx hy => hx.add hy)
    (fun hx hy => hx.mul hy)
    (fun x => IsSumSq.mul_self x)
    (IsSemireal.not_isSumSq_neg_one F)

@[simp] theorem mem_sumSq [IsSemireal F] {x : F} : x ∈ sumSq F ↔ IsSumSq x := Iff.rfl

/-! ### Adjoining an element to a preordering -/

variable (P : RingPreordering F)

/-- For a preordering `P` of a field and `a` with `-a ∉ P`, the set `P + a·P` is again a
preordering. It contains `a` and extends `P`. -/
def adjoin (a : F) (ha : -a ∉ P) : RingPreordering F :=
  mk' {z : F | ∃ p ∈ P, ∃ q ∈ P, z = p + a * q}
    (by
      rintro x y ⟨p₁, hp₁, q₁, hq₁, rfl⟩ ⟨p₂, hp₂, q₂, hq₂, rfl⟩
      exact ⟨p₁ + p₂, add_mem hp₁ hp₂, q₁ + q₂, add_mem hq₁ hq₂, by ring⟩)
    (by
      rintro x y ⟨p₁, hp₁, q₁, hq₁, rfl⟩ ⟨p₂, hp₂, q₂, hq₂, rfl⟩
      refine ⟨p₁ * p₂ + a * a * (q₁ * q₂), ?_, p₁ * q₂ + p₂ * q₁, ?_, by ring⟩
      · exact add_mem (mul_mem hp₁ hp₂)
          (mul_mem (P.mem_of_isSquare ⟨a, rfl⟩) (mul_mem hq₁ hq₂))
      · exact add_mem (mul_mem hp₁ hq₂) (mul_mem hp₂ hq₁))
    (fun x => ⟨x * x, P.mem_of_isSquare ⟨x, rfl⟩, 0, zero_mem P, by ring⟩)
    (by
      rintro ⟨p, hp, q, hq, hpq⟩
      by_cases hq0 : q = 0
      · refine P.neg_one_notMem ?_
        rw [hq0, mul_zero, add_zero] at hpq
        exact hpq ▸ hp
      · refine ha ?_
        have hP1 : -a * (q * q) = (1 + p) * q := by linear_combination q * hpq
        have key : -a * (q * q) * (q⁻¹ * q⁻¹) = -a := by field_simp
        rw [← key, hP1]
        exact mul_mem (mul_mem (add_mem (one_mem P) hp) hq) (P.mem_of_isSquare ⟨q⁻¹, rfl⟩))

theorem mem_adjoin {a z : F} (ha : -a ∉ P) :
    z ∈ P.adjoin a ha ↔ ∃ p ∈ P, ∃ q ∈ P, z = p + a * q := Iff.rfl

theorem self_mem_adjoin {a : F} (ha : -a ∉ P) : a ∈ P.adjoin a ha :=
  ⟨0, zero_mem P, 1, one_mem P, by ring⟩

theorem le_adjoin {a : F} (ha : -a ∉ P) : P ≤ P.adjoin a ha :=
  fun x hx => ⟨x, hx, 0, zero_mem P, by ring⟩

/-! ### Every preordering of a field extends to an ordering -/

/-- Every preordering of a field is contained in an ordering. -/
theorem exists_isOrdering_ge (P : RingPreordering F) :
    ∃ O : RingPreordering F, O.IsOrdering ∧ P ≤ O := by
  -- Chains of preorderings above `P` are bounded by their union.
  have ih : ∀ c ⊆ Set.Ici P, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub, ∀ z ∈ c, z ≤ ub := by
    intro c _ hc y hy
    refine ⟨mk' (⋃ Q ∈ c, (Q : Set F)) ?_ ?_ ?_ ?_, ?_⟩
    · rintro x z hx hz
      obtain ⟨Q₁, hQ₁, hx⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨Q₂, hQ₂, hz⟩ := Set.mem_iUnion₂.1 hz
      rcases hc.total hQ₁ hQ₂ with h | h
      · exact Set.mem_iUnion₂.2 ⟨Q₂, hQ₂, add_mem (SetLike.le_def.1 h hx) hz⟩
      · exact Set.mem_iUnion₂.2 ⟨Q₁, hQ₁, add_mem hx (SetLike.le_def.1 h hz)⟩
    · rintro x z hx hz
      obtain ⟨Q₁, hQ₁, hx⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨Q₂, hQ₂, hz⟩ := Set.mem_iUnion₂.1 hz
      rcases hc.total hQ₁ hQ₂ with h | h
      · exact Set.mem_iUnion₂.2 ⟨Q₂, hQ₂, mul_mem (SetLike.le_def.1 h hx) hz⟩
      · exact Set.mem_iUnion₂.2 ⟨Q₁, hQ₁, mul_mem hx (SetLike.le_def.1 h hz)⟩
    · exact fun x => Set.mem_iUnion₂.2 ⟨y, hy, y.mem_of_isSquare ⟨x, rfl⟩⟩
    · rintro hmem
      obtain ⟨Q, _, h⟩ := Set.mem_iUnion₂.1 hmem
      exact Q.neg_one_notMem h
    · exact fun z hz => SetLike.le_def.2 fun x hx => Set.mem_iUnion₂.2 ⟨z, hz, hx⟩
  obtain ⟨M, hPM, hMmax⟩ := zorn_le_nonempty_Ici₀ P ih P le_rfl
  -- A maximal preordering has the mem-or-neg-mem property, using the adjoin construction.
  have hmem : HasMemOrNegMem M := ⟨fun t => by
    by_cases h : -t ∈ M
    · exact Or.inr h
    · refine Or.inl ?_
      have hge : M.adjoin t h ≤ M := hMmax (le_adjoin M h)
      exact SetLike.le_def.1 hge (self_mem_adjoin M h)⟩
  haveI := hmem
  -- Over a field, mem-or-neg-mem implies the ordering axioms (the support is `⊥`, hence prime).
  have hord : M.IsOrdering := by
    rw [isOrdering_iff]
    intro x z hxz
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hx, hz⟩ := hcon
    have hmx : -x ∈ M := (mem_or_neg_mem M x).resolve_left hx
    have hmz : -z ∈ M := (mem_or_neg_mem M z).resolve_left hz
    have hxz' : x * z ∈ M := by simpa using mul_mem hmx hmz
    have h0 : x * z = 0 := RingPreordering.eq_zero_of_mem_of_neg_mem hxz' hxz
    rcases mul_eq_zero.1 h0 with h | h
    · exact hx (h ▸ zero_mem M)
    · exact hz (h ▸ zero_mem M)
  exact ⟨M, hord, hPM⟩

/-! ### The easy Artin–Schreier theorem -/

/-- **Easy Artin–Schreier.** In a formally real field, an element that is not a sum of squares is
negative in some ordering: there is an ordering `O` with `-a ∈ O`. -/
theorem exists_isOrdering_neg_mem [IsSemireal F] {a : F} (ha : ¬ IsSumSq a) :
    ∃ O : RingPreordering F, O.IsOrdering ∧ -a ∈ O := by
  have hna : -(-a) ∉ sumSq F := by simpa using ha
  obtain ⟨O, hO, hle⟩ := exists_isOrdering_ge ((sumSq F).adjoin (-a) hna)
  exact ⟨O, hO, SetLike.le_def.1 hle (self_mem_adjoin (sumSq F) hna)⟩

/-- **Easy Artin–Schreier, contrapositive form.** In a formally real field, an element lying in
*every* ordering is a sum of squares. -/
theorem isSumSq_of_forall_mem [IsSemireal F] {a : F}
    (h : ∀ O : RingPreordering F, O.IsOrdering → a ∈ O) : IsSumSq a := by
  by_contra ha
  obtain ⟨O, hO, hmem⟩ := exists_isOrdering_neg_mem ha
  have ha0 : a = 0 := RingPreordering.eq_zero_of_mem_of_neg_mem (h O hO) hmem
  exact ha (ha0 ▸ IsSumSq.zero)

section Order

variable (O : RingPreordering F) [O.IsOrdering]

/-- An ordering of a field is a (positive) ring cone: a subsemiring whose support is trivial. -/
def toRingCone : RingCone F where
  __ := O.toSubsemiring
  eq_zero_of_mem_of_neg_mem' {a} ha hna := by
    have h : a ∈ O.supportAddSubgroup := mem_supportAddSubgroup.mpr ⟨ha, hna⟩
    rw [supportAddSubgroup_eq_bot] at h
    simpa using h

instance : HasMemOrNegMem (toRingCone O) := ⟨fun a => mem_or_neg_mem O a⟩

open scoped Classical in
/-- The linear order on a field induced by an ordering `O`: `x ≤ y` iff `y - x ∈ O`. -/
noncomputable def toLinearOrder : LinearOrder F :=
  LinearOrder.mkOfAddGroupCone (toRingCone O)

open scoped Classical in
/-- The order induced by an ordering of a field makes it a strict ordered ring. -/
noncomputable def toIsStrictOrderedRing :
    letI := toLinearOrder O; IsStrictOrderedRing F := by
  letI := toLinearOrder O
  haveI : IsOrderedRing F := IsOrderedRing.mkOfCone (toRingCone O)
  infer_instance

open scoped Classical in
/-- The induced order has `O` as its set of nonnegative elements. -/
theorem toLinearOrder_nonneg_iff {x : F} :
    letI := toLinearOrder O; 0 ≤ x ↔ x ∈ O := by
  letI := toLinearOrder O
  change x - 0 ∈ toRingCone O ↔ x ∈ O
  rw [sub_zero]; exact Iff.rfl

end Order

end RingPreordering
