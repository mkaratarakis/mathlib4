/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Common

/-!
# List lemmas for Perron–Frobenius

Auxiliary lemmas on `List` used by quiver paths and matrix Perron–Frobenius theory.
-/

@[expose] public section

namespace List
open List
variable {α : Type*}

/--
A list `l` is disjoint from a singleton list `[x]` if and only if
`x` is not an element of `l`.
-/
@[simp]
lemma disjoint_singleton_right {l : List α} {x : α} :
  List.Disjoint l [x] ↔ x ∉ l :=
  List.disjoint_singleton

/--
An element `a` is a member of `l.concat x` if and only if it is a member of `l` or is equal to `x`.
-/
@[simp]
theorem mem_concat {a x : α} {l : List α} : a ∈ l.concat x ↔ a ∈ l ∨ a = x := by
  rw [concat_eq_append,List.mem_append, List.mem_singleton, or_comm]

lemma dropLast_append_singleton {l : List α} {a : α} (h : l.length > 0) :
  (l.concat a).dropLast = l := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    cases tl with
    | nil => simp [concat_eq_append, dropLast_cons_cons, dropLast_singleton]
    | cons _ _ => simp_all [concat_eq_append, dropLast_cons_cons]

/-- Any `x ∈ l` gives a decomposition `l = l₁ ++ x :: l₂`. -/
lemma exists_mem_split {l : List α} {x : α} (h : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  induction l with
  | nil     => cases h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h'
    · -- head
      exact ⟨[], ys, by simp only [List.nil_append]⟩
    · rcases ih h' with ⟨l₁, l₂, rfl⟩
      use y :: l₁, l₂
      simp only [List.cons_append]

variable {α : Type*} [DecidableEq α]

/-- A list contains a duplicate element if the count of some element is greater than 1. -/
def ContainsDup {α : Type*} [DecidableEq α] (l : List α) : Prop :=
  ∃ x, 2 ≤ l.count x

lemma nodup_iff_not_contains_dup {α : Type*} [DecidableEq α] {l : List α} :
    l.Nodup ↔ ¬l.ContainsDup := by
  rw [List.nodup_iff_count_le_one, List.ContainsDup, not_exists]
  constructor
  · intro h x
    specialize h x
    simp only [not_le]
    exact Nat.lt_of_le_of_lt h (Nat.lt_add_one 1)
  · intro h x
    specialize h x
    exact Nat.le_of_lt_succ (Nat.lt_of_not_le h)

variable {α : Type*} [DecidableEq α]


@[simp] lemma head_not_mem_tail_of_nodup [DecidableEq α] {l : List α}
    (h : l.Nodup) (hne : l ≠ []) : l.head hne ∉ l.tail := by
  cases l with
  | nil => cases hne rfl
  | cons _ _ => exact (nodup_cons.mp h).1

lemma idxOf_append_left {v : α} {l₁ l₂ : List α} (hv : v ∈ l₁) :
    idxOf v (l₁ ++ l₂) = idxOf v l₁ :=
  idxOf_append_of_mem hv

/-- If `l₁` is a prefix of `l₂` and `v ∈ l₁` then the two
    indices of `v` coincide. -/
lemma idxOf_eq_idxOf_of_isPrefix {v : α} {l₁ l₂ : List α}
    (hpref : IsPrefix l₁ l₂) (hv : v ∈ l₁) :
    idxOf v l₂ = idxOf v l₁ :=
  (IsPrefix.idxOf_eq_of_mem hpref hv).symm


omit [DecidableEq α] in
/--
If a list contains an element `x` at least twice, then `x` is contained
in the tail of this list.
-/
lemma mem_tail_of_count_ge_two [DecidableEq α] {x : α} {l : List α}
    (h : l.count x ≥ 2) : x ∈ l.tail := by
  cases l with
  | nil       => simp at h
  | cons hd tl =>
      by_cases hhd : hd = x
      · have h_tl : tl.count x ≥ 1 := by
          have : tl.count x + 1 ≥ 2 := by
            simpa [hhd] using h
          omega
        have h_pos : 0 < tl.count x := by omega
        have : x ∈ tl := (List.count_pos_iff).1 h_pos
        simpa using this
      · have h_tl : tl.count x ≥ 2 := by simpa [hhd] using h
        have h_pos : 0 < tl.count x := by omega
        have : x ∈ tl := (List.count_pos_iff).1 h_pos
        simpa using this

omit [DecidableEq α] in
lemma get_eq_get_dropLast {l : List α} {i : Nat} (hi : i < l.length - 1) :
    l.get ⟨i, Nat.lt_of_lt_pred hi⟩ = l.dropLast.get ⟨i, by rw [List.length_dropLast]; omega⟩ := by
  simp [List.get_eq_getElem, List.dropLast_eq_take, List.getElem_take]

/-- If an element is both the head and in the tail of a list, it appears at least twice -/
lemma count_ge_two_of_mem_head_and_tail {l : List α} {x : α}
    (h_head : l.head? = some x) (h_tail : x ∈ l.tail) : l.count x ≥ 2 := by
  cases l with
  | nil =>
    simp only [head?, reduceCtorEq] at h_head
  | cons y ys =>
    have hyx : y = x := by injection h_head
    subst hyx
    have h_count_tail : ys.count y > 0 :=  by exact count_pos_iff.mpr h_tail
    simp only [count_cons_self, ge_iff_le, Nat.reduceLeDiff, one_le_count_iff]
    simp_all only [head?_cons, tail_cons, gt_iff_lt, count_pos_iff]

omit [DecidableEq α] in
/-- A list with its head not in its tail has no duplicates if its tail has no duplicates -/
lemma nodup_of_head_not_mem_tail   {l : List α} {x : α} (h_nonempty : l ≠ []) (h_head : l.head h_nonempty = x)
    (h_not_in_tail : x ∉ l.tail) (h_nodup_tail : l.tail.Nodup) : l.Nodup := by
  cases l with
  | nil => contradiction
  | cons y ys =>
    simp only [head_cons] at h_head
    subst h_head
    simp only [tail_cons] at h_not_in_tail
    simp only [nodup_cons]
    constructor
    · exact h_not_in_tail
    · simpa using h_nodup_tail

/-- The index of an element in a prefix equals the index in the whole list -/
lemma idxOf_eq_of_isPrefix {l₁ l₂ : List α} (h_prefix : l₁.IsPrefix l₂) {x : α} (h_mem : x ∈ l₁) :
    l₁.idxOf x = l₂.idxOf x :=
  IsPrefix.idxOf_eq_of_mem h_prefix h_mem


/-- For an element x in a list l, if x appears exactly once and is not in the tail,
    then its count is less than 2 -/
lemma count_lt_of_mem_of_not_mem_tail {l : List α} {x : α}
    (h_mem : x ∈ l) (h_not_in_tail : x ∉ l.tail) : l.count x < 2 := by
  cases l with
  | nil =>
    simp only [not_mem_nil] at h_mem
  | cons y ys =>
    have hxy : x = y := by
      simp only [tail_cons, mem_cons] at h_mem h_not_in_tail
      grind
    subst hxy
    simp only [List.count_cons_self]
    have h0 : ys.count x = 0 := by
      by_contra h1
      have hpos : ys.count x > 0 := Nat.pos_of_ne_zero h1
      have hmem' := (List.count_pos_iff).mp hpos
      exact h_not_in_tail hmem'
    simp [count_cons, h0]

omit [DecidableEq α] in
/-- Count an element in a head-tail splitting of a list.
If the first (i.e. leftmost) occurrence of `x` is at index `l.length - 1`
(so at the last position) then `x` occurs exactly once. -/
lemma count_eq_one_of_idxOf_eq_length_sub_one [DecidableEq α] {l : List α} {x : α}
    (hlt : l.idxOf x < l.length) :
    l.idxOf x = l.length - 1 → l.count x = 1 := by
  intro hidx
  induction l using List.reverseRecOn with
  | nil => cases (Nat.lt_irrefl _ hlt)
  | append_singleton xs y ih =>
    have hlen : (xs ++ [y]).length = xs.length + 1 := by simp
    have hidx' : idxOf x (xs ++ [y]) = xs.length := by
      simpa [hlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hidx
    by_cases hx : x = y
    · subst hx
      have h_not_mem : x ∉ xs := by
        intro hmem
        have : idxOf x (xs ++ [x]) = idxOf x xs := by
          simp [idxOf_append_of_mem hmem]
        have hlt' : idxOf x xs < xs.length := idxOf_lt_length_of_mem hmem
        simp_rw [← hidx'] at hlt'
        omega
      have hcount0 : xs.count x = 0 := count_eq_zero_of_not_mem h_not_mem
      simp [count_append, hcount0]
    · have hx_mem : x ∈ xs ++ [y] := idxOf_lt_length_iff.mp hlt
      have : x ∈ xs ∨ x = y := by
        simpa [mem_append, mem_singleton] using hx_mem
      cases this with
      | inl hmem =>
          have : idxOf x (xs ++ [y]) = idxOf x xs := by
            simp [idxOf_append_of_mem hmem]
          have hlt' : idxOf x xs < xs.length := idxOf_lt_length_of_mem hmem
          simp; omega
      | inr hxy => exact (hx hxy).elim

@[simp] lemma idxOf_eq_length_sub_one_of_getLast {l : List α} {x : α}
    (h_nonempty : l ≠ []) (h_last : l.getLast h_nonempty = x) (h_unique : x ∉ l.dropLast) :
    l.idxOf x = l.length - 1 := by
  conv_lhs => rw [← h_last]
  exact idxOf_getLast h_nonempty (by simpa [← h_last] using h_unique)

/-- If `x` is in the tail of a list, then `x` is not the head of the list.
This is only true in general for lists without duplicates. -/
lemma ne_of_mem_tail {l : List α} {x : α} (h_nodup : l.Nodup) (h_mem : x ∈ l.tail) (h_ne_nil : l ≠ []) :
    x ≠ l.head h_ne_nil := by
  intro h_eq
  have h_head_in_tail : l.head h_ne_nil ∈ l.tail := by
    rwa [← h_eq]
  have h_head_not_in_tail := head_not_mem_tail_of_nodup h_nodup h_ne_nil
  contradiction

lemma bif_of_false {α : Type*} {p : Bool} {a b : α} (h : p = false) : (bif p then a else b) = b := by
  rw [h]
  rfl

lemma bif_of_true {α : Type*} {p : Bool} {a b : α} (h : p = true) : (bif p then a else b) = a := by
  rw [h]
  rfl

/-- Helper lemma for findIdx.go with accumulator incrementing by 1 -/
lemma findIdx_go_succ' {α : Type*} (p : α → Bool) (l : List α) (n : Nat) :
  findIdx.go p l (n+1) = findIdx.go p l n + 1 := by
  induction l generalizing n with
  | nil => rfl
  | cons hd tl ih =>
    simp only [findIdx.go]
    by_cases h_p : p hd = true
    · rw [bif_of_true h_p, bif_of_true h_p]
    · have h_p_false : p hd = false := by rw [Bool.not_eq_true] at h_p; exact h_p
      rw [bif_of_false h_p_false, bif_of_false h_p_false]
      exact ih (n+1)

/-- Helper lemma: the findIdx.go function with accumulator 1 returns the result of findIdx plus 1 -/
lemma findIdx_go_succ {α : Type*} (p : α → Bool) (l : List α) :
  findIdx.go p l 1 = findIdx p l + 1 := by
  unfold findIdx
  exact findIdx_go_succ' p l 0

omit [DecidableEq α] in
/-- Helper lemma: Boolean equality is false iff the terms are not equal -/
lemma beq_eq_false_iff_ne [DecidableEq α] {a b : α} : (a == b) = false ↔ a ≠ b := by
  rw [_root_.beq_eq_false_iff_ne]

omit [DecidableEq α] in
/-- Helper lemma for index computation with head != x -/
lemma idxOf_cons_of_ne [DecidableEq α] {hd : α} {tl : List α} {x : α} (h_neq : hd ≠ x) :
  idxOf x (hd :: tl) = idxOf x tl + 1 := by
  dsimp only [idxOf, findIdx]
  simp only [findIdx.go]
  have h_eq_false : (hd == x) = false := by
    rw [beq_eq_false_iff_ne]
    exact h_neq
  rw [bif_of_false h_eq_false]
  exact findIdx_go_succ (fun y => y == x) tl

-- This helper lemma addresses many of the beq_iff_eq rewrite failures
lemma not_beq_eq_true_iff_ne {a b : α} : ¬(a == b) = true ↔ a ≠ b := by
  rw [Bool.not_eq_true]
  rw [beq_eq_false_iff_ne]

lemma mem_of_idxOf_lt_length {l : List α} {x : α} (h : idxOf x l < l.length) : x ∈ l :=
  idxOf_lt_length_iff.mp h

/-- If `x` is in `l`, then getting the element at index `idxOf x l` gives `x`. -/
lemma get_idxOf_of_mem {l : List α} {x : α} (h : x ∈ l) :
  l.get ⟨idxOf x l, idxOf_lt_length_of_mem h⟩ = x := by
  induction l with
  | nil => simp only [not_mem_nil] at h
  | cons hd tl ih =>
    by_cases h_eq : hd = x
    · subst h_eq
      have h_idx : idxOf hd (hd :: tl) = 0 := by
        dsimp [idxOf, findIdx]
        simp only [findIdx.go]
        simp only [BEq.rfl, le_refl, Nat.zero_add, cond_true, Nat.eq_zero_of_le_zero]
      simp only [h_idx, get_eq_getElem, getElem_cons_zero]
    · simp only [mem_cons] at h
      cases h with
      | inl h_hd =>
        subst h_hd
        contradiction
      | inr h_tl =>
        have ih' := ih h_tl
        have h_idxOf : idxOf x (hd :: tl) = idxOf x tl + 1 := idxOf_cons_of_ne h_eq
        have hl : idxOf x tl < tl.length := idxOf_lt_length_of_mem h_tl
        have hl' : idxOf x tl + 1 < (hd :: tl).length := by
          rw [length_cons]
          exact Nat.add_lt_add_right hl 1
        have helper : (hd :: tl).get ⟨idxOf x (hd :: tl), idxOf_lt_length_of_mem (mem_cons.mpr (Or.inr h_tl))⟩ =
                      (hd :: tl).get ⟨idxOf x tl + 1, hl'⟩ := by
          congr
        have h_getElem : (hd :: tl).get ⟨idxOf x tl + 1, hl'⟩ = tl.get ⟨idxOf x tl, hl⟩ := by
          simp only [get_eq_getElem]
          apply getElem_cons_succ
        exact Eq.trans helper (Eq.trans h_getElem ih')

omit [DecidableEq α] in
/-- A duplicate in `dropLast` occurs at a positive index. -/
lemma exists_pos_get_of_dropLast_count_ge_two [DecidableEq α] {l : List α} {x : α}
    (h : 2 ≤ l.dropLast.count x) :
    ∃ (i : Nat) (hi : i < l.length), 0 < i ∧ i < l.length - 1 ∧ l.get ⟨i, hi⟩ = x := by
  have hx_tail := mem_tail_of_count_ge_two h
  have hlen : 2 ≤ l.length := by
    have := Nat.le_trans h List.count_le_length
    rw [List.length_dropLast] at this
    omega
  match l with
  | [] | [_] => simp [List.length_dropLast] at hlen
  | y :: z :: tl =>
    have hx_mem : x ∈ (z :: tl).dropLast := by
      simpa [List.dropLast_cons_cons, List.tail_cons] using hx_tail
    let i := (z :: tl).dropLast.idxOf x + 1
    have hidx : (z :: tl).dropLast.idxOf x < (z :: tl).dropLast.length :=
      List.idxOf_lt_length_of_mem hx_mem
    have hdl : (z :: tl).dropLast.length = tl.length := by
      simp only [List.length_cons, List.length_dropLast]
      omega
    have hi_pred : i < (y :: z :: tl).length - 1 := by
      dsimp [i, List.length_cons]
      rw [hdl] at hidx
      exact Nat.succ_lt_succ hidx
    have hi_lt_len : i < (y :: z :: tl).length := Nat.lt_of_lt_pred hi_pred
    have hi_z : (z :: tl).dropLast.idxOf x < (z :: tl).length - 1 := by
      have h1 : (z :: tl).length - 1 = (z :: tl).dropLast.length := by
        rw [List.length_dropLast, List.length_cons]
      rw [h1]
      exact hidx
    have hi_get : (y :: z :: tl).get ⟨i, hi_lt_len⟩ = x := by
      dsimp only [i]
      rw [List.get_cons_succ, get_eq_get_dropLast hi_z, get_idxOf_of_mem hx_mem]
    exact ⟨i, hi_lt_len, Nat.succ_pos _, hi_pred, hi_get⟩

omit [DecidableEq α] in
/-- If `l.get i = x`, then `idxOf x l ≤ i.val`. -/
lemma idxOf_le_of_get_eq [DecidableEq α] {l : List α} {x : α} {i : Fin l.length} (h : l.get i = x) :
  idxOf x l ≤ i.val := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons hd tl ih =>
    cases i using Fin.cases with
    | zero =>
      dsimp only [idxOf, findIdx, length_cons, Fin.val_zero]
      simp only [findIdx.go]
      have : hd = x := by
        simp only [get_eq_getElem] at h
        exact h
      rw [beq_iff_eq.mpr this]
      simp only [cond_true]
      exact Nat.zero_le 0
    | succ j =>
      dsimp only [idxOf, findIdx, length_cons, Fin.val_succ]
      simp only [findIdx.go]
      by_cases h_hd_eq : hd == x
      · simp only [h_hd_eq, cond_true]
        exact Nat.zero_le j.val.succ
      · simp only [h_hd_eq, cond_false]
        have h_tl : tl.get j = x := by
          simp only [get_eq_getElem] at h
          exact h
        have ih' := ih h_tl
        have h_idx : findIdx.go (fun y => y == x) tl 1 = idxOf x tl + 1 := by
          unfold idxOf at ih'
          exact findIdx_go_succ (fun y => y == x) tl
        calc
          findIdx.go (fun y => y == x) tl 1 = idxOf x tl + 1 := h_idx
          _ ≤ j.val + 1 := Nat.add_le_add_right ih' 1

/-- If v is in a list but not equal to a, then a is not in the singleton list containing v. -/
lemma not_mem_implies_ne {α} [DecidableEq α] {v a : α} {l : List α} :
  v ∈ l → v ≠ a → a ∉ [v] :=
  fun _ hne ha => hne.symm (mem_singleton.1 ha)

/-- If v is in the list but not the head, then its index is positive. -/
lemma idxOf_pos_of_ne_head {α} [DecidableEq α] {v : α} {l : List α}
    (hv : v ∈ l) (hne : ∀ (h : l ≠ []), v ≠ l.head h) :
    idxOf v l > 0 := by
  cases l with
  | nil => cases hv
  | cons hd tl =>
    by_cases h_eq : v = hd
    · subst h_eq
      exact absurd rfl (hne (cons_ne_nil _ _))
    · have h : hd ≠ v := by intro h; exact h_eq h.symm
      simp only [gt_iff_lt]
      rw [idxOf_cons_of_ne h]
      exact Nat.succ_pos _

/-- If an element `x` is in the tail of a list `l` without duplicates, its first index in `l` must be positive. -/
lemma idxOf_pos_of_mem_tail  {l : List α} (h_nodup : l.Nodup) {x : α} (h : x ∈ l.tail) : 0 < l.idxOf x := by
  cases l with
  | nil => simp only [tail_nil, not_mem_nil] at h
  | cons hd tl =>
    have h_mem_tl : x ∈ tl := by rwa [tail_cons] at h
    have h_ne : hd ≠ x := by
      intro h_eq
      subst h_eq
      simp_all only [nodup_cons, not_true_eq_false, false_and]
    rw [idxOf_cons_of_ne h_ne]
    exact Nat.succ_pos _

/-- Membership in the tail of `l.concat y`.
It is only useful if `l` is **non-empty** – we require `hl : l ≠ []`. -/
@[simp] lemma mem_tail_concat_of_ne_nil
    {α : Type*} [DecidableEq α] {l : List α} (hl : l ≠ []) (x y : α) :
    x ∈ (l.concat y).tail ↔ x ∈ l.tail ∨ x = y := by
  cases l with
  | nil      => exact (hl rfl).elim
  | cons _ t => simp only [concat_eq_append, cons_append, tail_cons, mem_append, mem_cons,
    not_mem_nil, or_false]

/-- Membership in the tail of a concatenation splits into the two obvious
    alternatives. -/
lemma mem_tail_append {α : Type*} {x : α} {L₁ L₂ : List α} :
    x ∈ (L₁ ++ L₂).tail ↔ (L₁ = nil ∧ x ∈ L₂.tail) ∨ (L₁ ≠ nil ∧ x ∈ L₁.tail ++ L₂) := by
  cases L₁ with
  | nil =>
      simp only [tail, nil_append, true_and, ne_eq, not_true_eq_false, false_and, or_false]
  | cons h t =>
      simp only [tail, cons_append, mem_append, reduceCtorEq, false_and, ne_eq, not_false_eq_true,
        true_and, false_or]

/-- For a non-empty list `L`, membership in the tail of `L.concat a`
    means “either in the tail of `L` or equal to the new element `a`”. -/
lemma mem_tail_concat_of_ne_nil' {α : Type*} {L : List α} (hL : L ≠ []) {x a : α} :
    x ∈ (L.concat a).tail ↔ x ∈ L.tail ∨ x = a := by
  -- `L.concat a = L ++ [a]`
  simpa [List.concat, mem_tail_append, List.tail, hL] using
        (by
          cases L with
          | nil            => cases hL rfl
          | cons h t =>
              simp only [cons_append, mem_append, mem_cons, not_mem_nil, or_false])

@[simp]
lemma mem_of_mem_tail_dropLast {α} {x : α} {l : List α} :
    x ∈ (l.dropLast).tail → x ∈ l.tail := by
  cases l with
  | nil       => intro h; cases h
  | cons hd tl =>
      cases tl with
      | nil        => intro h; cases h
      | cons hd' tl' =>
          intro h
          have h' : x ∈ (hd' :: tl').dropLast := by
            simpa using h
          have : x ∈ (hd' :: tl') := List.mem_of_mem_dropLast h'
          simpa using this

/-- The last element of a list of length at least 2 is in its tail. -/
@[simp]
lemma getLast_mem_tail {α : Type*} {l : List α} (h : l.length ≥ 2) :
    l.getLast (ne_nil_of_length_pos (by omega)) ∈ l.tail := by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    have h_tl : tl ≠ [] := by rintro rfl; simp [length_cons] at h
    cases tl with
    | nil => simp at h_tl
    | cons _ _ => simp [tail_cons, getLast_cons, getLast_mem]

omit [DecidableEq α] in
@[simp]
lemma not_mem_dropLast_getLast {l : List α}
    (h₁ : l ≠ []) (h₂ : l.Nodup) :
    l.getLast h₁ ∉ l.dropLast := by
  induction l using List.reverseRecOn with
  | nil =>
      cases h₁ rfl
  | append_singleton xs x ih =>
      simp only [getLast_append_singleton] at *
      have h_disj : List.Disjoint xs [x] := disjoint_of_nodup_append h₂
      have hx_not_mem : x ∉ xs := (disjoint_singleton_right).1 h_disj
      simpa using hx_not_mem

lemma nodup_take_of_nodup {α : Type*} {l : List α} (h : l.Nodup) (n : ℕ) :
    (l.take n).Nodup :=
  h.sublist (List.take_sublist _ _)

omit [DecidableEq α] in
/--
For a list `l` with no duplicates, the element at index `i` is not a member of the prefix of `l` of length `i`.
-/
lemma get_not_mem_take {l : List α} (h_nodup : l.Nodup)
    (i : ℕ) (h_bounds : i < l.length) :
    l.get ⟨i, h_bounds⟩ ∉ l.take i := by
  revert i h_bounds
  induction l with
  | nil =>
      intro i h_bounds
      simpa using (Nat.not_lt_zero _ h_bounds).elim
  | cons hd tl ih =>
      intro i h_bounds
      simp only [nodup_cons] at h_nodup
      cases i with
      | zero =>
          simp only [le_refl, take_zero, length_cons, Fin.zero_eta, get_eq_getElem, Fin.val_zero,
            Nat.eq_zero_of_le_zero, getElem_cons_zero, not_mem_nil, not_false_eq_true]
      | succ i' =>
          have h_bounds' : i' < tl.length := by
            simpa [List.length_cons] using Nat.lt_of_succ_lt_succ h_bounds
          have h_ind := ih h_nodup.2 i' h_bounds'
          simp only [get_cons_succ]
          rw [take_succ_cons, mem_cons, not_or]
          constructor
          · intro h_eq
            have h_mem : hd ∈ tl := by
              rw [← h_eq]
              exact get_mem tl ⟨i', Nat.lt_of_succ_lt_succ h_bounds⟩
            exact h_nodup.1 h_mem
          · exact h_ind

omit [DecidableEq α] in
@[simp] lemma getLast_not_mem_dropLast
   {l : List α} (h_ne : l ≠ []) (h_nodup : l.Nodup) :
    l.getLast h_ne ∉ l.dropLast := by
  simpa using List.not_mem_dropLast_getLast (l := l) h_ne h_nodup

omit [DecidableEq α] in
/-- An element `x` is not a member of the prefix of `l` up to the first
occurrence of `x`. -/
lemma not_mem_take_idxOf [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
    x ∉ l.take (l.idxOf x) := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    by_cases hx : x = hd
    · subst hx
      simp [idxOf_cons_self]
    · have h_in_tl : x ∈ tl := by
        simpa [hx] using h
      have h_idx : idxOf x (hd :: tl) = idxOf x tl + 1 :=
        idxOf_cons_of_ne fun a ↦ hx (id (Eq.symm a))
      rw [h_idx, take_succ_cons, mem_cons, not_or]
      exact ⟨hx, ih h_in_tl⟩

omit [DecidableEq α] in
/-- Two prefixes of the same list with the same length are equal. -/
lemma IsPrefix.eq_of_length_eq {l₁ l₂ l : List α}
    (h₁ : l₁.IsPrefix l) (h₂ : l₂.IsPrefix l) (h_len : l₁.length = l₂.length) :
    l₁ = l₂ := by
  obtain ⟨t₁, rfl⟩ := h₁
  obtain ⟨t₂, h_eq⟩ := h₂
  have h_append_eq : l₁ ++ t₁ = l₂ ++ t₂ := by rw [h_eq]
  have h_take_eq := congr_arg (fun l ↦ l.take l₁.length) h_append_eq
  simpa [take_left', h_len] using h_take_eq

end List
