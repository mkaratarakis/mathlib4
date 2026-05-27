/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Common
public import Batteries.Data.List.Lemmas

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively.
-/

public section

assert_not_exists Monoid Set.range

open Nat

variable {α β : Type*}

namespace List

@[simp]
theorem countP_lt_length_iff {l : List α} {p : α → Bool} :
    l.countP p < l.length ↔ ∃ a ∈ l, p a = false := by
  simp [Nat.lt_iff_le_and_ne, countP_le_length]

variable [BEq α] [LawfulBEq α] {l l₁ l₂ : List α}

section beq

@[simp]
theorem count_lt_length_iff {a : α} : l.count a < l.length ↔ ∃ b ∈ l, b ≠ a := by simp [count]

lemma countP_erase (p : α → Bool) (l : List α) (a : α) :
    countP p (l.erase a) = countP p l - if a ∈ l ∧ p a then 1 else 0 := by
  grind [countP_eq_length_filter]

lemma count_diff (a : α) (l₁ : List α) :
    ∀ l₂, count a (l₁.diff l₂) = count a l₁ - count a l₂
  | [] => rfl
  | b :: l₂ => by
    simp only [diff_cons, count_diff, count_erase, beq_iff_eq, Nat.sub_right_comm, count_cons,
      Nat.sub_add_eq]

lemma countP_diff (hl : l₂ <+~ l₁) (p : α → Bool) :
    countP p (l₁.diff l₂) = countP p l₁ - countP p l₂ := by
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [← countP_append]
  exact ((subperm_append_diff_self_of_count_le <| subperm_ext_iff.1 hl).symm.trans
    perm_append_comm).countP_eq _

@[simp]
theorem count_map_of_injective [BEq β] [LawfulBEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map]
  unfold Function.comp
  simp only [hf.beq_eq]

end beq

section decidableCount

variable {α : Type*} [DecidableEq α]

theorem mem_tail_of_count_ge_two {x : α} {l : List α} (h : 2 ≤ l.count x) : x ∈ l.tail := by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    have hpos : 0 < tl.count x := by
      by_contra h0
      have h0' : tl.count x = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp h0)
      by_cases hhd : hd = x
      · simp [hhd, count_cons, h0'] at h
      · simp [hhd, count_cons, h0'] at h
    exact (count_pos_iff).1 hpos

theorem exists_pos_get_of_dropLast_count_ge_two {l : List α} {x : α}
    (h : 2 ≤ l.dropLast.count x) :
    ∃ (i : Nat) (hi : i < l.length), 0 < i ∧ i < l.length - 1 ∧ l.get ⟨i, hi⟩ = x := by
  have hx_tail := mem_tail_of_count_ge_two h
  have hlen : 2 ≤ l.length := by
    have := Nat.le_trans h count_le_length
    rw [length_dropLast] at this
    omega
  match l with
  | [] | [_] => simp at hlen
  | y :: z :: tl =>
    have hx_mem : x ∈ (z :: tl).dropLast := by
      simpa [dropLast_cons_cons, tail_cons] using hx_tail
    let i := (z :: tl).dropLast.idxOf x + 1
    have hidx := idxOf_lt_length_of_mem hx_mem
    have hdl : (z :: tl).dropLast.length = tl.length := by
      simp only [length_cons, length_dropLast]
      omega
    have hi_pred : i < (y :: z :: tl).length - 1 := by
      dsimp [i, length_cons]
      rw [hdl] at hidx
      exact Nat.succ_lt_succ hidx
    have hi_lt_len : i < (y :: z :: tl).length := Nat.lt_of_lt_pred hi_pred
    have hi_z : (z :: tl).dropLast.idxOf x < (z :: tl).length - 1 := by
      have h1 : (z :: tl).length - 1 = (z :: tl).dropLast.length := by
        rw [length_dropLast, length_cons]
      rw [h1]
      exact hidx
    have hi_get : (y :: z :: tl).get ⟨i, hi_lt_len⟩ = x := by
      dsimp only [i]
      rw [get_cons_succ, get_eq_get_dropLast hi_z, get_eq_getElem,
        getElem_idxOf (idxOf_lt_length_of_mem hx_mem)]
    exact ⟨i, hi_lt_len, Nat.succ_pos _, hi_pred, hi_get⟩

end decidableCount

end List
