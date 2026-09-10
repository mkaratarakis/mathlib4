/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting elements in an interval with given residue

The theorems in this file generalise `Nat.card_multiples` in
`Mathlib/Data/Nat/Factorization/Basic.lean` to all integer intervals and any fixed residue (not just
zero, which reduces to the multiples). Theorems are given for `Ico` and `Ioc` intervals.
-/

public section


open Finset Int

namespace Int

variable (a b : ℤ) {r : ℤ}


lemma Ico_filter_modEq_eq (v : ℤ) :
    {x ∈ Ico a b | x ≡ v [ZMOD r]} =
    {x ∈ Ico (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

lemma Ioc_filter_modEq_eq (v : ℤ) :
    {x ∈ Ioc a b | x ≡ v [ZMOD r]} =
    {x ∈ Ioc (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ioc, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

variable (hr : 0 < r)
include hr

lemma Ico_filter_dvd_eq :
    {x ∈ Ico a b | r ∣ x} =
      (Ico ⌈a / (r : ℚ)⌉ ⌈b / (r : ℚ)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff₀, lt_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

lemma Ioc_filter_dvd_eq :
    {x ∈ Ioc a b | r ∣ x} =
      (Ioc ⌊a / (r : ℚ)⌋ ⌊b / (r : ℚ)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, floor_lt, le_floor, div_lt_iff₀, le_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

/-- There are `⌈b / r⌉ - ⌈a / r⌉` multiples of `r` in `[a, b)`, if `a ≤ b`. -/
theorem Ico_filter_dvd_card : #{x ∈ Ico a b | r ∣ x} = max (⌈b / (r : ℚ)⌉ - ⌈a / (r : ℚ)⌉) 0 := by
  rw [Ico_filter_dvd_eq _ _ hr, card_map, card_Ico, toNat_eq_max]

/-- There are `⌊b / r⌋ - ⌊a / r⌋` multiples of `r` in `(a, b]`, if `a ≤ b`. -/
theorem Ioc_filter_dvd_card : #{x ∈ Ioc a b | r ∣ x} = max (⌊b / (r : ℚ)⌋ - ⌊a / (r : ℚ)⌋) 0 := by
  rw [Ioc_filter_dvd_eq _ _ hr, card_map, card_Ioc, toNat_eq_max]

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. -/
theorem Ico_filter_modEq_card (v : ℤ) :
    #{x ∈ Ico a b | x ≡ v [ZMOD r]} = max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, hr]

/-- There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(a, b]`,
if `a ≤ b`. -/
theorem Ioc_filter_modEq_card (v : ℤ) :
    #{x ∈ Ioc a b | x ≡ v [ZMOD r]} = max (⌊(b - v) / (r : ℚ)⌋ - ⌊(a - v) / (r : ℚ)⌋) 0 := by
  simp [Ioc_filter_modEq_eq, Ioc_filter_dvd_eq, hr]

end Int

namespace Nat

variable (a b : ℕ) {r : ℕ}

lemma Ico_filter_modEq_cast {v : ℕ} :
    {x ∈ Ico a b | x ≡ v [MOD r]}.map castEmbedding =
      {x ∈ Ico (a : ℤ) (b : ℤ) | x ≡ v [ZMOD r]} := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by omega); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

lemma Ioc_filter_modEq_cast {v : ℕ} :
    {x ∈ Ioc a b | x ≡ v [MOD r]}.map castEmbedding =
      {x ∈ Ioc (a : ℤ) (b : ℤ) | x ≡ v [ZMOD r]} := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by lia); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

variable (hr : 0 < r)
include hr

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. `Nat` version of `Int.Ico_filter_modEq_card`. -/
theorem Ico_filter_modEq_card (v : ℕ) :
    #{x ∈ Ico a b | x ≡ v [MOD r]} = max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp_rw [← Ico_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ico_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/-- There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(a, b]`,
if `a ≤ b`. `Nat` version of `Int.Ioc_filter_modEq_card`. -/
theorem Ioc_filter_modEq_card (v : ℕ) :
    #{x ∈ Ioc a b | x ≡ v [MOD r]} = max (⌊(b - v) / (r : ℚ)⌋ - ⌊(a - v) / (r : ℚ)⌋) 0 := by
  simp_rw [← Ioc_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ioc_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/-- There are `⌈(b - v % r) / r⌉` numbers in `[0, b)` congruent to `v` mod `r`. -/
theorem count_modEq_card_eq_ceil (v : ℕ) :
    b.count (· ≡ v [MOD r]) = ⌈(b - (v % r : ℕ)) / (r : ℚ)⌉ := by
  have hr' : 0 < (r : ℚ) := by positivity
  rw [count_eq_card_filter_range, ← Ico_zero_eq_range, Ico_filter_modEq_card _ _ hr,
    max_eq_left (sub_nonneg.mpr <| by gcongr; positivity)]
  conv_lhs =>
    rw [← div_add_mod v r, cast_add, cast_mul, add_comm]
    tactic => simp_rw [← sub_sub, sub_div (_ - _), mul_div_cancel_left₀ _ hr'.ne',
      Int.ceil_sub_natCast]
    rw [sub_sub_sub_cancel_right, cast_zero, zero_sub]
  rw [sub_eq_self, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff₀ hr', lt_div_iff₀ hr', neg_one_mul,
    zero_mul, neg_lt_neg_iff, cast_lt]
  exact ⟨mod_lt _ hr, by simp⟩

/-- There are `b / r + [v % r < b % r]` numbers in `[0, b)` congruent to `v` mod `r`,
where `[·]` is the Iverson bracket. -/
theorem count_modEq_card (v : ℕ) :
    b.count (· ≡ v [MOD r]) = b / r + if v % r < b % r then 1 else 0 := by
  have hr' : 0 < (r : ℚ) := by positivity
  rw [← ofNat_inj, count_modEq_card_eq_ceil _ hr, cast_add]
  conv_lhs => rw [← div_add_mod b r, cast_add, cast_mul, ← add_sub, _root_.add_div,
    mul_div_cancel_left₀ _ hr'.ne', add_comm, Int.ceil_add_natCast, add_comm]
  rw [add_right_inj]
  split_ifs with h
  · rw [← cast_sub h.le, Int.ceil_eq_iff, div_le_iff₀ hr', lt_div_iff₀ hr', cast_one, Int.cast_one,
      sub_self, zero_mul, cast_pos, tsub_pos_iff_lt, one_mul, cast_le, tsub_le_iff_right]
    exact ⟨h, ((mod_lt _ hr).trans_le (by simp)).le⟩
  · rw [cast_zero, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff₀ hr', lt_div_iff₀ hr', zero_mul,
      tsub_nonpos, ← neg_eq_neg_one_mul, neg_lt_sub_iff_lt_add, ← cast_add, cast_lt, cast_le]
    exact ⟨(mod_lt _ hr).trans_le (by simp), not_lt.mp h⟩

end Nat

namespace Nat

/-! ### Counts over an initial segment -/

/-- The number of `u < M` congruent to `v` mod `Q`, as a single ceiling. -/
theorem card_range_filter_modEq {M Q : ℕ} (hQ : 0 < Q) (v : ℕ) :
    (#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℚ)
      = ((⌈((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ)⌉ : ℤ) : ℚ) := by
  have h : ((#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℕ) : ℤ)
      = ⌈((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ)⌉ := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card_eq_ceil _ hQ v
  exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h

/-- At least `M / Q - 1` of the `u < M` are congruent to `v` mod `Q`. -/
theorem le_card_range_filter_modEq {M Q : ℕ} (hQ : 0 < Q) (v : ℕ) :
    (M : ℚ) / Q - 1 ≤ #{u ∈ Finset.range M | u ≡ v [MOD Q]} := by
  have hQQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [card_range_filter_modEq hQ v]
  have h1 := Int.le_ceil (((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ))
  have h2 : ((v % Q : ℕ) : ℚ) < Q := by exact_mod_cast Nat.mod_lt _ hQ
  have h3 : ((M : ℚ) - (v % Q : ℕ)) / Q = (M : ℚ) / Q - ((v % Q : ℕ) : ℚ) / Q := by ring
  have h4 : ((v % Q : ℕ) : ℚ) / Q ≤ 1 := by rw [div_le_one hQQ]; linarith
  linarith

/-- At most `M / Q + 1` of the `u < M` are congruent to `v` mod `Q`. -/
theorem card_range_filter_modEq_le {M Q : ℕ} (hQ : 0 < Q) (v : ℕ) :
    (#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℚ) ≤ (M : ℚ) / Q + 1 := by
  have hQQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [card_range_filter_modEq hQ v]
  have h1 := Int.ceil_lt_add_one (((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ))
  have h2 : (0 : ℚ) ≤ ((v % Q : ℕ) : ℚ) := by positivity
  have h3 : ((M : ℚ) - (v % Q : ℕ)) / Q ≤ (M : ℚ) / Q := by
    rw [div_le_div_iff_of_pos_right hQQ]; linarith
  linarith

/-- At least `M / Q - M / (q Q) - 2` of the `u < M` are congruent to `v` mod `Q` and prime to
`q`, whenever `q` and `Q` are coprime:  the multiples of `q` in the class of `v` form a single
class modulo `q Q`. -/
theorem le_card_range_filter_modEq_not_dvd {M Q q : ℕ} (hQ : 0 < Q) (hq : 0 < q)
    (hcop : Nat.Coprime Q q) (v : ℕ) :
    (M : ℚ) / Q - (M : ℚ) / (q * Q) - 2 ≤
      #{u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} := by
  classical
  obtain ⟨c, hcQ, hcq⟩ := Nat.chineseRemainder hcop v 0
  have hsub : {u ∈ Finset.range M | u ≡ v [MOD Q]} ⊆
      {u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} ∪
      {u ∈ Finset.range M | u ≡ c [MOD Q * q]} := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hdvd : q ∣ u
    · refine Or.inr ⟨hu.1, ?_⟩
      refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hu.2.trans hcQ.symm, ?_⟩
      exact ((Nat.modEq_zero_iff_dvd).2 hdvd).trans hcq.symm
    · exact Or.inl ⟨hu.1, hdvd, hu.2⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    {u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]}
    {u ∈ Finset.range M | u ≡ c [MOD Q * q]}
  have hA := le_card_range_filter_modEq (M := M) hQ v
  have hC := card_range_filter_modEq_le (M := M) (Nat.mul_pos hQ hq) c
  have hcast : (#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℚ) ≤
      (#{u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} : ℚ) +
      (#{u ∈ Finset.range M | u ≡ c [MOD Q * q]} : ℚ) := by
    exact_mod_cast le_trans hcard hunion
  have hqQ : ((Q * q : ℕ) : ℚ) = (q : ℚ) * (Q : ℚ) := by push_cast; ring
  rw [hqQ] at hC
  linarith

/-- The `u < M` congruent to `r` mod `Q`, for `r < Q`, are exactly the `r + Q t` with
`t < (M - r + Q - 1) / Q`. -/
theorem filter_range_modEq_eq_image {M Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) :
    {u ∈ Finset.range M | u ≡ r [MOD Q]}
      = (Finset.range ((M - r + Q - 1) / Q)).image (fun t => r + Q * t) := by
  classical
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨huM, hucong⟩
    have hmod : u % Q = r := by
      have h : u % Q = r % Q := hucong
      rwa [Nat.mod_eq_of_lt hr] at h
    have hu : r + Q * (u / Q) = u := by rw [← hmod]; exact Nat.mod_add_div u Q
    refine ⟨u / Q, ?_, hu⟩
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hQ]
    have hru : r ≤ u := Nat.le.intro hu
    calc (u / Q + 1) * Q = Q * (u / Q) + Q := by ring
      _ = (u - r) + Q := by rw [Nat.eq_sub_of_add_eq' hu]
      _ ≤ M - r + Q - 1 := by omega
  · rintro ⟨t, htT, rfl⟩
    have hle : Q * t + Q ≤ M - r + Q - 1 := by
      have h1 : (t + 1) * Q ≤ M - r + Q - 1 := by
        rw [← Nat.le_div_iff_mul_le hQ]
        omega
      calc Q * t + Q = (t + 1) * Q := by ring
        _ ≤ M - r + Q - 1 := h1
    refine ⟨?_, ?_⟩
    · obtain ⟨s, hs⟩ : ∃ s, Q * t = s := ⟨_, rfl⟩
      rw [hs] at hle ⊢
      omega
    · simp [Nat.ModEq, Nat.add_mul_mod_self_left]

end Nat
