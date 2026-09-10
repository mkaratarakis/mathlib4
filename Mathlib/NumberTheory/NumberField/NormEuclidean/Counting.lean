/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Counting integer tuples in a box with prescribed residues

Fix a finite index type `ι`, moduli `M : ι → ℕ` with `0 < M i`, and a set `S` of tuples of
residues, that is a `Finset (∀ i, ZMod (M i))`.  This file counts the integer tuples
`a : ι → ℤ` lying in the box `|a i| ≤ X` whose reduction `fun i ↦ (a i : ZMod (M i))` belongs
to `S`, and shows that the proportion of such tuples in the box tends to
`#S / ∏ i, M i` as `X → ∞`.

Allowing a different modulus for each coordinate is what makes the statement usable for
Eisenstein-type conditions on the coefficients of a polynomial, where the modulus attached to
the `i`-th coefficient varies with `i`.

## Main results

* `Int.le_card_Ioc_filter_modEq`, `Int.card_Ioc_filter_modEq_le`: an interval `(a, b]` contains
  between `(b - a) / r - 1` and `(b - a) / r + 1` integers in a fixed residue class mod `r`.
* `Int.card_box_filter_eq_sum`: the count splits as a sum over `S` of products of
  one-dimensional counts.
* `Int.le_card_box_filter`, `Int.card_box_filter_le`: the two-sided sandwich
  `#S * ∏ i, ((2 * X + 1) / M i - 1) ≤ count ≤ #S * ∏ i, ((2 * X + 1) / M i + 1)`.
* `Int.tendsto_card_box_filter_div`: the density
  `count / (2 * X + 1) ^ card ι → #S / ∏ i, M i`.
* `Int.tendsto_card_box_filter_div_piFinset`: for a product set `S = ∏ i, T i` the density
  factorises as `∏ i, #(T i) / M i`.

## References

The counting lemma of [Hibbler, McGown, Treviño, *Polynomial densities and Heilbronn's
criterion*][hibbler_mcgown_trevino2025] uses a single modulus for all coordinates, which suffices
for the Eisenstein condition; the version here allows one modulus per coordinate, as the
Eisenstein–Dumas condition requires.
-/

public section

open Filter Finset Topology

namespace Int

/-! ### One-dimensional counts -/

/-- An interval `(a, b]` contains at least `(b - a) / r - 1` integers congruent to `v` mod `r`. -/
theorem le_card_Ioc_filter_modEq {r : ℤ} (hr : 0 < r) (a b v : ℤ) :
    ((b : ℚ) - a) / r - 1 ≤ #{x ∈ Finset.Ioc a b | x ≡ v [ZMOD r]} := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hcast : (#{x ∈ Finset.Ioc a b | x ≡ v [ZMOD r]} : ℚ) =
      ((max (⌊((b : ℚ) - (v : ℚ)) / (r : ℚ)⌋ - ⌊((a : ℚ) - (v : ℚ)) / (r : ℚ)⌋) 0 : ℤ) : ℚ) := by
    rw [← Int.Ioc_filter_modEq_card a b hr v]; push_cast; ring
  rw [hcast]
  have h1 := Int.sub_one_lt_floor (((b : ℚ) - (v : ℚ)) / (r : ℚ))
  have h2 := Int.floor_le (((a : ℚ) - (v : ℚ)) / (r : ℚ))
  have hdiv : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b : ℚ) - a) / r := by
    field_simp
    ring
  push_cast
  refine le_trans ?_ (le_max_left _ _)
  linarith

/-- An interval `(a, b]` contains at most `(b - a) / r + 1` integers congruent to `v` mod `r`. -/
theorem card_Ioc_filter_modEq_le {r : ℤ} (hr : 0 < r) {a b : ℤ} (hab : a ≤ b) (v : ℤ) :
    (#{x ∈ Finset.Ioc a b | x ≡ v [ZMOD r]} : ℚ) ≤ ((b : ℚ) - a) / r + 1 := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hab' : (0 : ℚ) ≤ ((b : ℚ) - a) / r := by
    apply div_nonneg _ hrQ.le
    have : (a : ℚ) ≤ b := by exact_mod_cast hab
    linarith
  have hcast : (#{x ∈ Finset.Ioc a b | x ≡ v [ZMOD r]} : ℚ) =
      ((max (⌊((b : ℚ) - (v : ℚ)) / (r : ℚ)⌋ - ⌊((a : ℚ) - (v : ℚ)) / (r : ℚ)⌋) 0 : ℤ) : ℚ) := by
    rw [← Int.Ioc_filter_modEq_card a b hr v]; push_cast; ring
  rw [hcast]
  have h1 := Int.floor_le (((b : ℚ) - (v : ℚ)) / (r : ℚ))
  have h2 := Int.sub_one_lt_floor (((a : ℚ) - (v : ℚ)) / (r : ℚ))
  have hdiv : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b : ℚ) - a) / r := by
    field_simp
    ring
  push_cast
  refine max_le ?_ (by linarith)
  linarith

/-- The symmetric box `|x| ≤ X` as a half-open interval, so that the counts above apply. -/
theorem Icc_neg_natCast_eq_Ioc (X : ℕ) :
    Finset.Icc (-(X : ℤ)) (X : ℤ) = Finset.Ioc (-(X : ℤ) - 1) (X : ℤ) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- The residue class of `s` mod `m` is a congruence class of integers. -/
theorem filter_intCast_eq (m : ℕ) [NeZero m] (s : ZMod m) (T : Finset ℤ) :
    {x ∈ T | ((x : ℤ) : ZMod m) = s} = {x ∈ T | x ≡ (s.val : ℤ) [ZMOD (m : ℤ)]} := by
  refine Finset.filter_congr fun x _ => ?_
  rw [← ZMod.intCast_eq_intCast_iff]
  simp

/-- At least `(2 * X + 1) / m - 1` of the integers `x` with `|x| ≤ X` reduce to `s` mod `m`. -/
theorem le_card_Icc_filter_intCast_eq {m : ℕ} (hm : 0 < m) (s : ZMod m) (X : ℕ) :
    (2 * X + 1 : ℝ) / m - 1 ≤ #{x ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) | ((x : ℤ) : ZMod m) = s} := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [Icc_neg_natCast_eq_Ioc, filter_intCast_eq]
  have h := le_card_Ioc_filter_modEq (r := (m : ℤ)) (by exact_mod_cast hm)
    (-(X : ℤ) - 1) (X : ℤ) (s.val : ℤ)
  have h' := (Rat.cast_le (K := ℝ)).2 h
  push_cast at h' ⊢
  refine le_trans (le_of_eq ?_) h'
  ring

/-- At most `(2 * X + 1) / m + 1` of the integers `x` with `|x| ≤ X` reduce to `s` mod `m`. -/
theorem card_Icc_filter_intCast_eq_le {m : ℕ} (hm : 0 < m) (s : ZMod m) (X : ℕ) :
    (#{x ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) | ((x : ℤ) : ZMod m) = s} : ℝ) ≤ (2 * X + 1) / m + 1 := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [Icc_neg_natCast_eq_Ioc, filter_intCast_eq]
  have h := card_Ioc_filter_modEq_le (r := (m : ℤ)) (by exact_mod_cast hm)
    (a := -(X : ℤ) - 1) (b := (X : ℤ)) (by omega) (s.val : ℤ)
  have h' := (Rat.cast_le (K := ℝ)).2 h
  push_cast at h' ⊢
  refine le_trans h' (le_of_eq ?_)
  ring

/-! ### The box-counting lemma -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → ℕ}

/-- The number of integer tuples `a` in the box `|a i| ≤ X` whose reduction lies in `S` is the
sum over `s ∈ S` of the products of the one-dimensional counts. -/
theorem card_box_filter_eq_sum (S : Finset (∀ i, ZMod (M i))) (X : ℕ) :
    #{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
        (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S}
      = ∑ s ∈ S, ∏ i, #{x ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) | ((x : ℤ) : ZMod (M i)) = s i} := by
  classical
  refine Eq.trans (Finset.card_eq_sum_card_fiberwise
    (f := fun a : ι → ℤ => fun i => (((a i : ℤ) : ZMod (M i))))
    (s := {a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
      (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S}) (t := S)
    fun a ha => (Finset.mem_filter.1 ha).2) ?_
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [show {a ∈ {a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
        (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S} | (fun i => (((a i : ℤ) : ZMod (M i)))) = s}
      = Fintype.piFinset fun i =>
        {x ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) | ((x : ℤ) : ZMod (M i)) = s i} from ?_,
    Fintype.card_piFinset]
  ext a
  simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
  refine ⟨fun h i => ⟨h.1.1 i, h.2 i⟩, fun h => ⟨⟨fun i => (h i).1, ?_⟩, fun i => (h i).2⟩⟩
  exact (funext fun i => (h i).2 : (fun i => (((a i : ℤ) : ZMod (M i)))) = s) ▸ hs

/-- Upper bound in the box-counting lemma: the count is at most
`#S * ∏ i, ((2 * X + 1) / M i + 1)`. -/
theorem card_box_filter_le (hM : ∀ i, 0 < M i) (S : Finset (∀ i, ZMod (M i))) (X : ℕ) :
    (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
        (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S} : ℝ)
      ≤ #S * ∏ i, ((2 * (X : ℝ) + 1) / M i + 1) := by
  rw [card_box_filter_eq_sum]
  push_cast
  calc ∑ s ∈ S, ∏ i, (#{x ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) | ((x : ℤ) : ZMod (M i)) = s i} : ℝ)
      ≤ ∑ _s ∈ S, ∏ i : ι, ((2 * (X : ℝ) + 1) / M i + 1) :=
        Finset.sum_le_sum fun s _ => Finset.prod_le_prod (fun i _ => by positivity)
          fun i _ => card_Icc_filter_intCast_eq_le (hM i) (s i) X
    _ = #S * ∏ i, ((2 * (X : ℝ) + 1) / M i + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Lower bound in the box-counting lemma: as soon as the box is at least as long as every
modulus, the count is at least `#S * ∏ i, ((2 * X + 1) / M i - 1)`. -/
theorem le_card_box_filter (hM : ∀ i, 0 < M i) (S : Finset (∀ i, ZMod (M i))) {X : ℕ}
    (hX : ∀ i, M i ≤ 2 * X + 1) :
    (#S : ℝ) * ∏ i, ((2 * (X : ℝ) + 1) / M i - 1)
      ≤ #{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
          (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S} := by
  rw [card_box_filter_eq_sum]
  push_cast
  calc (#S : ℝ) * ∏ i, ((2 * (X : ℝ) + 1) / M i - 1)
      = ∑ _s ∈ S, ∏ i : ι, ((2 * (X : ℝ) + 1) / M i - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ s ∈ S, ∏ i, (#{x ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) |
          ((x : ℤ) : ZMod (M i)) = s i} : ℝ) := by
        refine Finset.sum_le_sum fun s _ => Finset.prod_le_prod (fun i _ => ?_)
          fun i _ => le_card_Icc_filter_intCast_eq (hM i) (s i) X
        have h1 : (0 : ℝ) < M i := by exact_mod_cast hM i
        have h2 : (M i : ℝ) ≤ 2 * X + 1 := by exact_mod_cast hX i
        rw [sub_nonneg, le_div_iff₀ h1]
        linarith

/-! ### The density -/

/-- **Box-counting density.**  The proportion of the integer tuples `a` with `|a i| ≤ X` whose
reduction `fun i ↦ (a i : ZMod (M i))` lies in `S` tends to `#S / ∏ i, M i`. -/
theorem tendsto_card_box_filter_div (hM : ∀ i, 0 < M i) (S : Finset (∀ i, ZMod (M i))) :
    Filter.Tendsto (fun X : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
          (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ S} : ℝ) / (2 * X + 1) ^ Fintype.card ι)
      Filter.atTop (nhds ((#S : ℝ) / ∏ i, (M i : ℝ))) := by
  have hMR : ∀ i, (0 : ℝ) < M i := fun i => by exact_mod_cast hM i
  have hpos : ∀ X : ℕ, (0 : ℝ) < 2 * X + 1 := fun X => by positivity
  have hinv : Filter.Tendsto (fun X : ℕ => (2 * (X : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop
      (Filter.tendsto_atTop_add_const_right _ 1
        ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos))
  -- the two auxiliary sequences have the expected limit
  have key : ∀ c : ℝ, Filter.Tendsto
      (fun X : ℕ => (#S : ℝ) * ∏ i, ((M i : ℝ)⁻¹ + c * (2 * (X : ℝ) + 1)⁻¹))
      Filter.atTop (nhds ((#S : ℝ) / ∏ i, (M i : ℝ))) := by
    intro c
    have h : Filter.Tendsto (fun X : ℕ => ∏ i, ((M i : ℝ)⁻¹ + c * (2 * (X : ℝ) + 1)⁻¹))
        Filter.atTop (nhds (∏ _i : ι, ((M _i : ℝ)⁻¹ + c * 0))) :=
      tendsto_finsetProd _ fun i _ => tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    simp only [mul_zero, add_zero] at h
    have h' := h.const_mul ((#S : ℝ))
    rwa [Finset.prod_inv_distrib, ← div_eq_mul_inv] at h'
  -- rewriting the two-sided sandwich after division by the size of the box
  have halg : ∀ (X : ℕ) (c : ℝ),
      ((#S : ℝ) * ∏ i, ((2 * (X : ℝ) + 1) / M i + c)) / (2 * (X : ℝ) + 1) ^ Fintype.card ι
        = (#S : ℝ) * ∏ i, ((M i : ℝ)⁻¹ + c * (2 * (X : ℝ) + 1)⁻¹) := by
    intro X c
    rw [mul_div_assoc, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_div_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    have h1 : (M i : ℝ) ≠ 0 := (hMR i).ne'
    have h2 : (2 * (X : ℝ) + 1) ≠ 0 := (hpos X).ne'
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (key (-1)) (key 1) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup M)] with X hX
    have hle : ∀ i, M i ≤ 2 * X + 1 := fun i =>
      le_trans (Finset.le_sup (Finset.mem_univ i)) (by omega)
    have h := le_card_box_filter hM S hle
    simp only [sub_eq_add_neg] at h
    rw [← halg X (-1)]
    gcongr
  · filter_upwards with X
    have h := card_box_filter_le hM S X
    rw [← halg X 1]
    gcongr

/-- For a product set of residues the density factorises into the local densities. -/
theorem card_piFinset_div_prod (T : ∀ i, Finset (ZMod (M i))) :
    (#(Fintype.piFinset T) : ℝ) / ∏ i, (M i : ℝ) = ∏ i, (#(T i) : ℝ) / M i := by
  rw [Fintype.card_piFinset, Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **Box-counting density for product conditions.**  If the residue condition is a product of
conditions on the individual coordinates, the density is the product of the local densities. -/
theorem tendsto_card_box_filter_div_piFinset (hM : ∀ i, 0 < M i) (T : ∀ i, Finset (ZMod (M i))) :
    Filter.Tendsto (fun X : ℕ =>
        (#{a ∈ Fintype.piFinset fun _ : ι => Finset.Icc (-(X : ℤ)) (X : ℤ) |
          (fun i => (((a i : ℤ) : ZMod (M i)))) ∈ Fintype.piFinset T} : ℝ)
            / (2 * X + 1) ^ Fintype.card ι)
      Filter.atTop (nhds (∏ i, (#(T i) : ℝ) / M i)) := by
  rw [← card_piFinset_div_prod]
  exact tendsto_card_box_filter_div hM _

end Int
