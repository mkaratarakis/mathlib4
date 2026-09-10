/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Producing an `n`-th power residue by a character sum

To apply Heilbronn's criterion one needs to write `p = u q₁ + v q₂` with `q₁ ∤ u`, `q₂ ∤ v` and
`u q₁` an `n`-th power residue modulo `p`.  When `gcd (p - 1, n) = 1` every residue is an `n`-th
power and there is nothing to do; in general one has to *find* a suitable `u`, and this is done by
a character sum.

Let `ψ` be a Dirichlet character modulo `p` of order `g = gcd (p - 1, n)`, so that `ψ y = 1`
exactly when `y` is an `n`-th power residue.  For `1 ≤ k ≤ g` the sums `ψ ^ k` detect that
condition (`NumberField.sum_pow_apply_eq`), and summing over a set `S` of candidates `u` — in the
application, those `u < p / q₁` prime to `q₁` and lying in a fixed class modulo `q₂ ^ 2`, the
class that forces `q₂ ∤ v` — expresses the number of good `u` as a main term plus character sums
attached to the `k` with `ψ ^ k ≠ 1`.  If those are small the count is positive, and a good `u`
exists: this is `NumberField.exists_apply_eq_one_of_lt_card`.

The smallness of the character sums is the Pólya–Vinogradov inequality, which is not available in
Mathlib; it is therefore carried as the hypothesis `hPV`, exactly as it is quoted from the
literature in the classical treatment.  Everything else is proved.

## Main results

* `NumberField.sum_pow_apply_eq`: `∑_{k=1}^{g} ψ^k x` is `g` if `ψ x = 1` and `0` otherwise.
* `NumberField.exists_apply_eq_one_of_lt_card`: if the character sums over `S` attached to the
  non-principal `ψ ^ k` are bounded by `B`, and the number of `u ∈ S` with `q₁ u` invertible
  exceeds `(g - 1) B`, then some `u ∈ S` has `ψ (q₁ u) = 1`.
-/

public section

open Finset

namespace NumberField

set_option linter.style.haveILetI false

/-- The sum of `ψ ^ k (x)` over `1 ≤ k ≤ g`, for a character `ψ` with `ψ ^ g = 1`, detects
`ψ x = 1`. -/
theorem sum_pow_apply_eq {p g : ℕ} [NeZero p] (hg : 0 < g) (ψ : DirichletCharacter ℂ p)
    (hψg : ψ ^ g = 1) (x : ZMod p) :
    ∑ k ∈ Finset.Icc 1 g, (ψ ^ k) x = if ψ x = 1 then (g : ℂ) else 0 := by
  by_cases hx : IsUnit x
  · set z := ψ x with hz
    have hzg : z ^ g = 1 := by
      have h1 : (ψ ^ g) x = z ^ g := MulChar.pow_apply' ψ hg.ne' x
      rw [hψg, MulChar.one_apply hx] at h1
      exact h1.symm
    have hterm : ∀ k ∈ Finset.Icc 1 g, (ψ ^ k) x = z ^ k := by
      intro k hk
      exact MulChar.pow_apply' ψ (by simp only [Finset.mem_Icc] at hk; omega) x
    rw [Finset.sum_congr rfl hterm]
    by_cases hz1 : z = 1
    · simp [hz1, Nat.card_Icc]
    · have hIco : Finset.Icc 1 g = Finset.Ico 1 (g + 1) := (Finset.val_inj.mp rfl).symm
      rw [hIco, Finset.sum_Ico_eq_sub _ (by omega), geom_sum_eq hz1, geom_sum_eq hz1]
      have hzz : z ^ (g + 1) = z := by rw [pow_succ, hzg, one_mul]
      have hz10 : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      rw [hzz, pow_one, div_self hz10, sub_self]
      simp only [hz1, ite_false]
  · have h0 : ∀ k ∈ Finset.Icc 1 g, (ψ ^ k) x = 0 := by
      intro k _
      exact MulChar.map_nonunit _ hx
    have hne1 : ¬ (ψ x = 1) := by
      rw [MulChar.map_nonunit ψ hx]
      exact zero_ne_one
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    simp only [hne1, ite_false]

open scoped Classical in
/-- **The character-sum count.**  Let `ψ` be a Dirichlet character mod `p` with `ψ ^ g = 1`, and
let `S` be any finite set of natural numbers — in the application, the `u < p / q₁` lying in a
fixed class modulo `q₂ ^ 2` and prime to `q₁`.  If every character sum `∑_{u ∈ S} ψ^k (q₁ u)` with
`ψ ^ k ≠ 1` is bounded by `B`, and the number of `u ∈ S` with `q₁ u` invertible mod `p` exceeds
`(g - 1) B`, then some `u ∈ S` has `ψ (q₁ u) = 1`, that is, `q₁ u` is an `n`-th power residue.

The hypothesis `hPV` is what the Pólya–Vinogradov inequality supplies: the sum of a non-principal
character over an interval, restricted to an arithmetic progression, is `O(√M log M)`. -/
theorem exists_apply_eq_one_of_lt_card {p q₁ g : ℕ} [NeZero p] (hg : 0 < g)
    (ψ : DirichletCharacter ℂ p) (hψg : ψ ^ g = 1) (S : Finset ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hPV : ∀ k ∈ Finset.Icc 1 g, ψ ^ k ≠ 1 →
      ‖∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ B)
    (hmain : ((g : ℝ) - 1) * B <
      #{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))}) :
    ∃ u ∈ S, ψ ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  -- with no good `u`, the double sum vanishes
  have hzero : ∑ u ∈ S, ∑ k ∈ Finset.Icc 1 g, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [sum_pow_apply_eq hg ψ hψg]
    simp only [hcon u hu, ite_false]
  -- the same double sum, summed the other way, splits off the terms with `ψ ^ k = 1`
  rw [Finset.sum_comm] at hzero
  have hsplit : ∑ k ∈ Finset.Icc 1 g, ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))
      = (∑ k ∈ {k ∈ Finset.Icc 1 g | ψ ^ k = 1},
            ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)))
        + ∑ k ∈ {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1},
            ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- each principal term is the main term
  have hprin : ∀ k ∈ {k ∈ Finset.Icc 1 g | ψ ^ k = 1},
      ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))
        = (#{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))} : ℂ) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2, Finset.sum_congr rfl (fun u _ => rfl)]
    rw [← Finset.sum_filter_add_sum_filter_not S
      (fun u => IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)))]
    rw [Finset.sum_congr rfl (fun u hu => MulChar.one_apply (Finset.mem_filter.1 hu).2),
      Finset.sum_congr rfl (fun u hu =>
        MulChar.map_nonunit (1 : DirichletCharacter ℂ p) (Finset.mem_filter.1 hu).2)]
    simp
  -- there is at least one principal term, and at most `g - 1` others
  have hone : (1 : ℕ) ≤ #{k ∈ Finset.Icc 1 g | ψ ^ k = 1} := by
    refine Finset.card_pos.2 ⟨g, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hg, le_refl g⟩, hψg⟩
  have hcard : #{k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} ≤ g - 1 := by
    have hsub : {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} ⊆ (Finset.Icc 1 g).erase g := by
      intro k hk
      rw [Finset.mem_filter] at hk
      exact Finset.mem_erase.2 ⟨fun h => hk.2 (h ▸ hψg), hk.1⟩
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_erase_of_mem (Finset.mem_Icc.2 ⟨hg, le_refl g⟩), Nat.card_Icc]
    omega
  -- bound the non-principal part
  have hbound : ‖∑ k ∈ {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1},
      ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ ((g : ℝ) - 1) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ B (fun k hk => ?_)) ?_
    · rw [Finset.mem_filter] at hk
      exact hPV k hk.1 hk.2
    · rw [nsmul_eq_mul]
      have hle : (#{k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} : ℝ) ≤ (g : ℝ) - 1 := by
        have h1 : (#{k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} : ℝ) ≤ ((g - 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
        have h2 : ((g - 1 : ℕ) : ℝ) ≤ (g : ℝ) - 1 := by
          have : 1 ≤ g := hg
          push_cast [Nat.cast_sub this]
          linarith
        linarith
      nlinarith
  -- put it together
  rw [hsplit, Finset.sum_congr rfl hprin, Finset.sum_const, nsmul_eq_mul] at hzero
  set M : ℝ := (#{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))} : ℝ) with hM
  have hMle : M ≤ ((g : ℝ) - 1) * B := by
    have heq : ((#{k ∈ Finset.Icc 1 g | ψ ^ k = 1} : ℂ)) * (M : ℂ)
        = -∑ k ∈ {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1},
            ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) := by
      rw [hM]
      push_cast at hzero ⊢
      linear_combination hzero
    have hnorm : ‖((#{k ∈ Finset.Icc 1 g | ψ ^ k = 1} : ℂ)) * (M : ℂ)‖ ≤ ((g : ℝ) - 1) * B := by
      rw [heq, norm_neg]
      exact hbound
    rw [norm_mul] at hnorm
    have h1 : (1 : ℝ) ≤ ‖((#{k ∈ Finset.Icc 1 g | ψ ^ k = 1} : ℂ))‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast hone
    have h2 : ‖(M : ℂ)‖ = M := by
      rw [hM]
      push_cast
      simp
    rw [h2] at hnorm
    nlinarith [hnorm, h1, Nat.cast_nonneg (α := ℝ)
      (#{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))})]
  linarith [hmain, hMle]

end NumberField
