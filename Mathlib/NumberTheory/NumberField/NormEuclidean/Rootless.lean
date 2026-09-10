/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Real.Basic

/-!
# Monic polynomials over a finite field with no roots

Let `F` be a finite field with `q` elements.  Monic polynomials of degree `n` over `F` are
parametrised by their lower coefficients, that is, by tuples `a : Fin n → F`, the polynomial being
`X ^ n + ∑ i, C (a i) * X ^ i`.  We count the tuples whose polynomial has no root in a prescribed
subset `T` of `F`: the answer is `∑ k, (-1) ^ k * (#T).choose k * q ^ (n - k)`, and for `T = F` and
`n ≥ q` this collapses to `(q - 1) ^ q * q ^ (n - q)`.

These are the local densities appearing in the study of the proportion of Eisenstein (or
Eisenstein–Dumas) polynomials generating a field that is not norm-Euclidean: `q` is not the norm of
an algebraic integer unless the polynomial has a root modulo `q`.

## Main results

* `Polynomial.card_no_root_eq_sum`: the inclusion–exclusion formula for the number of tuples whose
  monic polynomial avoids every root in `T`.
* `Polynomial.card_no_root_univ_eq`: the closed form `(q - 1) ^ q * q ^ (n - q)` when `n ≥ q`.
* `Polynomial.card_no_root_univ_div_bounds`: the bounds
  `(q ^ 2 - 1) / (3 * q ^ 2) ≤ C ≤ (q - 1) / (2 * q)` for the proportion `C`, valid for `n ≥ 2`.
* `Polynomial.card_no_root_univ_div_ge_quarter` and `Polynomial.card_no_root_univ_div_lt_half`:
  the coarser bounds `1 / 4 ≤ C < 1 / 2` in the form the density theorems use.

## References

The count of rootless monic polynomials over a finite field and the bounds for it are those of
[Hibbler, McGown, Treviño, *Polynomial densities and Heilbronn's
criterion*][hibbler_mcgown_trevino2025].
-/

public section

open Finset

namespace Polynomial

/-! ### Monic polynomials of degree `n` and their coefficient tuples -/

section Dictionary

variable {R : Type*} [Semiring R]

/-- The polynomial attached to a coefficient tuple is monic. -/
theorem monic_X_pow_add_sum (n : ℕ) (a : Fin n → R) :
    (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).Monic := by
  refine monic_X_pow_add (lt_of_le_of_lt (degree_sum_le _ _) ?_)
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  exact fun i _ => lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)

/-- The polynomial attached to a coefficient tuple has degree `n`. -/
theorem natDegree_X_pow_add_sum [Nontrivial R] (n : ℕ) (a : Fin n → R) :
    (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).natDegree = n := by
  refine natDegree_eq_of_degree_eq_some ?_
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  exact fun i _ => lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)

/-- The coefficients of the polynomial attached to a tuple are the entries of the tuple:  the
assignment `a ↦ X ^ n + ∑ a i X ^ i` is injective, with the coefficient map as its inverse. -/
theorem coeff_X_pow_add_sum {n : ℕ} (a : Fin n → R) (i : Fin n) :
    (X ^ n + ∑ j : Fin n, C (a j) * X ^ (j : ℕ)).coeff i = a i := by
  have hi : (i : ℕ) ≠ n := by omega
  have h1 : ((X : R[X]) ^ n).coeff i = 0 := by simp [coeff_X_pow, hi]
  rw [coeff_add, h1, zero_add, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.val_injective h.symm)
    simp [coeff_C_mul, coeff_X_pow, this]
  · simp

/-- Every monic polynomial of degree `n` is the one attached to its own tuple of coefficients:
together with `coeff_X_pow_add_sum` this identifies the monic polynomials of degree `n` with the
tuples in `Fin n → R`. -/
theorem eq_X_pow_add_sum_of_monic {f : R[X]} (hf : f.Monic) {n : ℕ} (hd : f.natDegree = n) :
    f = X ^ n + ∑ i : Fin n, C (f.coeff i) * X ^ (i : ℕ) := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := n + 1) (by omega)]
  rw [Finset.sum_range_succ, ← hd, hf.coeff_natDegree, map_one, one_mul, hd, add_comm,
    Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) n]

end Dictionary

/-! ### Counting the tuples whose polynomial vanishes on a given set -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of monic polynomials of degree `n` over a finite field with `q` elements vanishing
at every point of a set `S` of at most `n` points is `q ^ (n - #S)`. -/
theorem card_forall_isRoot (n : ℕ) (S : Finset F) (hS : #S ≤ n) :
    #{a : Fin n → F | ∀ r ∈ S, (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} =
      Fintype.card F ^ (n - #S) := by
  classical
  set g : F[X] := ∏ r ∈ S, (X - C r) with hg
  have hgm : g.Monic := monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have hgd : g.natDegree = #S := by
    rw [hg, natDegree_prod _ _ fun r _ => X_sub_C_ne_zero r]
    simp
  -- vanishing on `S` is the same as being divisible by `g`
  have hiff : ∀ f : F[X], (∀ r ∈ S, f.IsRoot r) ↔ g ∣ f := by
    intro f
    refine ⟨fun h => Finset.prod_dvd_of_coprime ?_ fun r hr => dvd_iff_isRoot.2 (h r hr), ?_⟩
    · intro r hr s hs hrs
      exact (pairwise_coprime_X_sub_C (Function.injective_id (α := F))) hrs
    · intro h r hr
      exact (dvd_iff_isRoot (a := r)).1 (dvd_trans (Finset.dvd_prod_of_mem (fun s => X - C s) hr) h)
  -- and monic polynomials of degree `n` divisible by `g` are `g` times a monic polynomial of
  -- degree `n - #S`
  rw [← Fintype.card_fin (n - #S), ← Fintype.card_fun, ← Finset.card_univ]
  refine Finset.card_nbij'
    (fun a => fun j : Fin (n - #S) =>
      ((X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)) /ₘ g).coeff j)
    (fun b => fun i : Fin n =>
      (g * (X ^ (n - #S) + ∑ j : Fin (n - #S), C (b j) * X ^ (j : ℕ))).coeff i)
    ?_ ?_ ?_ ?_
  · exact fun a _ => Finset.mem_univ _
  · intro b _
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
    set h : F[X] := X ^ (n - #S) + ∑ j : Fin (n - #S), C (b j) * X ^ (j : ℕ) with hh
    have hhm : h.Monic := monic_X_pow_add_sum _ _
    have hprod : (g * h).Monic := hgm.mul hhm
    have hdeg : (g * h).natDegree = n := by
      rw [natDegree_mul hgm.ne_zero hhm.ne_zero, hgd, hh, natDegree_X_pow_add_sum]
      omega
    rw [← eq_X_pow_add_sum_of_monic hprod hdeg, hiff]
    exact Dvd.intro h rfl
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    funext i
    dsimp only
    set f : F[X] := X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ) with hf
    have hfm : f.Monic := monic_X_pow_add_sum _ _
    have hdvd : g ∣ f := (hiff f).1 ha.2
    have hmul : g * (f /ₘ g) = f := by
      conv_rhs => rw [← modByMonic_add_div f g, (modByMonic_eq_zero_iff_dvd hgm).2 hdvd, zero_add]
    have hqm : (f /ₘ g).Monic := hgm.of_mul_monic_left (by rw [hmul]; exact hfm)
    have hfd : f.natDegree = n := by rw [hf]; exact natDegree_X_pow_add_sum _ _
    have hqd : (f /ₘ g).natDegree = n - #S := by
      have h2 := natDegree_mul hgm.ne_zero hqm.ne_zero
      rw [hmul, hfd, hgd] at h2
      omega
    have : g * (X ^ (n - #S) + ∑ j : Fin (n - #S), C ((f /ₘ g).coeff j) * X ^ (j : ℕ)) = f := by
      rw [← eq_X_pow_add_sum_of_monic hqm hqd, hmul]
    rw [this, hf, coeff_X_pow_add_sum]
  · intro b _
    funext j
    dsimp only
    set h : F[X] := X ^ (n - #S) + ∑ j : Fin (n - #S), C (b j) * X ^ (j : ℕ) with hh
    have hhm : h.Monic := monic_X_pow_add_sum _ _
    have hprod : (g * h).Monic := hgm.mul hhm
    have hdeg : (g * h).natDegree = n := by
      rw [natDegree_mul hgm.ne_zero hhm.ne_zero, hgd, hh, natDegree_X_pow_add_sum]
      omega
    rw [← eq_X_pow_add_sum_of_monic hprod hdeg, mul_divByMonic_cancel_left _ hgm, hh,
      coeff_X_pow_add_sum]

/-! ### The inclusion–exclusion count -/

/-- **The number of monic polynomials with no root in a prescribed set.**  Over a finite field with
`q` elements, the number of monic polynomials of degree `n` having no root in `T` is
`∑ k, (-1) ^ k * (#T).choose k * q ^ (n - k)`.  For `T = Finset.univ` this is the count of
rootless monic polynomials of degree `n`. -/
theorem card_no_root_eq_sum (n : ℕ) (T : Finset F) :
    (#{a : Fin n → F | ∀ r ∈ T, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℤ) =
      ∑ k ∈ range (n + 1), (-1) ^ k * ((#T).choose k : ℤ) * (Fintype.card F : ℤ) ^ (n - k) := by
  classical
  set Sr : F → Finset (Fin n → F) :=
    fun r => {a | (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} with hSr
  -- a monic polynomial of degree `n` has at most `n` roots
  have hroots : ∀ (t : Finset F) (a : Fin n → F),
      (∀ r ∈ t, (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r) → #t ≤ n := by
    intro t a ha
    have hne : (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)) ≠ 0 := (monic_X_pow_add_sum n a).ne_zero
    have hsub : t.val ≤ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).roots := by
      rw [Multiset.le_iff_subset t.nodup]
      intro r hr
      exact (mem_roots hne).2 (ha r hr)
    calc #t = Multiset.card t.val := rfl
      _ ≤ Multiset.card (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).roots :=
          Multiset.card_le_card hsub
      _ ≤ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).natDegree := card_roots' _
      _ = n := natDegree_X_pow_add_sum n a
  -- the tuples vanishing on a set `t` of size `k ≤ n` are a `q ^ (n - k)`-element set
  have hinf : ∀ t : Finset F,
      (#(t.inf Sr) : ℤ) = if #t ≤ n then (Fintype.card F : ℤ) ^ (n - #t) else 0 := by
    intro t
    have hset : t.inf Sr = ({a | ∀ r ∈ t,
        (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : Finset (Fin n → F)) := by
      ext a; simp [Finset.mem_inf, hSr]
    split_ifs with h
    · rw [hset, card_forall_isRoot n t h]
      push_cast
      ring
    · rw [hset, Finset.card_eq_zero.2 ?_, Nat.cast_zero]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact h (hroots t a ha)
  -- the rootless tuples are the intersection of the complements, so inclusion-exclusion applies
  have hcompl : T.inf (fun r => (Sr r)ᶜ) =
      ({a | ∀ r ∈ T, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} :
        Finset (Fin n → F)) := by
    ext a; simp [Finset.mem_inf, hSr]
  rw [← hcompl, Finset.inclusion_exclusion_card_inf_compl T Sr]
  -- group the subsets of `T` by their cardinality
  rw [Finset.powerset_card_biUnion, Finset.sum_biUnion
    (fun i _ j _ hij => Finset.pairwise_disjoint_powersetCard T hij)]
  have hstep : ∀ k ∈ range (#T + 1), ∑ t ∈ T.powersetCard k, (-1 : ℤ) ^ #t * #(t.inf Sr) =
      (-1) ^ k * ((#T).choose k : ℤ) * (if k ≤ n then (Fintype.card F : ℤ) ^ (n - k) else 0) := by
    intro k _
    have hconst : ∀ t ∈ T.powersetCard k, (-1 : ℤ) ^ #t * #(t.inf Sr) =
        (-1) ^ k * (if k ≤ n then (Fintype.card F : ℤ) ^ (n - k) else 0) := by
      intro t ht
      rw [(Finset.mem_powersetCard.1 ht).2, hinf t, (Finset.mem_powersetCard.1 ht).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hstep]
  rcases le_total (#T) n with hTn | hTn
  · rw [Finset.sum_subset (fun k hk => Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hk) (by omega : #T + 1 ≤ n + 1))) ?_]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk
      simp [hkn]
    · intro k _ hk
      rw [Nat.choose_eq_zero_of_lt (by simpa [Nat.lt_succ_iff, not_le] using hk)]
      simp
  · rw [← Finset.sum_subset (fun k hk => Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hk) (by omega : n + 1 ≤ #T + 1))) ?_]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk
      simp [hkn]
    · intro k _ hk
      have hkn : ¬ k ≤ n := by simpa [Nat.lt_succ_iff, not_le] using hk
      simp [hkn]

/-! ### The closed form and the bounds for the proportion of rootless polynomials -/

/-- The count of `card_no_root_eq_sum` for `T = Finset.univ`, phrased without the membership. -/
theorem card_no_root_univ_eq_sum (n : ℕ) :
    (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℤ) =
      ∑ k ∈ range (n + 1),
        (-1) ^ k * ((Fintype.card F).choose k : ℤ) * (Fintype.card F : ℤ) ^ (n - k) := by
  classical
  have h := card_no_root_eq_sum n (Finset.univ : Finset F)
  rw [Finset.card_univ] at h
  rw [← h]
  congr 2
  exact Finset.filter_congr fun a _ => by simp

/-- **Closed form.**  If `n ≥ q` then the number of monic polynomials of degree `n` over a finite
field with `q` elements having no root at all is `(q - 1) ^ q * q ^ (n - q)`; equivalently the
proportion is `(1 - 1 / q) ^ q`. -/
theorem card_no_root_univ_eq {n : ℕ} (hn : Fintype.card F ≤ n) :
    (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ Fintype.card F *
        (Fintype.card F : ℤ) ^ (n - Fintype.card F) := by
  classical
  rw [card_no_root_univ_eq_sum n]
  set q := Fintype.card F with hq
  -- only the terms with `k ≤ q` contribute
  rw [← Finset.sum_subset (s₁ := range (q + 1)) (fun k hk => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hk) (by omega))) ?_]
  · rw [show ((q : ℤ) - 1) ^ q = ∑ k ∈ range (q + 1), (-1 : ℤ) ^ k * (q : ℤ) ^ (q - k) *
        (q.choose k : ℤ) by rw [← add_pow (-1 : ℤ) (q : ℤ) q]; ring_nf]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ q := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk
    have hpow : (q : ℤ) ^ (q - k) * (q : ℤ) ^ (n - q) = (q : ℤ) ^ (n - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hpow]
    ring
  · intro k _ hk
    rw [Nat.choose_eq_zero_of_lt (by simpa [Nat.lt_succ_iff, not_le] using hk)]
    simp

/-- The alternating sum of an antitone sequence of nonnegative reals lies between `0` and its
first term. -/
theorem _root_.Finset.sum_range_alternating_bounds {f : ℕ → ℝ} (hanti : ∀ k, f (k + 1) ≤ f k)
    (hpos : ∀ k, 0 ≤ f k) (d m : ℕ) :
    0 ≤ ∑ k ∈ range d, (-1 : ℝ) ^ k * f (m + k) ∧
      ∑ k ∈ range d, (-1 : ℝ) ^ k * f (m + k) ≤ f m := by
  induction d generalizing m with
  | zero => simpa using hpos m
  | succ d ih =>
      have hsplit : ∑ k ∈ range (d + 1), (-1 : ℝ) ^ k * f (m + k) =
          f m - ∑ k ∈ range d, (-1 : ℝ) ^ k * f ((m + 1) + k) := by
        have hterm : ∀ k ∈ range d, (-1 : ℝ) ^ (k + 1) * f (m + (k + 1)) =
            -((-1 : ℝ) ^ k * f (m + 1 + k)) := by
          intro k _
          rw [show m + (k + 1) = m + 1 + k by omega, pow_succ]
          ring
        rw [Finset.sum_range_succ', Finset.sum_congr rfl hterm, Finset.sum_neg_distrib,
          pow_zero, one_mul, add_zero]
        ring
      obtain ⟨h1, h2⟩ := ih (m + 1)
      constructor
      · rw [hsplit]
        have := hanti m
        linarith
      · rw [hsplit]
        linarith

/-- Peeling the first term off an alternating sum. -/
theorem _root_.Finset.sum_range_alternating_succ (f : ℕ → ℝ) (d m : ℕ) :
    ∑ k ∈ range (d + 1), (-1 : ℝ) ^ k * f (m + k) =
      f m - ∑ k ∈ range d, (-1 : ℝ) ^ k * f (m + 1 + k) := by
  have hterm : ∀ k ∈ range d, (-1 : ℝ) ^ (k + 1) * f (m + (k + 1)) =
      -((-1 : ℝ) ^ k * f (m + 1 + k)) := by
    intro k _
    rw [show m + (k + 1) = m + 1 + k by omega, pow_succ]
    ring
  rw [Finset.sum_range_succ', Finset.sum_congr rfl hterm, Finset.sum_neg_distrib,
    pow_zero, one_mul, add_zero]
  ring

/-- The proportion of rootless monic polynomials, as an alternating sum. -/
theorem card_no_root_univ_div_eq (n : ℕ) :
    (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℝ) /
        (Fintype.card F : ℝ) ^ n =
      ∑ k ∈ range (n + 1),
        (-1 : ℝ) ^ k * ((Fintype.card F).choose k / (Fintype.card F : ℝ) ^ k) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_eq_iff (by positivity), Finset.sum_mul]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (card_no_root_univ_eq_sum (F := F) n)
  push_cast at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk
  have hsplit : (Fintype.card F : ℝ) ^ n
      = (Fintype.card F : ℝ) ^ (n - k) * (Fintype.card F : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp

/-- The proportion `C` of monic polynomials of degree `n ≥ 2` over a finite field with `q`
elements having no root satisfies `(q ^ 2 - 1) / (3 * q ^ 2) ≤ C ≤ (q - 1) / (2 * q)`. -/
theorem card_no_root_univ_div_bounds {n : ℕ} (hn : 2 ≤ n) :
    ((Fintype.card F : ℝ) ^ 2 - 1) / (3 * (Fintype.card F : ℝ) ^ 2) ≤
      (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℝ) /
        (Fintype.card F : ℝ) ^ n ∧
      (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℝ) /
        (Fintype.card F : ℝ) ^ n ≤ ((Fintype.card F : ℝ) - 1) / (2 * Fintype.card F) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hq2
  have hq2' : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq2
  -- the inclusion-exclusion sum has terms `g k = C(q, k) / q ^ k`, which decrease in `k`
  set g : ℕ → ℝ := fun k => ((Fintype.card F).choose k : ℝ) / (Fintype.card F : ℝ) ^ k with hg
  have hpos : ∀ k, 0 ≤ g k := fun k => by positivity
  have hanti : ∀ k, g (k + 1) ≤ g k := by
    intro k
    have hnat : (Fintype.card F).choose (k + 1) ≤ (Fintype.card F).choose k * Fintype.card F := by
      have h1 := Nat.choose_succ_right_eq (Fintype.card F) k
      have h2 : (Fintype.card F).choose k * (Fintype.card F - k) ≤
          (Fintype.card F).choose k * Fintype.card F * (k + 1) := by
        calc (Fintype.card F).choose k * (Fintype.card F - k)
            ≤ (Fintype.card F).choose k * Fintype.card F := by
              refine Nat.mul_le_mul_left _ ?_
              omega
          _ ≤ (Fintype.card F).choose k * Fintype.card F * (k + 1) :=
              Nat.le_mul_of_pos_right _ (by omega)
      rw [← h1] at h2
      exact Nat.le_of_mul_le_mul_right h2 (by omega)
    have hcast : ((Fintype.card F).choose (k + 1) : ℝ) ≤
        ((Fintype.card F).choose k : ℝ) * (Fintype.card F : ℝ) := by exact_mod_cast hnat
    rw [hg]
    dsimp only
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((Fintype.card F).choose (k + 1) : ℝ) * (Fintype.card F : ℝ) ^ k
        ≤ (((Fintype.card F).choose k : ℝ) * (Fintype.card F : ℝ)) * (Fintype.card F : ℝ) ^ k := by
          have : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ k := by positivity
          nlinarith
      _ = ((Fintype.card F).choose k : ℝ) * (Fintype.card F : ℝ) ^ (k + 1) := by ring
  -- the first two terms cancel
  have hzero : g 0 = 1 := by simp [hg]
  have hone : g 1 = 1 := by
    rw [hg]
    simp [Nat.choose_one_right]
  have hsum : (#{a : Fin (d + 2) → F | ∀ r : F,
      ¬ (X ^ (d + 2) + ∑ i : Fin (d + 2), C (a i) * X ^ (i : ℕ)).IsRoot r} : ℝ) /
        (Fintype.card F : ℝ) ^ (d + 2) = ∑ k ∈ range (d + 1), (-1 : ℝ) ^ k * g (2 + k) := by
    rw [card_no_root_univ_div_eq, Finset.sum_range_succ', Finset.sum_range_succ']
    have hterm : ∀ i ∈ range (d + 1), (-1 : ℝ) ^ (i + 1 + 1) *
        (((Fintype.card F).choose (i + 1 + 1) : ℝ) / (Fintype.card F : ℝ) ^ (i + 1 + 1)) =
        (-1 : ℝ) ^ i * g (2 + i) := by
      intro i _
      rw [hg, show i + 1 + 1 = 2 + i by omega]
      ring
    rw [Finset.sum_congr rfl hterm]
    have h1 : ((Fintype.card F).choose 1 : ℝ) / (Fintype.card F : ℝ) ^ 1 = 1 := by
      rw [Nat.choose_one_right, pow_one, div_self hq.ne']
    rw [show ((0 : ℕ) + 1) = 1 from rfl, h1]
    norm_num
  -- the two-sided estimate for the alternating tail
  obtain ⟨hlow, hhigh⟩ := Finset.sum_range_alternating_bounds hanti hpos (d + 1) 2
  -- the first two terms of the tail, which bracket it
  have hg2 : g 2 = ((Fintype.card F : ℝ) - 1) / (2 * Fintype.card F) := by
    have h1 := Nat.choose_succ_right_eq (Fintype.card F) 1
    rw [Nat.choose_one_right] at h1
    have h2 : ((Fintype.card F).choose 2 : ℝ) * 2 = (Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ) - 1) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) h1
      push_cast [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)] at this
      linarith
    rw [hg]
    dsimp only
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (Fintype.card F : ℝ) * h2
  have hg3 : g 3 = ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) /
      (6 * (Fintype.card F : ℝ) ^ 2) := by
    have h1 := Nat.choose_succ_right_eq (Fintype.card F) 2
    have h2 := Nat.choose_succ_right_eq (Fintype.card F) 1
    rw [Nat.choose_one_right] at h2
    have c2 : ((Fintype.card F).choose 2 : ℝ) * 2 = (Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ) - 1) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) h2
      push_cast [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)] at this
      linarith
    have c3 : ((Fintype.card F).choose 3 : ℝ) * 3 = ((Fintype.card F).choose 2 : ℝ) *
        ((Fintype.card F : ℝ) - 2) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) h1
      push_cast [Nat.cast_sub (by omega : 2 ≤ Fintype.card F)] at this
      linarith
    have h6 : ((Fintype.card F).choose 3 : ℝ) * 6 = (Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) := by
      linear_combination 2 * c3 + ((Fintype.card F : ℝ) - 2) * c2
    rw [hg]
    dsimp only
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (Fintype.card F : ℝ) ^ 2 * h6
  -- the tail lies between `g 2 - g 3` and `g 2`
  constructor
  · -- lower bound
    rw [hsum, Finset.sum_range_alternating_succ (fun k => g k) d 2]
    obtain ⟨_, htail⟩ := Finset.sum_range_alternating_bounds hanti hpos d 3
    have h3 : ∑ k ∈ range d, (-1 : ℝ) ^ k * g (2 + 1 + k) ≤ g 3 := by
      simpa using htail
    have : ((Fintype.card F : ℝ) ^ 2 - 1) / (3 * (Fintype.card F : ℝ) ^ 2) = g 2 - g 3 := by
      rw [hg2, hg3]
      field_simp
      ring
    rw [this]
    linarith
  · -- upper bound
    rw [hsum]
    calc ∑ k ∈ range (d + 1), (-1 : ℝ) ^ k * g (2 + k) ≤ g 2 := hhigh
      _ = ((Fintype.card F : ℝ) - 1) / (2 * Fintype.card F) := hg2

/-! ### Reformulations -/

/-- The proportion of rootless monic polynomials of degree `n ≥ 2` is at least `1 / 4`. -/
theorem card_no_root_univ_div_ge_quarter {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / 4 ≤
      (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℝ) /
        (Fintype.card F : ℝ) ^ n := by
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq2' : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq2
  refine le_trans ?_ (card_no_root_univ_div_bounds hn).1
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [hq2']

/-- The proportion of rootless monic polynomials of degree `n ≥ 2` is less than `1 / 2`. -/
theorem card_no_root_univ_div_lt_half {n : ℕ} (hn : 2 ≤ n) :
    (#{a : Fin n → F | ∀ r : F, ¬ (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).IsRoot r} : ℝ) /
        (Fintype.card F : ℝ) ^ n < 1 / 2 := by
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq2' : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq2
  refine lt_of_le_of_lt (card_no_root_univ_div_bounds hn).2 ?_
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hq2']

end Polynomial
