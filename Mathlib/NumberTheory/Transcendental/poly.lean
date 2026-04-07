-- A computational representation of Polynomials in one (anonymous) variable over a commutative ring R
-- Computational implies that need DecidableEq for R
-- Started by Mario Carniero at Hausdorff Institute June 2024
-- Representation is as a list of pairs (exponent, coefficient) in ℕ × R
-- Exponents in decreasing order, coefficients non-zero (so zero polynomial is empty list)
-- Note that Lean allows the ring with just 0 (so 1=0)
-- JHD: we may wish to rethink allowing this, as it causes extra checks
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic
--import Mathlib

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longFile 2000

@[ext] structure SparsePoly (R : Type) [CommRing R] : Type where
  coeffs : List (ℕ × R)
  sorted : coeffs.Pairwise (·.1 > ·.1)
  nonzero : ∀ x ∈ coeffs, x.2 ≠ 0

namespace SparsePoly
open Polynomial

variable {R}

instance [CommRing R] [Lean.ToFormat R] : Lean.ToFormat (SparsePoly R) where
  format x :=
    have := x.coeffs.foldl (init := none) fun (f : Option Lean.Format) (i, x) =>
      let monomial := if i = 0 then f!"({x})" else if i = 1 then f!"({x})*X" else f!"({x})*X^{i}"
      match f with
      | none => monomial
      | some f => f ++ " + " ++ monomial
    this.getD f!"0"

variable [CommRing R] [DecidableEq R]
def ofSortedList
    (coeffs : List (ℕ × R)) (sorted : coeffs.Pairwise (·.1 > ·.1)) :
    SparsePoly R where
  coeffs := coeffs.filter (·.2 ≠ 0)
  sorted := sorted.sublist (List.filter_sublist)
  nonzero := by simp [List.mem_filter]

theorem ofSortedList_of_nonzero {R : Type} [CommRing R] [DecidableEq R]
    (coeffs : List (ℕ × R)) (nonzero : ∀ x ∈ coeffs, x.2 ≠ 0) (sorted) :
    (ofSortedList coeffs sorted).coeffs = coeffs := by
  simp (config := {contextual := true}) [ofSortedList, nonzero]

instance : Zero (SparsePoly R) where
  zero := { coeffs := [], sorted := .nil, nonzero := nofun }

def C (r : R) : SparsePoly R := ofSortedList [(0, r)] (List.pairwise_singleton _ _)
-- Need the ofSortedList to deal with r=0

instance : One (SparsePoly R) where
  one := C 1

def degLt (a : ℕ) (l : List (ℕ × R)) : Prop := ∀ x ∈ l, x.1 < a

-- Relate our structures to the Polynomial of Mathlib
noncomputable def toPolyCore : List (ℕ × R) → R[X]
  | [] => 0
  | (i, a) :: x => Polynomial.C a * Polynomial.X^i + toPolyCore x

noncomputable def toPoly (x : SparsePoly R) : Polynomial R :=
  toPolyCore x.coeffs

def addCore : List (ℕ × R) → List (ℕ × R) → List (ℕ × R)
  | [], yy => yy
  | xx, [] => xx
  | xx@((i, a) :: x), yy@((j, b) :: y) =>
    if i < j then
      (j, b) :: addCore xx y
    else if j < i then
      (i, a) :: addCore x yy
    else  -- Check for a+b=0
      ( fun c => if c=0 then addCore x y else (i, c) :: addCore x y) (a+b)
    termination_by xx yy => xx.length + yy.length

theorem addCore_degLt {n : ℕ} : ∀ {x y : List (ℕ × R)},
    degLt n x → degLt n y → degLt n (addCore x y)
  | [], yy, _, hy => by
    unfold addCore
    exact hy
  | (i, a) :: x, [], hx, _ => by
    unfold addCore
    exact hx
  | xx@((i, a) :: x), yy@((j, b) :: y), hx, hy => by
    -- 1. Extract hypotheses for the heads and tails separately
    -- Lean 4's mem_cons_self uses implicit arguments, so no `_ _` is needed
    have hx_head : i < n := hx (i, a) List.mem_cons_self
    have hx_tail : degLt n x := fun e he => hx e (List.mem_cons_of_mem _ he)
    have hy_head : j < n := hy (j, b) List.mem_cons_self
    have hy_tail : degLt n y := fun e he => hy e (List.mem_cons_of_mem _ he)
    unfold addCore
    split
    · -- Case: i < j
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hy_head
      · exact addCore_degLt hx hy_tail e he
    · -- Case: ¬(i < j)
      split
      · -- Case: j < i
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hx_head
        · exact addCore_degLt hx_tail hy e he
      · -- Case: i = j
        dsimp only
        split
        · -- Case: a + b = 0
          exact addCore_degLt hx_tail hy_tail
        · -- Case: a + b ≠ 0
          intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hx_head
          · exact addCore_degLt hx_tail hy_tail e he
termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (ℕ × R)},
    x.Pairwise (·.1 > ·.1) → y.Pairwise (·.1 > ·.1) →
    (addCore x y).Pairwise (·.1 > ·.1)
  | [], yy, _, hy => by
    unfold addCore
    exact hy
  | (i, a) :: x, [], hx, _ => by
    unfold addCore
    exact hx
  | xx@((i, a) :: x), yy@((j, b) :: y), hx, hy => by
    -- FIX: Use List.pairwise_cons.1 to extract the head and tail proofs safely
    have ⟨hi, hx'⟩ := List.pairwise_cons.1 hx
    have ⟨hj, hy'⟩ := List.pairwise_cons.1 hy
    unfold addCore
    split
    · next ij => -- Case: i < j
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    · split
      · next ji => -- Case: j < i
        constructor
        · apply addCore_degLt
          · exact hi
          · intro
            | _, .head _ => exact ji
            | p, .tail _ hp => exact (hj _ hp).trans ji
        · exact addCore_sorted hx' hy
      · -- Case: i = j
        cases (by omega : i = j)
        -- dsimp is needed here to beta-reduce the (fun c => ...)(a+b)
        dsimp only
        split
        · -- Case: a + b = 0
          exact addCore_sorted hx' hy'
        · -- Case: a + b ≠ 0
          constructor
          · exact addCore_degLt hi hj
          · exact addCore_sorted hx' hy'
termination_by x y => x.length + y.length

instance : Add (SparsePoly R) where
  add x y :=
    let coeffs := addCore x.coeffs y.coeffs
    ofSortedList coeffs (addCore_sorted x.sorted y.sorted)

def dedupList : List (ℕ × R) → List (ℕ × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

-- Helper: Proves that deduplicating a list does not increase its maximum degree
lemma dedupList_degLt {n : ℕ} : ∀ (l : List (ℕ × R)),
    degLt n l → degLt n (dedupList l)
  | [] => fun h => by
    unfold dedupList
    exact h
  | [(i, a)] => fun h => by
    unfold dedupList
    exact h
  | (i, a) :: (j, b) :: xs => fun h => by
    unfold dedupList
    split
    · next heq => -- Case: i = j
      -- Recursively apply the lemma
      apply dedupList_degLt
      -- Now prove the un-deduplicated tail still respects degLt
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact h (i, a) List.mem_cons_self
      · exact h e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
    · next hneq => -- Case: i ≠ j
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact h (i, a) List.mem_cons_self
      · have h_tail : degLt n ((j, b) :: xs) := fun x hx => h x (List.mem_cons_of_mem _ hx)
        exact dedupList_degLt ((j, b) :: xs) h_tail e he
termination_by l => l.length

theorem dedupList_sorted : ∀ (coeffs : List (ℕ × R)),
    coeffs.Pairwise (·.1 ≥ ·.1) →
    (dedupList coeffs).Pairwise (·.1 > ·.1)
  | [] => fun _ => by
    unfold dedupList
    exact List.Pairwise.nil
  | [(i, a)] => fun _ => by
    unfold dedupList
    rw [List.pairwise_cons]
    constructor
    · intro e he
      contradiction -- A singleton has no tail elements, so this is vacuously true
    · exact List.Pairwise.nil
  | (i, a) :: (j, b) :: xs => fun h => by
    -- 1. Extract the proofs for the head and the tail separately
    have h_ij : i ≥ j := (List.pairwise_cons.1 h).1 (j, b) List.mem_cons_self
    have h_tail : ((j, b) :: xs).Pairwise (·.1 ≥ ·.1) := (List.pairwise_cons.1 h).2
    unfold dedupList
    split
    · next heq => -- Case: i = j
      apply dedupList_sorted
      rw [List.pairwise_cons]
      constructor
      · intro e he
        have h_je : j ≥ e.1 := (List.pairwise_cons.1 h_tail).1 e he
        omega -- i = j and j >= e.1 implies i >= e.1
      · exact (List.pairwise_cons.1 h_tail).2
    · next hneq => -- Case: i ≠ j
      have hij_strict : i > j := by omega
      rw [List.pairwise_cons]
      constructor
      · -- Here is where our helper lemma saves the day!
        apply dedupList_degLt
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hij_strict
        · have h_je : j ≥ e.1 := (List.pairwise_cons.1 h_tail).1 e he
          omega
      · exact dedupList_sorted ((j, b) :: xs) h_tail
termination_by coeffs => coeffs.length

def ofList (coeffs : List (ℕ × R)) : SparsePoly R :=
  let r : ℕ × R → ℕ × R → Bool := fun a b => decide (a.1 ≥ b.1)
  let coeffs' := coeffs.mergeSort r
  have h_trans : ∀ a b c, r a b = true → r b c = true → r a c = true := by
    intro a b c hab hbc
    simp only [r, decide_eq_true_eq] at *
    omega
  have h_total : ∀ a b, (r a b || r b a) = true := by
    intro a b
    simp only [r, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have h_sorted_bool : coeffs'.Pairwise (fun a b => r a b = true) :=
    List.pairwise_mergeSort h_trans h_total coeffs
  have h_sorted : coeffs'.Pairwise (·.1 ≥ ·.1) :=
    List.Pairwise.imp (fun h => of_decide_eq_true h) h_sorted_bool
  ofSortedList (dedupList coeffs')
    (dedupList_sorted coeffs' h_sorted)

def X : SparsePoly R := ofSortedList [(1, 1)] (List.pairwise_singleton _ _)

instance : Mul (SparsePoly R) where   -- James: I don't follow this
  mul x y :=
    ofList do
      let (i, a) ← x.coeffs
      let (j, b) ← y.coeffs
      return (i + j, a * b)

instance : Neg (SparsePoly R) where
  neg x := C (-1) * x

-- Helper Lemma: Filtering out zeros doesn't change the underlying polynomial.
-- Mathlib knows `C 0 * X^i = 0`, so this naturally collapses.
theorem toPolyCore_filter_nonzero (l : List (ℕ × R)) :
    toPolyCore (l.filter (·.2 ≠ 0)) = toPolyCore l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    simp only [List.filter_cons]
    split
    · next h_nonzero =>
      -- Case: a ≠ 0. The term is kept.
      unfold toPolyCore
      rw [ih]
    · next h_zero =>
      -- Case: a = 0. The term is dropped.
      unfold toPolyCore
      aesop

-- Lemma 1: addCore perfectly mirrors Polynomial addition
theorem toPolyCore_addCore : ∀ (x y : List (ℕ × R)),
    toPolyCore (addCore x y) = toPolyCore x + toPolyCore y
  | [], yy => by simp [addCore, toPolyCore]
  | (i, a) :: x, [] => by simp [addCore, toPolyCore]
  | xx@((i, a) :: x), yy@((j, b) :: y) => by
    unfold addCore
    split
    · next ij => -- Case: i < j
      -- 1. Unfold the outer layer of toPolyCore to expose the math
      dsimp only [toPolyCore]
      -- 2. Apply the recursive hypothesis
      rw [toPolyCore_addCore ((i, a) :: x) y]
      -- 3. The IH introduces `toPolyCore ((i, a) :: x)`. Unfold it again!
      dsimp only [toPolyCore]
      -- 4. Now ring can see all the additions and multiplications.
      ring
    · split
      · next ji => -- Case: j < i
        dsimp only [toPolyCore]
        rw [toPolyCore_addCore x ((j, b) :: y)]
        dsimp only [toPolyCore]
        ring
      · -- Case: i = j
        cases (by omega : i = j)
        dsimp only
        split
        · next hab => -- Case: a + b = 0
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore x y]
          -- Isolate the highest degree terms so we can cancel them
          have h_eq : Polynomial.C a * Polynomial.X ^ i + toPolyCore x +
            (Polynomial.C b * Polynomial.X ^ i + toPolyCore y) =
            (Polynomial.C a * Polynomial.X ^ i + Polynomial.C b * Polynomial.X ^ i) +
            (toPolyCore x + toPolyCore y) := by ring
          rw [h_eq]
          -- Prove that those specific terms cancel to 0 using a+b=0
          have h_zero : Polynomial.C a * Polynomial.X ^ i +
              Polynomial.C b * Polynomial.X ^ i = 0 := by
            rw [← add_mul, ← map_add, hab, map_zero, zero_mul]
          rw [h_zero, zero_add]
        · next hab => -- Case: a + b ≠ 0
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore x y]
          -- Expand C(a+b) into Ca + Cb, then distribute the X^i
          rw [map_add, add_mul]
          ring
termination_by x y => x.length + y.length

-- Lemma 2: SparsePoly addition mirrors Polynomial addition
theorem toPoly_add (x y : SparsePoly R) :
    toPoly (x + y) = toPoly x + toPoly y := by
  -- Use `change` to skip the Add typeclass and evaluate the struct directly
  change toPolyCore ((addCore x.coeffs y.coeffs).filter (·.2 ≠ 0)) = toPolyCore x.coeffs + toPolyCore y.coeffs
  -- The zeros filter drops out using our helper lemma
  rw [toPolyCore_filter_nonzero]
  -- We are left with exactly the addCore lemma we just proved!
  exact toPolyCore_addCore x.coeffs y.coeffs

-- Helper 1: Extract the `degLt` property from a `Sorted` list easily
lemma degLt_of_sorted_cons {i : ℕ} {a : R} {xs : List (ℕ × R)}
    (h : ((i, a) :: xs).Pairwise (·.1 > ·.1)) : degLt i xs :=
  fun x hx => (List.pairwise_cons.1 h).1 x hx

-- Helper 2: If all elements in a list have degree strictly less than `n`,
-- then evaluating the polynomial at degree `n` yields 0.
theorem coeff_toPolyCore_of_degLt {n : ℕ} (xs : List (ℕ × R)) (h : degLt n xs) :
    Polynomial.coeff (toPolyCore xs) n = 0 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [Polynomial.coeff_add]
    -- FIX: Removed `_ _` from List.mem_cons_self
    have h_deg : i < n := h (i, a) List.mem_cons_self
    have h_ne : i ≠ n := ne_of_lt h_deg
    rw [Polynomial.coeff_C_mul_X_pow]
    have h_tl : degLt n tl := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [ih h_tl, add_zero]
    grind

-- Helper 3: The coefficient of the head of the list at its own exponent `i` is exactly `a`.
theorem coeff_toPolyCore_head {i : ℕ} {a : R} (xs : List (ℕ × R)) (h : degLt i xs) :
    Polynomial.coeff (toPolyCore ((i, a) :: xs)) i = a := by
  dsimp only [toPolyCore]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  rw [coeff_toPolyCore_of_degLt xs h, add_zero]
-- The Main Boss Fight: Induction on both lists simultaneously


theorem toPolyCore_injective_of_sorted : ∀ (l1 l2 : List (ℕ × R)),
    l1.Pairwise (·.1 > ·.1) → l2.Pairwise (·.1 > ·.1) →
    (∀ x ∈ l1, x.2 ≠ 0) → (∀ x ∈ l2, x.2 ≠ 0) →
    toPolyCore l1 = toPolyCore l2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: ys, _, s2, _, nz2, heq => by
    have h_coeff : Polynomial.coeff (toPolyCore []) j = Polynomial.coeff (toPolyCore ((j, b) :: ys)) j := by rw [heq]
    -- FIX: Explicitly change the syntax to 0 so `rw` can see it
    change (0 : Polynomial R).coeff j = _ at h_coeff
    rw [Polynomial.coeff_zero] at h_coeff
    rw [coeff_toPolyCore_head ys (degLt_of_sorted_cons s2)] at h_coeff
    have hb_nz := nz2 (j, b) List.mem_cons_self
    exact False.elim (hb_nz h_coeff.symm)
  | (i, a) :: xs, [], s1, _, nz1, _, heq => by
    have h_coeff : Polynomial.coeff (toPolyCore ((i, a) :: xs)) i = Polynomial.coeff (toPolyCore []) i := by rw [heq]
    -- FIX: Explicitly change the syntax to 0 so `rw` can see it
    change _ = (0 : Polynomial R).coeff i at h_coeff
    rw [Polynomial.coeff_zero] at h_coeff
    rw [coeff_toPolyCore_head xs (degLt_of_sorted_cons s1)] at h_coeff
    have ha_nz := nz1 (i, a) List.mem_cons_self
    exact False.elim (ha_nz h_coeff)
  | (i, a) :: xs, (j, b) :: ys, s1, s2, nz1, nz2, heq => by
    have h_deg_x : degLt i xs := degLt_of_sorted_cons s1
    have h_deg_y : degLt j ys := degLt_of_sorted_cons s2
    obtain hij | rfl | hji := lt_trichotomy i j
    · have h_coeff : Polynomial.coeff (toPolyCore ((i, a) :: xs)) j = Polynomial.coeff (toPolyCore ((j, b) :: ys)) j := by rw [heq]
      rw [coeff_toPolyCore_head ys h_deg_y] at h_coeff
      have h_xs_j : degLt j xs := fun e he => lt_trans (h_deg_x e he) hij
      have h_lhs : Polynomial.coeff (toPolyCore ((i, a) :: xs)) j = 0 := by
        dsimp only [toPolyCore]
        rw [Polynomial.coeff_add]
        have hne : i ≠ j := ne_of_lt hij
        rw [Polynomial.coeff_C_mul_X_pow]
        rw [coeff_toPolyCore_of_degLt xs h_xs_j]
        grind
      rw [h_lhs] at h_coeff
      have hb_nz := nz2 (j, b) List.mem_cons_self
      exact False.elim (hb_nz h_coeff.symm)
    · have h_coeff : Polynomial.coeff (toPolyCore ((i, a) :: xs)) i = Polynomial.coeff (toPolyCore ((i, b) :: ys)) i := by rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x] at h_coeff
      rw [coeff_toPolyCore_head ys h_deg_y] at h_coeff
      subst h_coeff
      dsimp only [toPolyCore] at heq
      have heq_xs_ys : toPolyCore xs = toPolyCore ys := add_left_cancel heq
      have s1_xs : xs.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s1).2
      have s2_ys : ys.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s2).2
      have nz1_xs : ∀ x ∈ xs, x.2 ≠ 0 := fun e he => nz1 e (List.mem_cons_of_mem _ he)
      have nz2_ys : ∀ x ∈ ys, x.2 ≠ 0 := fun e he => nz2 e (List.mem_cons_of_mem _ he)
      rw [toPolyCore_injective_of_sorted xs ys s1_xs s2_ys nz1_xs nz2_ys heq_xs_ys]
    · have h_coeff : Polynomial.coeff (toPolyCore ((i, a) :: xs)) i = Polynomial.coeff (toPolyCore ((j, b) :: ys)) i := by rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x] at h_coeff
      have h_ys_i : degLt i ys := fun e he => lt_trans (h_deg_y e he) hji
      have h_rhs : Polynomial.coeff (toPolyCore ((j, b) :: ys)) i = 0 := by
        dsimp only [toPolyCore]
        rw [Polynomial.coeff_add]
        have hne : j ≠ i := ne_of_lt hji
        rw [Polynomial.coeff_C_mul_X_pow]
        rw [coeff_toPolyCore_of_degLt ys h_ys_i]
        grind
      rw [h_rhs] at h_coeff
      have ha_nz := nz1 (i, a) List.mem_cons_self
      exact False.elim (ha_nz h_coeff)

theorem toPoly_injective : Function.Injective (toPoly (R := R)) := by
  intro x y h
  ext1
  exact toPolyCore_injective_of_sorted x.coeffs y.coeffs x.sorted y.sorted x.nonzero y.nonzero h

-- Helper 4: toPoly of the zero SparsePoly is the zero Polynomial
theorem toPoly_zero : toPoly (0 : SparsePoly R) = 0 := rfl



-- Helper 5: toPoly of a constant SparsePoly is the constant Polynomial
theorem toPoly_C (r : R) : toPoly (C r) = Polynomial.C r := by
  unfold C toPoly ofSortedList
  dsimp only
  -- Branch depending on if the constant is 0 (filtered out) or non-zero (kept)
  by_cases hr : r = 0
  · simp [hr, toPolyCore]
  · simp [hr, toPolyCore]

-- ==========================================
-- PART 1: List Permutation Infrastructure
-- ==========================================

-- 1. Polynomials distribute cleanly over appended lists
theorem toPolyCore_append (l1 l2 : List (ℕ × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    calc
      toPolyCore ((i, a) :: tl ++ l2)
          = Polynomial.C a * Polynomial.X ^ i + toPolyCore (tl ++ l2) := by
              simp [List.cons_append, toPolyCore]
      _ = Polynomial.C a * Polynomial.X ^ i + (toPolyCore tl + toPolyCore l2) := by
            rw [ih]
      _ = toPolyCore ((i, a) :: tl) + toPolyCore l2 := by
            simp [toPolyCore, add_assoc]

-- 2. Sorting a list is just a permutation. Permuting a list doesn't change the polynomial!
theorem toPolyCore_perm {l1 l2 : List (ℕ × R)} (h : List.Perm l1 l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rcases x with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [ih]
  | swap x y l =>
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    dsimp only [toPolyCore]
    ring -- Algebraically, C a * X^i + C b * X^j = C b * X^j + C a * X^i
  | trans _ _ ih1 ih2 =>
    exact Eq.trans ih1 ih2

-- 3. mergeSort is a permutation, so it safely preserves the polynomial
theorem toPolyCore_mergeSort (l : List (ℕ × R)) (r : ℕ × R → ℕ × R → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l := by
  apply toPolyCore_perm
  exact List.mergeSort_perm l r


-- 4. Deduplicating adds coefficients of matching exponents, preserving the math
theorem toPolyCore_dedupList : ∀ (l : List (ℕ × R)),
    toPolyCore (dedupList l) = toPolyCore l
  | [] => by
    simp [dedupList, toPolyCore]
  | [(i, a)] => by
    simp [dedupList, toPolyCore]
  | (i, a) :: (j, b) :: xs => by
    unfold dedupList
    split
    · next heq => -- Case i = j
      subst heq
      rw [toPolyCore_dedupList ((i, a + b) :: xs)]
      dsimp only [toPolyCore]
      -- Expand C(a+b)*X^i into Ca*X^i + Cb*X^i
      rw [map_add, add_mul]
      ring
    · next hneq => -- Case i ≠ j
      dsimp only [toPolyCore]
      rw [toPolyCore_dedupList ((j, b) :: xs)]
      simp [toPolyCore]

theorem toPoly_ofList (l : List (ℕ × R)) :
    toPoly (ofList l) = toPolyCore l := by
  unfold toPoly ofList ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero]
  rw [toPolyCore_dedupList]
  rw [toPolyCore_mergeSort]

-- Helper for the inner loop of the List Monad multiplication
lemma toPolyCore_mul_y (i : ℕ) (a : R) (y : List (ℕ × R)) :
    toPolyCore (y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) =
      (Polynomial.C a * Polynomial.X ^ i) * toPolyCore y := by
  induction y with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    rcases hd with ⟨j, b⟩
    change toPolyCore ([(i + j, a * b)] ++ tl.flatMap _) = _
    rw [toPolyCore_append, ih]
    dsimp only [toPolyCore]
    have h_term : Polynomial.C (a * b) * Polynomial.X ^ (i + j) =
        Polynomial.C a * Polynomial.X ^ i * (Polynomial.C b * Polynomial.X ^ j) := by
      rw [map_mul, pow_add]
      ring
    rw [h_term]
    ring

-- Helper for the outer loop of the List Monad multiplication
lemma toPolyCore_mul_x (x y : List (ℕ × R)) :
    toPolyCore (x.flatMap fun ⟨i, a⟩ => y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) =
    toPolyCore x * toPolyCore y := by
  induction x with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    change toPolyCore ((y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) ++ tl.flatMap _) = _
    rw [toPolyCore_append, ih, toPolyCore_mul_y]
    dsimp only [toPolyCore]
    ring

-- ==========================================
-- PART 3: The Final Theorems!
-- ==========================================

theorem toPoly_one : toPoly (1 : SparsePoly R) = 1 := by
  change toPoly (C 1) = 1
  rw [toPoly_C]
  exact map_one (Polynomial.C (R := R))

theorem toPoly_mul (x y : SparsePoly R) : toPoly (x * y) = toPoly x * toPoly y := by
  -- Explicitly state the desugaring of the `do` block from your Mul instance
  have h_xy : x * y = ofList (x.coeffs.flatMap fun ⟨i, a⟩ =>
    y.coeffs.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) := rfl
  rw [h_xy, toPoly_ofList]
  exact toPolyCore_mul_x x.coeffs y.coeffs

theorem toPoly_neg (x : SparsePoly R) : toPoly (-x) = -toPoly x := by
  change toPoly (C (-1) * x) = -toPoly x
  rw [toPoly_mul, toPoly_C]
  simp

instance : CommRing (SparsePoly R) where
  add := (·+·)
  zero := 0
  mul := (·*·)
  one := 1
  neg := (-·)
  sub x y := x + -y
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec
  natCast n := C (n : R)
  intCast z := C (z : R)

  -- The core Ring axioms
  add_assoc := by
    intro x y z
    apply toPoly_injective
    rw [toPoly_add, toPoly_add, toPoly_add, toPoly_add]
    exact add_assoc (toPoly x) (toPoly y) (toPoly z)
  zero_add := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_zero, zero_add]

  add_zero := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_zero, add_zero]

  add_comm := by
    intro a b
    apply toPoly_injective
    rw [toPoly_add, toPoly_add, add_comm]

-- Inside your CommRing instance:
  neg_add_cancel := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_neg, toPoly_zero, neg_add_cancel]

  mul_assoc := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_mul, toPoly_mul, toPoly_mul, mul_assoc]

  one_mul := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_one, one_mul]

  mul_one := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_one, mul_one]

  left_distrib := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul, left_distrib]

  right_distrib := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul, right_distrib]

  zero_mul := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_zero, zero_mul]

  mul_zero := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_zero,  mul_zero]

  mul_comm := by
    intro a b
    apply toPoly_injective
    rw [toPoly_mul, toPoly_mul, mul_comm]

  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  natCast_zero := by
    apply toPoly_injective
    rw [toPoly_C, toPoly_zero]
    push_cast
    exact map_zero Polynomial.C

  natCast_succ := by
    intro n
    apply toPoly_injective
    show toPoly (C ((n + 1 : ℕ) : R)) = toPoly (C (n : R) + 1)
    rw [toPoly_C, toPoly_add, toPoly_C, toPoly_one]
    push_cast
    grind

  intCast_ofNat := by
    intro n
    apply toPoly_injective
    show toPoly (C ((Int.ofNat n : ℤ) : R)) = toPoly (C (n : R))
    rw [toPoly_C, toPoly_C]
    aesop

  intCast_negSucc := by
    intro n
    apply toPoly_injective
    show toPoly (C _) = toPoly (- C _)
    rw [toPoly_C, toPoly_neg, toPoly_C]
    push_cast
    grind

-- First, we bundle your `C` constructor into a formal RingHom
def C_hom : R →+* SparsePoly R where
  toFun := C
  map_zero' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_zero, map_zero]
  map_one' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_one, map_one]
  map_add' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_add, toPoly_C, map_add]
  map_mul' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_mul, toPoly_C, map_mul]

-- Now we define the Algebra using that RingHom
instance : Algebra R (SparsePoly R) where
  smul := fun a r => C a * r
  algebraMap := C_hom
  commutes' r p := mul_comm (C r) p
  smul_def' _ _ := rfl

class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

def degree (a : SparsePoly R) : ℕ := (a.coeffs.headD (0, 0)).1

-- ==========================================
-- 1. The Translation API (Bridges SparsePoly to Mathlib)
-- ==========================================
-- These 4 atomic facts tell Lean how your lists mathematically behave.
-- You can prove these later once you define SMul and Sub!

lemma degree_eq_head [CommRing R] (p : SparsePoly R) (i : ℕ) (x : R) (tail : List (ℕ × R))
    (h : p.coeffs = (i, x) :: tail) : p.degree = i := by
  rw [degree, h]
  simp

lemma natDegree_toPolyCore_lt [CommRing R] (i : ℕ) (x : R) (tail : List (ℕ × R))
  (h_sorted : ((i, x) :: tail).Pairwise (·.1 > ·.1)) :
  (toPolyCore tail).natDegree < i ∨ toPolyCore tail = 0 := by
  by_cases h0 : toPolyCore tail = 0
  · exact Or.inr h0
  ·
    by_contra hlt
    have hge : i ≤ (toPolyCore tail).natDegree := by {grind}
    have h_degLt_i : degLt i tail := by
      intro p hp
      exact (List.pairwise_cons.1 h_sorted).1 p hp
    have h_degLt_nd : degLt (toPolyCore tail).natDegree tail := by
      intro p hp
      exact lt_of_lt_of_le (h_degLt_i p hp) hge
    have hcoeff0 :
     (toPolyCore tail).coeff (toPolyCore tail).natDegree = 0 :=
     coeff_toPolyCore_of_degLt tail h_degLt_nd
    aesop

-- Bridge: degree of a SparsePoly agrees with natDegree of its translated Polynomial
lemma degree_eq_natDegree_toPoly [CommRing R] (p : SparsePoly R) :
    p.degree = (toPoly p).natDegree := by
  by_cases hnil : p.coeffs = []
  · simpa [degree, toPoly, toPolyCore, hnil]
  · rcases List.exists_cons_of_ne_nil hnil with ⟨hd, tl, hcoeffs⟩
    rcases hd with ⟨i, x⟩
    have hs : ((i, x) :: tl).Pairwise (·.1 > ·.1) := by simpa [hcoeffs] using p.sorted
    have hdegTl : degLt i tl := degLt_of_sorted_cons hs
    have hx0 : x ≠ 0 := by
     have := p.nonzero (i, x) (by simpa [hcoeffs])
     simpa using this

    have hcoeff_i : (toPoly p).coeff i = x := by
     rw [toPoly, hcoeffs]
     simpa using coeff_toPolyCore_head (i := i) (a := x) tl hdegTl

    have hcoeff_i_ne : (toPoly p).coeff i ≠ 0 := by simpa [hcoeff_i] using hx0

    have hpoly_ne : toPoly p ≠ 0 := by
     intro hz
     exact hcoeff_i_ne (by simpa [hz])

    have hupper : ∀ k > i, (toPoly p).coeff k = 0 := by
     intro k hk
     have hdegTl' : degLt k tl := fun e he => lt_trans (hdegTl e he) hk
     rw [toPoly, hcoeffs, toPolyCore, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
     have hik : i ≠ k := by grind
     simp [hik, coeff_toPolyCore_of_degLt tl hdegTl']
     grind

    have hle : i ≤ (toPoly p).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff_i_ne
    have hge : (toPoly p).natDegree ≤ i := by
     by_contra hgt
     have hi_lt : i < (toPoly p).natDegree := lt_of_not_ge hgt
     have hz : (toPoly p).coeff (toPoly p).natDegree = 0 := by grind
     specialize hupper (toPoly p).natDegree hi_lt
     aesop

    have hnat : (toPoly p).natDegree = i := le_antisymm hge hle
    calc
      p.degree = i := by simpa [degree, hcoeffs]
    _ = (toPoly p).natDegree := hnat.symm


-- The pseudo-division of 'a' annihilates the leading x*y*X^i term (when i > j)
lemma toPoly_pseudo_rem_a [CommRing R] (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
  (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hij : i > j) :
  (y • a - x • X^(i-j) * b).degree =
  (Polynomial.C y * toPolyCore as - Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs).natDegree := by

  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
   by_cases h1 : (1 : R) = 0
   · unfold X toPoly ofSortedList
     simp [toPolyCore, h1, Polynomial.X]
   · unfold X toPoly ofSortedList
     simp [toPolyCore, h1, Polynomial.X]

  have hpow : ∀ n : ℕ, toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
   intro n
   induction n with
  | zero => simp [toPoly_one]
  | succ n ih =>
    simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)

  have hsmul_a : toPoly (y • a) = Polynomial.C y * toPoly a := by
   change toPoly (C y * a) = _
   rw [toPoly_mul, toPoly_C]

  have hsmul_X : toPoly (x • (X : SparsePoly R)^(i - j)) = Polynomial.C x * Polynomial.X^(i - j) := by
   change toPoly (C x * (X : SparsePoly R)^(i - j)) = _
   rw [toPoly_mul, toPoly_C, hpow]

  have htoa : toPoly a = Polynomial.C x * Polynomial.X^i + toPolyCore as := by
   simpa [toPoly, toPolyCore, ha]
  have htob : toPoly b = Polynomial.C y * Polynomial.X^j + toPolyCore bs := by
   simpa [toPoly, toPolyCore, hb]

  have hcross :
    (Polynomial.C x * Polynomial.X^(i - j)) * (Polynomial.C y * Polynomial.X^j)
    = Polynomial.C y * (Polynomial.C x * Polynomial.X^i) := by
   have hsum : (i - j) + j = i := by omega
   have hpowX : (Polynomial.X : Polynomial R)^(i - j) * (Polynomial.X : Polynomial R)^j =
      (Polynomial.X : Polynomial R)^i := by
    rw [← pow_add, hsum]
   calc
    (Polynomial.C x * Polynomial.X^(i - j)) * (Polynomial.C y * Polynomial.X^j)
      = (Polynomial.C x * Polynomial.C y) * ((Polynomial.X : Polynomial R)^(i - j) * (Polynomial.X : Polynomial R)^j) := by ring
    _ = (Polynomial.C x * Polynomial.C y) * (Polynomial.X : Polynomial R)^i := by rw [hpowX]
    _ = Polynomial.C y * (Polynomial.C x * Polynomial.X^i) := by ring

  have hpoly :
    toPoly (y • a - x • X^(i-j) * b) =
    Polynomial.C y * toPolyCore as - Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs := by
   rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, hsmul_a, hsmul_X, htoa, htob]
   rw [mul_add, mul_add, hcross]
   ring

  calc
  (y • a - x • X^(i-j) * b).degree = (toPoly (y • a - x • X^(i-j) * b)).natDegree :=
    degree_eq_natDegree_toPoly _
  _ = (Polynomial.C y * toPolyCore as - Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs).natDegree := by
    rw [hpoly]


-- The pseudo-division of 'b' annihilates the leading x*y*X^j term (when ¬ i > j)
lemma toPoly_pseudo_rem_b [CommRing R] (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
  (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hji : ¬ (i > j)) :
  (x • b - y • X^(j-i) * a).degree =
  (Polynomial.C x * toPolyCore bs - Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as).natDegree := by

  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
   by_cases h1 : (1 : R) = 0
   · unfold X toPoly ofSortedList
     simp [toPolyCore, h1, Polynomial.X]
   · unfold X toPoly ofSortedList
     simp [toPolyCore, h1, Polynomial.X]

  have hpow : ∀ n : ℕ, toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
   intro n
   induction n with
   | zero => simp [toPoly_one]
   | succ n ih =>
    simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)

  have hsmul_b : toPoly (x • b) = Polynomial.C x * toPoly b := by
   change toPoly (C x * b) = _
   rw [toPoly_mul, toPoly_C]

  have hsmul_X : toPoly (y • (X : SparsePoly R)^(j - i)) = Polynomial.C y * Polynomial.X^(j - i) := by
   change toPoly (C y * (X : SparsePoly R)^(j - i)) = _
   rw [toPoly_mul, toPoly_C, hpow]

  have htoa : toPoly a = Polynomial.C x * Polynomial.X^i + toPolyCore as := by
   simpa [toPoly, toPolyCore, ha]
  have htob : toPoly b = Polynomial.C y * Polynomial.X^j + toPolyCore bs := by
   simpa [toPoly, toPolyCore, hb]

  have hcross :
    (Polynomial.C y * Polynomial.X^(j - i)) * (Polynomial.C x * Polynomial.X^i)
    = Polynomial.C x * (Polynomial.C y * Polynomial.X^j) := by
   have hle : i ≤ j := by omega
   have hsum : (j - i) + i = j := by omega
   have hpowX : (Polynomial.X : Polynomial R)^(j - i) * (Polynomial.X : Polynomial R)^i =
      (Polynomial.X : Polynomial R)^j := by
    rw [← pow_add, hsum]
   calc
    (Polynomial.C y * (Polynomial.X : Polynomial R)^(j - i)) *
        (Polynomial.C x * (Polynomial.X : Polynomial R)^i)
      = (Polynomial.C y * Polynomial.C x) *
          ((Polynomial.X : Polynomial R)^(j - i) * (Polynomial.X : Polynomial R)^i) := by ring
    _ = (Polynomial.C y * Polynomial.C x) * (Polynomial.X : Polynomial R)^j := by rw [hpowX]
    _ = Polynomial.C x * (Polynomial.C y * (Polynomial.X : Polynomial R)^j) := by ring

  have hpoly :
    toPoly (x • b - y • X^(j-i) * a) =
    Polynomial.C x * toPolyCore bs - Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as := by
   rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, hsmul_b, hsmul_X, htob, htoa]
   rw [mul_add, mul_add, hcross]
   ring

  calc
  (x • b - y • X^(j-i) * a).degree = (toPoly (x • b - y • X^(j-i) * a)).natDegree :=
    degree_eq_natDegree_toPoly _
  _ = (Polynomial.C x * toPolyCore bs - Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as).natDegree := by
    rw [hpoly]

-- Helper 1: Cross-multiplying and subtracting drops the degree of 'a'
lemma deg_pseudo_rem_a [CommRing R] (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hij : i > j) :
    (y • a - x • X^(i-j) * b).degree < a.degree := by
  rw [degree_eq_head a i x as ha]
  rw [toPoly_pseudo_rem_a a b i j x y as bs ha hb]

  -- 1. Create a helper containing your exact coefficient math!
  have h_coeff : ∀ k ≥ i, (Polynomial.C y * toPolyCore as - Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs).coeff k = 0 := by
    intro k hk

    have h_as_sorted : ((i, x) :: as).Pairwise (·.1 > ·.1) := by simpa [ha] using a.sorted
    have h_bs_sorted : ((j, y) :: bs).Pairwise (·.1 > ·.1) := by simpa [hb] using b.sorted

    have h_as_deg : (toPolyCore as).natDegree < i ∨ toPolyCore as = 0 := natDegree_toPolyCore_lt i x as h_as_sorted
    have h_bs_deg : (toPolyCore bs).natDegree < j ∨ toPolyCore bs = 0 := natDegree_toPolyCore_lt j y bs h_bs_sorted

    have h_as_coeff : (toPolyCore as).coeff k = 0 := by
      rcases h_as_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp

    have h_bs_coeff : (toPolyCore bs).coeff (k - (i - j)) = 0 := by
      rcases h_bs_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp

    have h_term1 : (Polynomial.C y * toPolyCore as).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, h_as_coeff, mul_zero]

    have h_term2 : (Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs).coeff k = 0 := by
      have h_reassoc : Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs = (Polynomial.C x * toPolyCore bs) * Polynomial.X ^ (i - j) := by ring
      rw [h_reassoc]
      have h_shift : (k - (i - j)) + (i - j) = k := by omega
      rw [← h_shift, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, h_bs_coeff, mul_zero]

    -- sub_zero added here to close the 0 - 0 = 0 gap!
    rw [Polynomial.coeff_sub, h_term1, h_term2, sub_zero]

  -- 2. Deduce that the natural degree must be strictly less than i using core axioms
  by_cases h_zero : (Polynomial.C y * toPolyCore as -
     Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs) = 0
  · rw [h_zero, Polynomial.natDegree_zero]
    omega
  · apply lt_of_not_ge
    intro h_ge
    -- 1. Grab the coefficient at exactly the natural degree
    have h_lead_zero := h_coeff _ h_ge
    -- 2. In Mathlib 4, coeff at natDegree is definitionally `leadingCoeff`.
    -- If `leadingCoeff = 0`, the entire polynomial must be exactly `0`.
    have h_contra := Polynomial.leadingCoeff_eq_zero.mp h_lead_zero
    -- 3. This directly contradicts our h_zero assumption!
    exact h_zero h_contra
  exact hij

-- Helper 2: Cross-multiplying and subtracting drops the degree of 'b'
lemma deg_pseudo_rem_b [CommRing R] (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hji : ¬(i > j)) (hj_pos : 0 < j) :
    (x • b - y • X^(j-i) * a).degree < b.degree := by
  rw [degree_eq_head b j y bs hb]
  rw [toPoly_pseudo_rem_b a b i j x y as bs ha hb]

  have h_coeff : ∀ k ≥ j, (Polynomial.C x * toPolyCore bs -
      Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as).coeff k = 0 := by
    intro k hk

    have h_as_sorted : ((i, x) :: as).Pairwise (·.1 > ·.1) := by simpa [ha] using a.sorted
    have h_bs_sorted : ((j, y) :: bs).Pairwise (·.1 > ·.1) := by simpa [hb] using b.sorted

    have h_as_deg : (toPolyCore as).natDegree < i ∨ toPolyCore as = 0 := natDegree_toPolyCore_lt i x as h_as_sorted
    have h_bs_deg : (toPolyCore bs).natDegree < j ∨ toPolyCore bs = 0 := natDegree_toPolyCore_lt j y bs h_bs_sorted

    have h_bs_coeff : (toPolyCore bs).coeff k = 0 := by
      rcases h_bs_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp

    have h_as_coeff : (toPolyCore as).coeff (k - (j - i)) = 0 := by
      rcases h_as_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp

    have h_term1 : (Polynomial.C x * toPolyCore bs).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, h_bs_coeff, mul_zero]

    have h_term2 : (Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as).coeff k = 0 := by
      have h_reassoc : Polynomial.C y * Polynomial.X ^ (j - i) *
        toPolyCore as = (Polynomial.C y * toPolyCore as) * Polynomial.X ^ (j - i) := by ring
      rw [h_reassoc]
      have h_shift : (k - (j - i)) + (j - i) = k := by omega
      rw [← h_shift, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, h_as_coeff, mul_zero]

    rw [Polynomial.coeff_sub, h_term1, h_term2, sub_zero]

  by_cases h_zero : (Polynomial.C x * toPolyCore bs - Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as) = 0
  · rw [h_zero, Polynomial.natDegree_zero]
    -- Just hand Lean the assumption directly!
    exact hj_pos
  · apply lt_of_not_ge
    intro h_ge
    have h_lead_zero := h_coeff _ h_ge
    have h_contra := Polynomial.leadingCoeff_eq_zero.mp h_lead_zero
    exact h_zero h_contra
  exact hji

def gcdPrim (a b : SparsePoly R) : SparsePoly R :=
  -- Bind the matches so Lean remembers them!
  match ha : a.coeffs with
  | [] => b
  | (i, x) :: as =>
    match hb : b.coeffs with
    | [] => a
    | (j, y) :: bs =>
      -- NEW: Intercept constants to prevent the infinite loop!
      if h_const : i = 0 ∧ j = 0 then
        a -- Base case: Both are constants. Stop the loop here.
      else if h_gt : i > j then
        gcdPrim (y • a - x • X^(i-j) * b) b
      else
        gcdPrim a (x • b - y • X^(j-i) * a)
termination_by a.degree + b.degree
decreasing_by
  · simp_wf
    have h_drop := deg_pseudo_rem_a a b i j x y as bs ha hb h_gt
    aesop
  · simp_wf
    -- Since ¬(i = 0 ∧ j = 0) and ¬(i > j), Lean logically deduces j MUST be > 0.
    have hj_pos : 0 < j := by omega

    -- 2. Apply our exact helper lemma for branch 2
    have h_drop := deg_pseudo_rem_b a b i j x y as bs ha hb h_gt hj_pos
    aesop

-- def gcdPrim (a b : SparsePoly R) : SparsePoly R :=
--   match a.coeffs with
--   | [] => b
--   | (i, x) :: as =>
--     match b.coeffs with
--     | [] => a
--     | (j, y) :: bs =>
--       if i > j then
--         gcdPrim (y • a - x • X^(i-j) * b) b
--       else
--         gcdPrim a (x • b - y • X^(j-i) * a)
-- termination_by a.degree + b.degree
-- decreasing_by
--   all_goals
--     simp_rw [degree, sub_eq_add_neg]
--     · sorry



-- Helper 1: The core property of foldl gcd
lemma foldl_gcd_dvd_acc [CommRing R] [GCDMonoid R] (l : List (ℕ × R)) (acc : R) :
    l.foldl (fun a x => gcd a x.2) acc ∣ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    -- foldl (...) (gcd acc hd.2) tl  ∣  gcd acc hd.2  ∣  acc
    exact (ih (gcd acc hd.2)).trans (gcd_dvd_left _ _)


-- Helper 2: foldl gcd also divides every element in the list
lemma foldl_gcd_dvd_mem [CommRing R] [GCDMonoid R] {l : List (ℕ × R)} {i : ℕ} {c : R}
    (h : (i, c) ∈ l) (acc : R) : l.foldl (fun a x => gcd a x.2) acc ∣ c := by
  induction l generalizing acc with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h_mem
    · -- Case: c is the current head
      -- foldl (...) (gcd acc c) tl  ∣  gcd acc c  ∣  c
      exact (foldl_gcd_dvd_acc tl (gcd acc c)).trans (gcd_dvd_right _ _)
    · -- Case: c is in the tail
      exact ih h_mem (gcd acc hd.2)

-- Note: I removed [CommMonoidWithZero R] to prevent the diamond error!
lemma content_dvd_coeff_final [CommRing R] [GCDMonoid R] {l : List (ℕ × R)} {i : ℕ} {c : R}
    (h : (i, c) ∈ l) : l.foldl (init := 0) (fun acc x => gcd acc x.2) ∣ c := by
  -- Just call our helper with acc := 0
  exact foldl_gcd_dvd_mem h 0

def content [CommRing R] [GCDMonoid R] (a : SparsePoly R) : R :=
  a.coeffs.foldl (init := 0) (gcd · ·.2)

def primitivePart [CommRing R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : SparsePoly R) : SparsePoly R where
  coeffs :=
    let b := a.content
    a.coeffs.map fun (i, a) => (i, a / b)
  sorted := by
    -- 1. Exponents (x.1) are unchanged by the map, so the strictly decreasing order holds.
    have h_sorted := a.sorted
    grind
  nonzero := by
    intro x hx
    -- 2. Extract the original coefficient 'c' and exponent 'i'
    simp only [List.mem_map, Prod.exists] at hx
    rcases hx with ⟨i, c, h_mem, rfl⟩
    -- Original coeff was non-zero by SparsePoly invariant
    have hc_nz := a.nonzero (i, c) h_mem
    let b := a.content
    intro h_div_zero
    -- 3. If c/b = 0, then b*(c/b) = 0
    have h_mul := congr_arg (fun (z : R) => b * z) h_div_zero
    simp only [mul_zero] at h_mul
    -- 4. Use our new lemma: the content (GCD) must divide the coefficient
    have h_dvd : b ∣ c := content_dvd_coeff_final h_mem
    -- 5. By IsExactDiv, b * (c / b) = c. This implies c = 0, a contradiction.
    rw [IsExactDiv.mul_div_cancel h_dvd] at h_mul
    exact hc_nz h_mul


nonrec def gcd [CommRing R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a b : SparsePoly R) : SparsePoly R :=
  gcd a.content b.content • (gcdPrim a b).primitivePart

instance : IsExactDiv ℤ where
  mul_div_cancel := Int.mul_ediv_cancel'

instance {R} [CommGroupWithZero R] : IsExactDiv R where
  mul_div_cancel h := by
    apply mul_div_cancel_of_imp'; rintro rfl
    simpa only [zero_dvd_iff] using h


/-- Helper: If all elements in the list have exponents strictly
  less than k, the coefficient at k is 0. -/
lemma coeff_toPolyCore_eq_zero_of_forall_lt [CommRing R] (l : List (ℕ × R)) (k : ℕ)
    (h : ∀ p ∈ l, p.1 < k) : (toPolyCore l).coeff k = 0 := by
  induction l with
  | nil =>
    -- Base case: empty list evaluates to 0.
    simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨j, y⟩
    -- 1. Evaluate the head: we know j < k because (j, y) is in the list
    have h_j_lt_k : j < k := by
      aesop
    have h_k_ne_j : k ≠ j := h_j_lt_k.ne'
    -- 2. Evaluate the tail using the inductive hypothesis
    have h_tail_zero : (toPolyCore tl).coeff k = 0 := by
      apply ih
      intro p hp
      apply h
      simp [hp] -- Let simp prove that if p ∈ tl, then p ∈ (j, y) :: tl
    -- 3. Crush the polynomial math directly by unfolding
    unfold toPolyCore
    -- simp will evaluate (C y * X^j).coeff k to 0 (since k ≠ j)
    -- and plug in the tail zero we just proved!
    simp [h_k_ne_j, h_tail_zero]


lemma degree_eq_poly_degree [CommRing R] (a : SparsePoly R) (h : a.coeffs ≠ []) :
    a.degree = (toPoly a).natDegree := by
  rcases h_coeffs : a.coeffs with _ | ⟨⟨i, x⟩, as⟩
  · contradiction

  have h_deg : a.degree = i := by simp [degree, h_coeffs]
  rw [h_deg]

  have h_as_lt : ∀ p ∈ as, p.1 < i := by
    intro p hp
    have h_sorted := a.sorted
    rw [h_coeffs] at h_sorted
    exact List.rel_of_pairwise_cons h_sorted hp

  -- Step 1: Unfold toPolyCore directly to expose the addition
  have h_coeff_i : (toPoly a).coeff i = x := by
    simp only [toPoly, h_coeffs]
    unfold toPolyCore
    have h_tail_zero : (toPolyCore as).coeff i = 0 := by
      apply coeff_toPolyCore_eq_zero_of_forall_lt
      exact h_as_lt
    simp [h_tail_zero]

  have h_nz : (toPoly a).coeff i ≠ 0 := by
    rw [h_coeff_i]
    exact a.nonzero (i, x) (by rw [h_coeffs]; simp)

  -- Step 2: Unfold toPolyCore for the upper bounds check
  have h_zero : ∀ k > i, (toPoly a).coeff k = 0 := by
    intro k hk
    simp only [toPoly, h_coeffs]
    unfold toPolyCore
    have h_k_ne_i : k ≠ i := hk.ne'
    have h_tail_zero : (toPolyCore as).coeff k = 0 := by
      apply coeff_toPolyCore_eq_zero_of_forall_lt
      intro p hp
      exact (h_as_lt p hp).trans hk
    simp [h_k_ne_i, h_tail_zero]

  -- Step 3: Mathlib limits (single, correct application)
  symm
  apply le_antisymm
  · by_contra h_gt
    push Not at h_gt
    have h_lead_zero := h_zero ((toPoly a).natDegree) h_gt
    have h_poly_zero : toPoly a = 0 := by
      apply Polynomial.leadingCoeff_eq_zero.mp
      exact h_lead_zero
    rw [h_poly_zero] at h_nz
    simp only [Polynomial.coeff_zero, ne_eq, not_true_eq_false] at h_nz

  · by_contra h_lt
    push Not at h_lt
    have h_coeff_i_zero := Polynomial.coeff_eq_zero_of_natDegree_lt h_lt
    exact h_nz h_coeff_i_zero

/-- Core Helper: Pushing scalar multiplication through the list translation -/
lemma toPolyCore_map_smul [CommRing R] (c : R) (l : List (ℕ × R)) :
    toPolyCore (l.map fun p => (p.1, c * p.2)) = Polynomial.C c * toPolyCore l := by
  induction l with
  | nil =>
    -- Base case: empty list
    unfold toPolyCore
    simp
  | cons hd tl ih =>
    rcases hd with ⟨i, x⟩
    -- 1. Evaluate the list mapping for the head
    simp only [List.map_cons]
    unfold toPolyCore
    -- 2. Substitute the tail using the inductive hypothesis
    rw [ih]
    -- 3. Distribute C c * (Head + Tail) -> C c * Head + C c * Tail
    rw [mul_add]
    -- 4. Polynomial.C is a Ring Homomorphism, so C(c * x) = C(c) * C(x)
    rw [map_mul]
    -- 5. Realign the commutative multiplication
    ring

def coeffCore : List (ℕ × R) → ℕ → R
  | [], _ => 0
  | (i, a) :: tl, n => if n = i then a else coeffCore tl n

def coeff (P : SparsePoly R) (n : ℕ) : R :=
  coeffCore P.coeffs n

/-- Core List Helper: Custom list search matches Mathlib Polynomial evaluation -/
lemma coeffCore_eq_toPolyCore_coeff [CommRing R] (l : List (ℕ × R)) (n : ℕ)
    (hsorted : l.Pairwise (·.1 > ·.1)) :
    coeffCore l n = (toPolyCore l).coeff n := by
  induction l generalizing n with
  | nil =>
    -- Base case: empty list evaluates to 0 in both definitions
    unfold coeffCore toPolyCore
    simp
  | cons hd tl ih =>
    rcases hd with ⟨i, x⟩

    have hhead : ∀ p ∈ tl, i > p.1 := (List.pairwise_cons.1 hsorted).1
    have htail : tl.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 hsorted).2

    -- 1. Unfold both definitions for the head of the list
    unfold coeffCore toPolyCore

    -- 2. Push Mathlib's coefficient evaluation through the addition
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]

    -- 3. Handle the if/else logic (if n = i)
    by_cases h_eq : n = i
    · have hdeg : degLt n tl := fun p hp => by grind
      have h_tail_zero : (toPolyCore tl).coeff n = 0 := coeff_toPolyCore_of_degLt tl hdeg
      simp [h_eq, h_tail_zero]
      grind
    · have ih' : coeffCore tl n = (toPolyCore tl).coeff n := ih n htail
      simp [h_eq, ih']

/-- The Main Bridge Lemma -/
lemma coeff_toPoly [CommRing R] (P : SparsePoly R) (n : ℕ) :
    P.coeff n = (toPoly P).coeff n := by
  -- 1. Unfold your SparsePoly wrapper
  -- rw [SparsePoly.coeff_def, toPoly]

  -- 2. Apply the core list helper
  exact coeffCore_eq_toPolyCore_coeff P.coeffs n P.sorted

lemma toPoly_smul [CommRing R] (c : R) (P : SparsePoly R) :
    toPoly (c • P) = Polynomial.C c * toPoly P := by
  change toPoly (C c * P) = Polynomial.C c * toPoly P
  rw [toPoly_mul, toPoly_C]

/-- How scalar multiplication affects the translated polynomial's coefficients -/
lemma coeff_smul [CommRing R] (c : R) (P : SparsePoly R) (n : ℕ) :
    (toPoly (c • P)).coeff n = c * (toPoly P).coeff n := by
  change (toPoly (C c * P)).coeff n = c * (toPoly P).coeff n
  rw [toPoly_mul, toPoly_C, Polynomial.coeff_C_mul]

lemma toPoly_smul_X_pow_mul [CommRing R] (c : R) (n : ℕ) (Q : SparsePoly R) :
    toPoly ((c • X^n) * Q) = Polynomial.C c * Polynomial.X^n * toPoly Q := by
  rw [toPoly_mul, toPoly_smul]
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0
    · unfold X toPoly ofSortedList
      simp [toPolyCore, Polynomial.X, h1]
    · unfold X toPoly ofSortedList
      simp [toPolyCore, Polynomial.X, h1]
  have hpow : toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    induction n with
    | zero =>
      simpa [pow_zero, toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using
        (toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R))
  rw [hpow]
  -- to the target (Polynomial.C c * Polynomial.X^n * toPoly Q), so we are done!

/-- Bridge: Translates a SparsePoly monomial into a Mathlib Polynomial -/
lemma toPoly_smul_X_pow [CommRing R] (c : R) (n : ℕ) :
    toPoly (c • X^n) = Polynomial.C c * Polynomial.X^n := by
  calc
    toPoly (c • X^n) = toPoly ((c • X^n) * (1 : SparsePoly R)) := by simp
    _ = Polynomial.C c * Polynomial.X^n * toPoly (1 : SparsePoly R) :=
      toPoly_smul_X_pow_mul (R := R) c n (1 : SparsePoly R)
    _ = Polynomial.C c * Polynomial.X^n := by simp [toPoly_one]


-- Helper 2: Subtracting the leading term reduces the degree
lemma degree_sub_leading_term_lt [CommRing R] [Div R] [DecidableEq R]
    (P Q : SparsePoly R) {i j : ℕ} {x y : R} {as bs : List (ℕ × R)}
    (ha : P.coeffs = (i, x) :: as)
    (hb : Q.coeffs = (j, y) :: bs)
    (h_deg : j ≤ i) (h_div : y * (x / y) = x) (h_pos : 0 < i) :
    degree (P - ((x / y) • X^(i - j)) * Q) < i := by

  -- Explicitly unfold the degree definition for the empty list to guarantee h_pos application
  by_cases h_empty : (P - ((x / y) • X^(i - j)) * Q).coeffs = []
  · unfold degree
    rw [h_empty]
    grind

  rw [degree_eq_poly_degree _ h_empty]

  by_contra h_ge
  push Not at h_ge

  have h_coeff_zero : ∀ k ≥ i, (toPoly (P - ((x / y) • X^(i - j)) * Q)).coeff k = 0 := by
    intro k hk

    -- Bypass the missing toPoly_sub by converting subtraction to addition of a negative
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg]
    rw [toPoly_mul, toPoly_smul_X_pow]

    simp only [Polynomial.coeff_add, Polynomial.coeff_neg]

    have hP_deg : P.degree = i := by simp [degree, ha]
    have hQ_deg : Q.degree = j := by simp [degree, hb]
    have hP_nz : P.coeffs ≠ [] := by rw [ha];grind
    have hQ_nz : Q.coeffs ≠ [] := by rw [hb]; grind

    rcases eq_or_lt_of_le hk with rfl | h_gt
    · -- Case k = i: Exact Cancellation
      have hP_lead : (toPoly P).coeff i = x := by
        simp only [toPoly, ha]
        unfold toPolyCore
        have h_as_lt : ∀ p ∈ as, p.1 < i := by
          intro p hp; have hs := P.sorted; rw [ha] at hs; exact List.rel_of_pairwise_cons hs hp
        have h_tail_zero : (toPolyCore as).coeff i = 0 := by
          apply coeff_toPolyCore_eq_zero_of_forall_lt; exact h_as_lt
        simp [h_tail_zero]

      have hQ_lead : (Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q).coeff i = x := by
        have h_rearrange : Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q =
                           (Polynomial.C (x / y) * toPoly Q) * Polynomial.X ^ (i - j) := by ring
        rw [h_rearrange]

        -- EXPLICIT SHIFT: Split 'i' into 'j + (i - j)' so the lemma matches
        have h_shift : j + (i - j) = i := by omega
        have h_coeff_mul_X_pow :
            (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff i =
              (Polynomial.C (x / y) * toPoly Q).coeff j := by
          calc
            (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff i
                = (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff (j + (i - j)) := by
                    simpa [h_shift]
            _ = (Polynomial.C (x / y) * toPoly Q).coeff j := by
                  simpa using
                    (Polynomial.coeff_mul_X_pow
                      (p := Polynomial.C (x / y) * toPoly Q)
                      (d := j) (n := i - j))
        rw [h_coeff_mul_X_pow]

        have hQ_j : (toPoly Q).coeff j = y := by
          simp only [toPoly, hb]
          unfold toPolyCore
          have h_bs_lt : ∀ p ∈ bs, p.1 < j := by
            intro p hp; have hs := Q.sorted; rw [hb] at hs; exact List.rel_of_pairwise_cons hs hp
          have h_tail_zero : (toPolyCore bs).coeff j = 0 := by
            apply coeff_toPolyCore_eq_zero_of_forall_lt; exact h_bs_lt
          simp [h_tail_zero]
        grind
      grind
    · -- Case k > i: Upper Bounds
      have hP_zero : (toPoly P).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [← degree_eq_poly_degree P hP_nz, hP_deg]
        exact h_gt

      have hQ_zero : (Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q).coeff k = 0 := by
        have h_rearrange : Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q =
                           (Polynomial.C (x / y) * toPoly Q) * Polynomial.X ^ (i - j) := by ring
        rw [h_rearrange]

        -- EXPLICIT SHIFT: Split 'k' into '(k - (i - j)) + (i - j)'
        have h_shift_k : (k - (i - j)) + (i - j) = k := by omega

        -- Push coefficient check through X^pow and then through the Constant C
        rw [← h_shift_k, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul]

        -- Isolate Q and prove its coefficient is 0
        have hQ_coeff_zero : (toPoly Q).coeff (k - (i - j)) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [← degree_eq_poly_degree Q hQ_nz, hQ_deg]
          omega

        -- (x / y) * 0 = 0
        rw [hQ_coeff_zero, mul_zero]

      rw [hP_zero, hQ_zero, neg_zero, add_zero]

  -- 5. The Final Contradiction
  have h_lead_zero := h_coeff_zero ((toPoly (P - ((x / y) • X^(i - j)) * Q)).natDegree) h_ge
  have h_poly_zero : toPoly (P - ((x / y) • X^(i - j)) * Q) = 0 :=
    Polynomial.leadingCoeff_eq_zero.mp h_lead_zero
  have h_deg_zero : (toPoly (P - ((x / y) • X^(i - j)) * Q)).natDegree = 0 :=
    by rw [h_poly_zero, Polynomial.natDegree_zero]

  rw [h_deg_zero] at h_ge
  exact (not_lt_of_ge h_ge h_pos).elim

-- divRem a b = (q, r) -> a = b * q + r
def divRem [Div R] (a b : SparsePoly R) : SparsePoly R × SparsePoly R :=
  -- Bind the variables so Lean remembers them!
  match ha : a.coeffs, hb : b.coeffs with
  | (i, x) :: as, (j, y) :: bs =>
    if h_lt : i < j then
      (0, a)
    else
      -- Intercept i = 0 so we don't trigger the 0 < 0 loop
      if h_pos : i = 0 then
        let c := (x / y) • X^0
        if y * (x / y) = x then
          (c, a - c * b)
        else
          (0, a)
      else
        let c := (x / y) • X^(i - j)
        if h_div : y * (x / y) = x then
          -- Inline the c variable in the recursive call
          let (q', r') := divRem (a - ((x / y) • X^(i - j)) * b) b
          (q' + c, r')
        else
          (0, a)
  | _, _ => (0, a)
termination_by if a.coeffs = [] then 0 else a.degree + 1
decreasing_by
  simp_wf
  have hj_le_i : j ≤ i := by omega
  have h_pos_i : 0 < i := by omega

  have ha_not_empty : a.coeffs ≠ [] := by rw [ha]; simp
  have h_deg : a.degree = i := by unfold degree; rw [ha]; rfl

  rw [if_neg ha_not_empty, h_deg]

  by_cases h_empty : (a - ((x / y) • X^(i - j)) * b).coeffs = []
  · aesop--rw [if_pos h_empty]; omega
  · have h_lt_i := degree_sub_leading_term_lt a b ha hb hj_le_i h_div h_pos_i
    aesop

instance [Div R] : Div (SparsePoly R) where
  div a b := (divRem a b).1


/-- Unfolding lemma to safely evaluate divRem without projection motive errors -/
lemma divRem_eq [Div R] (a b : SparsePoly R) :
    divRem a b =
      match ha : a.coeffs, hb : b.coeffs with
      | (i, x) :: as, (j, y) :: bs =>
        if h_lt : i < j then
          (0, a)
        else
          if h_pos : i = 0 then
            let c := (x / y) • X^0
            if y * (x / y) = x then
              (c, a - c * b)
            else
              (0, a)
          else
            let c := (x / y) • X^(i - j)
            if h_div : y * (x / y) = x then
              let (q', r') := divRem (a - ((x / y) • X^(i - j)) * b) b
              (q' + c, r')
            else
              (0, a)
      | _, _ => (0, a) := by
  -- Lean safely unfolds this because there are no `.1` or `.2` projections!
  rw [divRem]

-- Helper 1: The Division Algorithm Specification
-- States that `divRem a b = (q, r)` always satisfies `b * q + r = a`
lemma divRem_spec [CommRing R] [Div R] (a b : SparsePoly R) :
    b * (divRem a b).1 + (divRem a b).2 = a := by
  -- Target 'a' for induction, 'b' is fixed
  induction a using divRem.induct
  case b => exact b

  -- We explicitly name ALL auto-generated variables exactly as they appear in the induction motive
  case case1 a i x as j y bs ha hb h_lt =>
    -- Rewriting ha and hb forces the match to see the concrete lists
    rw [divRem_eq, ha, hb]
    -- Simp now perfectly evaluates the `if` using the h_lt hypothesis
    simp [h_lt]

  case case2 a i x as j y bs ha hb h_nlt h_pos h_div =>
    rw [divRem_eq, hb]
    simp [h_nlt, h_pos, h_div]
    aesop
    --grind

  case case3 a i x as j y bs ha hb h_nlt h_pos h_ndiv =>
    rw [divRem_eq, hb]
    simp [h_nlt, h_pos, h_ndiv]
    grind

  case case4 a i x as j y bs ha hb h_nlt h_npos h_div q' r' heq ih =>
    rw [divRem_eq, ha, hb]
    -- By feeding simp the exact boolean branches and the recursive equality (heq),
    -- it utterly crushes the match and tuple projections into pure algebra!
    simp [h_nlt, h_npos, h_div, heq]

    have h_rearrange : ∀ (q r c : SparsePoly R),
      b * (q + c) + r = (b * q + r) + b * c := by intros; grind

    -- Execute the algebra pipeline
    rw [h_rearrange]
    simp_all only [not_lt, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    grind

  case case5 a i x as j y bs ha hb h_nlt h_npos h_ndiv =>
    rw [divRem_eq, ha, hb]
    simp [h_nlt, h_npos, h_ndiv]

  -- We leave case6 (fallback) unnamed to avoid arity mismatch on empty lists
  case case6 =>
    rw [divRem_eq]
    split <;> grind


-- -- Bridge: SparsePoly subtraction mirrors Polynomial subtraction
-- theorem toPoly_sub [CommRing R] (x y : SparsePoly R) :
--     toPoly (x - y) = toPoly x - toPoly y := by
--   -- 1. Unfold SparsePoly subtraction into addition of a negative
--   rw [sub_eq_add_neg]

--   -- 2. Push the translation through the addition and negation
--   rw [toPoly_add, toPoly_neg]

--   -- 3. Collapse the Mathlib polynomial addition and negation back into subtraction
--   rw [← sub_eq_add_neg]

-- -- Helper 1: The Remainder Degree Bound (Mathematically True over a Field!)
-- lemma degree_rem_lt [CommRing R] [Div R] [DecidableEq R] (a b : SparsePoly R) (hb_nz : b.coeffs ≠ []) :
--     (divRem a b).2.coeffs = [] ∨ (divRem a b).2.degree < b.degree := by
--   induction a using divRem.induct
--   case b => exact b

--   -- CASE 1: i < j (a's degree is strictly less than b's)
--   case case1 a i x as j y bs ha hb h_lt =>
--     rw [divRem_eq, ha, hb]
--     simp only [h_lt, ↓reduceIte, Prod.snd]
--     right
--     have h_deg_a : a.degree = i := degree_eq_head a i x as ha
--     have h_deg_b : b.degree = j := degree_eq_head b j y bs hb
--     grind

--   -- CASE 2: i = 0, Exact Division (Constants)
--   case case2 a i x as j y bs ha hb h_nlt h_pos h_div =>
--     rw [divRem_eq, hb]
--     simp only [h_nlt, h_pos, h_div, ↓reduceIte, Prod.snd]
--     left

--     -- 1. Exponents are natural numbers, so `¬ 0 < y` means `y = 0`.
--     have hy_zero : y = 0 := Nat.eq_zero_of_not_pos h_div
--     have hj_empty : j = [] := by
--       cases j with
--       | nil => rfl
--       | cons hd tl =>
--         have hs := x.sorted
--         rw [h_pos] at hs
--         have hlt : 0 > hd.1 := by
--           simpa using (List.rel_of_pairwise_cons hs (List.mem_cons_self : hd ∈ hd :: tl))
--         exact (Nat.not_lt_zero _ hlt).elim
--     have hha_empty : ha = [] := by
--       cases ha with
--       | nil => rfl
--       | cons hd tl =>
--         have hs := b.sorted
--         rw [hb] at hs
--         have hlt : y > hd.1 := List.rel_of_pairwise_cons hs (List.mem_cons_self : hd ∈ hd :: tl)
--         have hlt0 : 0 > hd.1 := by simpa [hy_zero] using hlt
--         exact (Nat.not_lt_zero _ hlt0).elim

--     -- 2. Bypass lists entirely! Map subtraction to Mathlib using toPoly_injective
--     have h_rem_zero : x - ((as / bs) • X ^ 0) * b = 0 := by
--       apply toPoly_injective
--       rw [toPoly_zero, toPoly_sub, toPoly_mul, toPoly_smul_X_pow]

--       -- Convert x and b into Mathlib constants
--       have h_toPoly_x : toPoly x = Polynomial.C as := by
--         simp [toPoly, h_pos, hj_empty, toPolyCore]
--       have h_toPoly_b : toPoly b = Polynomial.C bs := by
--         simp [toPoly, hb, hy_zero, hha_empty, toPolyCore]

--       rw [h_toPoly_x, h_toPoly_b]
--       simp only [pow_zero, mul_one]

--       -- Algebra: C(as/bs) * C(bs) = C((as/bs)*bs) = C(as). Therefore C(as) - C(as) = 0.
--       have h_mul : (as / bs) * bs = as := by simpa [mul_comm] using h_nlt
--       rw [← map_mul, h_mul, sub_self]

--     -- 3. A zero polynomial definitionally has an empty list of coefficients!
--     simp
--     aesop
--     -- rw [h_rem_zero]
--     -- rfl

--   -- CASE 3: i = 0, Inexact Division Abort (IMPOSSIBLE OVER A FIELD)
--   case case3 a i x as j y bs ha hb h_nlt h_pos h_ndiv =>
--     rw [divRem_eq, hb]
--     -- In this branch, `hb : b.coeffs = (y, bs) :: ha`, so `bs` is the leading coefficient.
--     have hbs_nz : bs ≠ 0 := b.nonzero (y, bs) (by simpa [hb])
--     have h_div_true : bs * (as / bs) = as := by
--       rw [mul_comm]
--       sorry
--     exact (h_nlt h_div_true).elim

--   -- CASE 4: i ≠ 0, Exact Division (The Recursive Step)
--   case case4 a i x as j y bs ha hb h_nlt h_npos h_div q' r' heq ih =>
--     rw [divRem_eq, ha, hb]
--     simp only [h_nlt, h_npos, h_div, heq, ↓reduceIte, Prod.snd]
--     aesop

--   -- CASE 5: i ≠ 0, Inexact Division Abort (IMPOSSIBLE OVER A FIELD)
--   case case5 a i x as j y bs ha hb h_nlt h_npos h_ndiv =>
--     rw [divRem_eq, ha, hb]
--     -- Exact same Field contradiction as Case 3
--     have hmem : (j, y) ∈ b.coeffs := by
--       simpa [hb] using (List.mem_cons_self (a := (j, y)) (l := bs))
--     have hy_nz : y ≠ 0 := b.nonzero (j, y) hmem
--     have h_div_true : y * (x / y) = x := by
--       sorry
--     exact (h_ndiv h_div_true).elim

--   -- CASE 6: Fallback (Empty Lists)
--   case case6 a h_no_cons =>
--     rw [divRem_eq]
--     cases ha_list : a.coeffs <;> cases hb_list : b.coeffs
--     · exact False.elim (hb_nz hb_list)
--     · simp [ha_list, hb_list]
--     · exact False.elim (hb_nz hb_list)
--     · exfalso
--       exact h_no_cons _ _ _ _ _ _ ha_list hb_list


-- Helper 2: Degree of Multiplication
-- Mathematically requires [IsDomain R] so zero-divisors don't wipe out the leading term!
lemma degree_mul [CommRing R] [IsDomain R] (a b : SparsePoly R)
    (ha : a.coeffs ≠ []) (hb : b.coeffs ≠ []) : (a * b).degree = a.degree + b.degree := by
  -- 1. Bridge your SparsePoly degrees to Mathlib's natDegree
  rw [degree_eq_natDegree_toPoly (a * b)]
  rw [degree_eq_natDegree_toPoly a]
  rw [degree_eq_natDegree_toPoly b]

  -- 2. Push multiplication through the translation layer
  rw [toPoly_mul]

  -- 3. Prove that the translated polynomials are not zero
  have h_ta_ne_zero : toPoly a ≠ 0 := by
    intro h
    -- If toPoly a = 0, injectivity means a = 0, which means empty lists!
    have ha_zero : a = 0 := toPoly_injective (by rw [h, toPoly_zero])
    have h_empty : a.coeffs = [] := by rw [ha_zero]; rfl
    exact ha h_empty

  have h_tb_ne_zero : toPoly b ≠ 0 := by
    intro h
    have hb_zero : b = 0 := toPoly_injective (by rw [h, toPoly_zero])
    have h_empty : b.coeffs = [] := by rw [hb_zero]; rfl
    exact hb h_empty

  -- 4. Apply Mathlib's heavy-duty theorem for Integral Domains!
  exact Polynomial.natDegree_mul h_ta_ne_zero h_tb_ne_zero

-- -- Helper 3: Uniqueness of Remainder
-- lemma divRem_rem_zero [CommRing R] [IsDomain R]
--   [Div R] [DecidableEq R] {a b : SparsePoly R} (h : b ∣ a) :
--     (divRem a b).2 = 0 := by
--   -- 1. `h` means `∃ c, a = c * b` (Mathlib's standard definition of divides)
--   rcases h with ⟨c, hc⟩

--   -- Edge Case: If b is 0, then a must be 0, and the remainder is 0.
--   by_cases hb_empty : b.coeffs = []
--   · have hb0 : b = 0 := by ext1; exact hb_empty
--     have ha0 : a = 0 := by rw [hc, hb0, zero_mul]
--     rw [divRem_eq, hb_empty]
--     simp [ha0]

--   -- 2. We know `b * q + r = a` from our `divRem_spec`.
--   let q := (divRem a b).1
--   let r := (divRem a b).2
--   have h_spec : b * q + r = a := divRem_spec a b

--   -- 3. Rearrange: r = a - b * q = b * c - b * q = b * (c - q).
--   have h_r_eq : r = b * (c - q) := by
--     have h_eq_poly : b.toPoly * q.toPoly + r.toPoly = b.toPoly * c.toPoly := by
--       have h_eq : b * q + r = b * c := by
--         grind
--       simpa [toPoly_add, toPoly_mul, add_comm, add_left_comm, add_assoc] using congrArg toPoly h_eq

--     have h_sub : b.toPoly * c.toPoly - b.toPoly * q.toPoly = r.toPoly := by
--       rw [sub_eq_iff_eq_add]
--       grind

--     apply toPoly_injective
--     calc
--       r.toPoly = b.toPoly * c.toPoly - b.toPoly * q.toPoly := by
--         exact h_sub.symm
--       _ = b.toPoly * (c.toPoly - q.toPoly) := by
--         ring
--       _ = (b * (c - q)).toPoly := by
--         simp [toPoly_mul, toPoly_sub]

--   -- 4. Check if (c - q) is zero.
--   by_cases h_cq : c - q = 0
--   · -- If c - q = 0, then r = b * 0 = 0.
--     rw [h_cq, mul_zero] at h_r_eq
--     exact h_r_eq

--   · -- 5. If c - q ≠ 0, we find a contradiction in the degrees.
--     have h_cq_nz : (c - q).coeffs ≠ [] := by
--       intro h; exact h_cq (by ext1; exact h)

--     -- From Helper 2: deg(r) = deg(b) + deg(c - q)
--     have h_deg_r : r.degree = b.degree + (c - q).degree := by
--       rw [h_r_eq, degree_mul b (c - q) hb_empty h_cq_nz]

--     -- From Helper 1: r = 0 OR deg(r) < deg(b)
--     have h_bound := degree_rem_lt a b hb_empty
--     rcases h_bound with h_r_empty | h_r_lt
--     · -- Subcase: r.coeffs = [] implies r = 0.
--       ext1; exact h_r_empty
--     · -- Subcase: deg(r) < deg(b).
--       -- But we proved deg(r) = deg(b) + deg(c-q), which is ≥ deg(b).
--       -- Contradiction!
--       have h_ge : b.degree ≤ r.degree := by rw [h_deg_r]; omega
--       exact (not_lt_of_ge h_ge h_r_lt).elim

-- instance [CommRing R] [Div R] [DecidableEq R] [IsDomain R] : IsExactDiv (SparsePoly R) where
--   mul_div_cancel {a b} h := by
--     -- 1. Get the foundational equation: b * q + r = a
--     have h_spec := divRem_spec a b

--     -- 2. Apply our hard-won uniqueness theorem to prove r = 0
--     have h_rem : (divRem a b).2 = 0 := divRem_rem_zero h

--     -- 3. Substitute r = 0 into the equation
--     rw [h_rem, add_zero] at h_spec

--     -- We are left with exactly b * (a / b) = a
--     exact h_spec

instance : DecidableEq (SparsePoly R) := fun a b =>
  decidable_of_iff' (a.coeffs = b.coeffs) (SparsePoly.ext_iff ..)

#eval (X * (C X * X + C (X + 2) : SparsePoly (SparsePoly ℤ))) / X

-- Bridge: The sparse variable X translates to the Mathlib variable X
theorem toPoly_X_fixed : toPoly (X : SparsePoly R) = Polynomial.X := by
  unfold X toPoly ofSortedList
  dsimp only
  by_cases h1 : (1 : R) = 0
  · simp [h1, toPolyCore]
    aesop
  · simp [h1, toPolyCore]

-- Bridge: Powers of X translate correctly
theorem toPoly_pow (n : ℕ) : toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
  induction n with
  | zero => simp [toPoly_one]
  | succ n ih => simp [pow_succ, toPoly_mul, toPoly_X_fixed, ih]

-- Helper: The inverse function (eval₂ at X) preserves the polynomial structure
lemma toPoly_ofPoly (p : Polynomial R) :
    toPoly (p.eval₂ (algebraMap R (SparsePoly R)) X) = p := by
  induction p using Polynomial.induction_on with
  | C r =>
    -- algebraMap is defined as C_hom, which uses our C function
    simp only [eval₂_C]
    --grind -- algebraMap R (SparsePoly R) is defined as the constructor C

--change toPoly (C r) = Polynomial.C r

    simpa using toPoly_C (R := R) r
  | add =>
    simp only [eval₂_add, toPoly_add]
    grind
  | monomial n r ih =>
    -- This handles the r * X^n logic
    simp
    simp only [eval₂_monomial, toPoly_mul, toPoly_pow]
    -- Now we have: toPoly (C r) * X^n = Polynomial.C r * X^n
    rw [← toPoly_C]
    -- Both sides are now Polynomial.C r * Polynomial.X ^ n
    rfl

noncomputable def toPolyEquiv : SparsePoly R ≃ₐ[R] Polynomial R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap R (SparsePoly R)) X

  -- Use our new helper for the right inverse
  right_inv p := toPoly_ofPoly p

  -- Use injectivity + right_inv to prove the left inverse
  left_inv p := by
    apply toPoly_injective
    rw [toPoly_ofPoly]

  -- The following preserve the Algebra/Ring structure
  map_add' := toPoly_add
  map_mul' := toPoly_mul
  commutes' r := toPoly_C r

@[simp]
theorem ofPoly_X : toPolyEquiv.symm Polynomial.X = (X : SparsePoly R) := by
  simp [toPolyEquiv]

@[simp]
theorem toPoly_X : (X : SparsePoly R).toPoly = Polynomial.X := by
  rw [← toPolyEquiv.apply_symm_apply Polynomial.X, ofPoly_X]; rfl

-- Define our inner "constant" (x + 1)
def x_plus_1 : SparsePoly ℤ := X + 1

-- Define the dividend: (x + 1) * y^2 - (x + 1)
-- Note: the outer X is 'y', the inner X is 'x'
def dividend : SparsePoly (SparsePoly ℤ) :=
  C x_plus_1 * X^2 - C x_plus_1

-- Define the divisor: y - 1
def divisor : SparsePoly (SparsePoly ℤ) :=
  X - 1

-- Run the computation
#eval (dividend / divisor)

-- This will return (0, dividend) because division in ℤ is strict

end SparsePoly
