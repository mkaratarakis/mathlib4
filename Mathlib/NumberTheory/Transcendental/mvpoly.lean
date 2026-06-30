/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic
import Mathlib.Data.List.Sort
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Computable multivariate polynomials (`MvSparsePoly`)

This file provides `MvSparsePoly`, a computational, sparse, distributed representation of
multivariate polynomials over a commutative ring `R` with `DecidableEq R`. The number of
variables `nvars` is fixed, and a polynomial is stored as a list of `(exponent-vector,
coefficient)` pairs (with non-zero coefficients), mirroring Mathlib's `MvPolynomial`. This
representation serves as the backend for the `mv_decide`/`mv_compute` reflection tactic.

Based on the univariate `SparsePoly` by Mario Carneiro at the Hausdorff Institute, June 2024.
-/

set_option linter.style.longFile 4400

@[ext] structure MvDegrees (nvars : ℕ) where
  degrees : Array ℕ
  correct: degrees.size = nvars
  totalDegree : ℕ
  totalDegree_eq : totalDegree = degrees.foldl (· + ·) 0

-- Helper 1: Pull accumulator out of a pure List foldl loop
lemma list_foldl_add_acc (l : List ℕ) (acc : ℕ) :
    l.foldl (· + ·) acc = acc + l.foldl (· + ·) 0 := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc + x), ih (0 + x)]
    omega

-- Helper 2: Prove the distribution entirely on pure Lists!
-- Notice there are NO arrays here, so foldlM never appears.
lemma list_zipWith_foldl_add (la lb : List ℕ) (h : la.length = lb.length) :
    (List.zipWith (· + ·) la lb).foldl (· + ·) 0 =
    la.foldl (· + ·) 0 + lb.foldl (· + ·) 0 := by
  induction la generalizing lb with
  | nil =>
    cases lb with
    | nil => rfl -- 100% works now because it's just pure lists!
    | cons y ys => simp at h
  | cons x xs ih =>
    cases lb with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zipWith, List.foldl_cons, List.length_cons, Nat.succ.injEq] at h ⊢
      rw [list_foldl_add_acc (List.zipWith (· + ·) xs ys) (0 + (x + y))]
      rw [ih ys h]
      have h1 : xs.foldl (· + ·) (0 + x) = x + xs.foldl (· + ·) 0 := by
        rw [list_foldl_add_acc xs (0 + x)]; omega
      have h2 : ys.foldl (· + ·) (0 + y) = y + ys.foldl (· + ·) 0 := by
        rw [list_foldl_add_acc ys (0 + y)]; omega
      rw [h1, h2]
      omega

-- Helper 3: The final Array lemma.
-- We instantly bridge to lists and apply the pure list theorem.
lemma array_zipWith_foldl_add (a b : Array ℕ) (h : a.size = b.size) :
    (Array.zipWith (· + ·) a b).foldl (· + ·) 0 =
    a.foldl (· + ·) 0 + b.foldl (· + ·) 0 := by
  have h_len : a.toList.length = b.toList.length := by exact h
  simp only [← Array.foldl_toList]
  simp only [Array.toList_zipWith]
  exact list_zipWith_foldl_add a.toList b.toList h_len

-- Helper 4: Pure list proof that folding a list of zeros is 0
lemma list_replicate_zero_foldl (n : ℕ) :
    (List.replicate n 0).foldl (· + ·) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- Replicate (succ k) is definitionally `0 :: replicate k`.
    -- `change` bypasses the need for Mathlib unfold lemmas!
    change (0 :: List.replicate k 0).foldl (· + ·) 0 = 0
    simp only [List.foldl_cons]
    -- We reuse the list_foldl_add_acc helper we proved earlier!
    rw [list_foldl_add_acc (List.replicate k 0) (0 + 0)]
    omega

-- Helper 5: Bridge the pure list proof back to the Array (Version-Proof)
lemma array_replicate_zero_foldl (n : ℕ) :
    ((List.replicate n 0).toArray).foldl (· + ·) 0 = 0 := by
  -- 1. Force Lean to unsimplify Array.foldl backwards into List.foldl
  simp only [← Array.foldl_toList]
  -- 2. toList and toArray instantly cancel each other out!
  -- 3. Apply our pure math theorem
  exact list_replicate_zero_foldl n

-- Helper 6: Pure List proof for distributing scalar multiplication over foldl sums
lemma list_map_mul_foldl (l : List ℕ) (n : ℕ) :
    (l.map (· * n)).foldl (· + ·) 0 = l.foldl (· + ·) 0 * n := by
  induction l with
  | nil => grind
  | cons x xs ih =>
    -- 1. Unfold the map and foldl one step
    simp only [List.map_cons, List.foldl_cons]

    -- 2. Pull the accumulated terms out using our trusty `list_foldl_add_acc`
    rw [list_foldl_add_acc (xs.map (· * n)) (0 + x * n)]
    rw [list_foldl_add_acc xs (0 + x)]

    -- 3. Apply the induction hypothesis to the tail
    rw [ih]

    -- 4. The goal is now non-linear (multiplying variables).
    -- We use Nat.add_mul to distribute `(a + b) * n` into `a * n + b * n`.
    rw [Nat.add_mul]

    -- 5. Now everything is linearly separated, omega crushes it instantly!
    grind

-- Helper 7: Bridge the pure list proof back to the Array
lemma array_map_mul_foldl (a : Array ℕ) (n : ℕ) :
    (a.map (· * n)).foldl (· + ·) 0 = a.foldl (· + ·) 0 * n := by
  -- Force Lean to unsimplify Array.foldl backwards into List.foldl
  simp only [← Array.foldl_toList]

  -- Push the toList inside the Array.map
  simp only [Array.toList_map]

  -- The goal now perfectly matches our pure List theorem!
  exact list_map_mul_foldl a.toList n

-- Intermediate 1: Arrays are equal if their lists are equal (bypasses Array bounds checking)
lemma array_eq_of_toList_eq {α} {a b : Array α} (h : a.toList = b.toList) : a = b := by
  cases a; cases b; simp_all

-- Intermediate 2: Associativity on Lists
lemma list_zipWith_add_assoc (a b c : List ℕ) :
  List.zipWith (· + ·) (List.zipWith (· + ·) a b) c =
  List.zipWith (· + ·) a (List.zipWith (· + ·) b c) := by
  induction a generalizing b c with
  | nil => rfl
  | cons x xs ih =>
    cases b; rfl
    cases c; rfl
    simp only [List.zipWith]
    rw [ih]
    grind

-- Intermediate 3: Commutativity on Lists
lemma list_zipWith_add_comm (a b : List ℕ) :
  List.zipWith (· + ·) a b = List.zipWith (· + ·) b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b; rfl
    simp only [List.zipWith]
    rw [ih]
    grind


-- Intermediate 4: Zero Add on Lists
lemma list_zipWith_zero_add (a : List ℕ) :
  List.zipWith (· + ·) (List.replicate a.length 0) a = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change List.zipWith (· + ·) (0 :: List.replicate xs.length 0) (x :: xs) = x :: xs
    simp only [List.zipWith]
    rw [ih]
    grind

-- Intermediate 5: Add Zero on Lists
lemma list_zipWith_add_zero (a : List ℕ) :
  List.zipWith (· + ·) a (List.replicate a.length 0) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change List.zipWith (· + ·) (x :: xs) (0 :: List.replicate xs.length 0) = x :: xs
    simp only [List.zipWith]
    rw [ih]
    grind

-- Right-cancellation for pointwise list addition.
lemma list_zipWith_add_right_cancel {la lb lc : List ℕ}
    (h1 : la.length = lc.length) (h2 : lb.length = lc.length)
    (h : List.zipWith (· + ·) la lc = List.zipWith (· + ·) lb lc) : la = lb := by
  induction la generalizing lb lc with
  | nil =>
    cases lc with
    | nil => cases lb with | nil => rfl | cons => simp at h2
    | cons => simp at h1
  | cons a as ih =>
    cases lc with
    | nil => simp at h1
    | cons c cs =>
      cases lb with
      | nil => simp at h2
      | cons b bs =>
        simp only [List.zipWith_cons_cons, List.cons.injEq] at h
        simp only [List.length_cons, Nat.succ.injEq] at h1 h2
        obtain ⟨hab, htail⟩ := h
        rw [show a = b by omega, ih h1 h2 htail]

-- Intermediate 6: Map * 0 is Replicate 0
lemma list_map_zero (a : List ℕ) :
  a.map (· * 0) = List.replicate a.length 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change (x * 0) :: (xs.map (· * 0)) = 0 :: List.replicate xs.length 0
    rw [ih]
    rfl

-- Intermediate 7: Nsmul Succ on Lists
lemma list_nsmul_succ (a : List ℕ) (n : ℕ) :
  a.map (· * (n + 1)) = List.zipWith (· + ·) a (a.map (· * n)) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, List.zipWith]
    rw [ih]
    grind
-- Intermediate Lemma: The size of ANY MvDegrees array is exactly nvars.
@[simp]
lemma MvDegrees.size_eq {nvars : ℕ} (x : MvDegrees nvars) : x.degrees.size = nvars :=
  x.correct

-- Intermediate 3: Bridge the associativity theorem to Arrays
lemma array_zipWith_add_assoc (a b c : Array ℕ) :
    Array.zipWith (· + ·) (Array.zipWith (· + ·) a b) c =
    Array.zipWith (· + ·) a (Array.zipWith (· + ·) b c) := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  exact list_zipWith_add_assoc a.toList b.toList c.toList

-- Bridge 4: Zero Add for Arrays
lemma array_zipWith_zero_add (a : Array ℕ) (nvars : ℕ) (h : a.size = nvars) :
    Array.zipWith (· + ·) (List.replicate nvars 0).toArray a = a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  -- Flip the size proof: if a.size = nvars, then nvars = a.toList.length
  have h_len : nvars = a.toList.length := h.symm
  rw [h_len]
  exact list_zipWith_zero_add a.toList

-- Bridge 5: Add Zero for Arrays
lemma array_zipWith_add_zero (a : Array ℕ) (nvars : ℕ) (h : a.size = nvars) :
    Array.zipWith (· + ·) a (List.replicate nvars 0).toArray = a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  have h_len : nvars = a.toList.length := h.symm
  rw [h_len]
  exact list_zipWith_add_zero a.toList

-- Bridge 6: Commutativity for Arrays
lemma array_zipWith_add_comm (a b : Array ℕ) :
    Array.zipWith (· + ·) a b = Array.zipWith (· + ·) b a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  exact list_zipWith_add_comm a.toList b.toList

-- Bridge 7: Nsmul Zero for Arrays
lemma array_map_zero (a : Array ℕ) (nvars : ℕ) (h : a.size = nvars) :
    a.map (· * 0) = (List.replicate nvars 0).toArray := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_map]
  have h_len : nvars = a.toList.length := h.symm
  rw [h_len]
  exact list_map_zero a.toList


-- Bridge 8: Nsmul Succ for Arrays (Updated order to match Mathlib)
lemma array_nsmul_succ (a : Array ℕ) (n : ℕ) :
    a.map (· * (n + 1)) = Array.zipWith (· + ·) (a.map (· * n)) a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_map, Array.toList_zipWith]
  ext i j
  grind

variable {nvars : ℕ}

instance : AddCommMonoid (MvDegrees nvars) where
  add a b := {
    -- FIX: Function comes first in Array.zipWith
    degrees := Array.zipWith (· + ·) a.degrees b.degrees
    correct := by simp [a.correct, b.correct]
    totalDegree := a.totalDegree + b.totalDegree
    totalDegree_eq := by
      -- 1. Unfold the proven total degrees of a and b
      rw [a.totalDegree_eq, b.totalDegree_eq]

      -- 2. Prove their sizes match using the `correct` field
      have h_size : a.degrees.size = b.degrees.size := by
        rw [a.correct, b.correct]

      -- 3. Apply our exact helper lemma to close the goal!
      grind [array_zipWith_foldl_add]
  }

  zero := {
    -- Create a list of zeros and convert it to an array
    degrees := (List.replicate nvars 0).toArray
    -- `simp` natively knows that the size of this array is `nvars`
    correct := by simp
    totalDegree := 0
    totalDegree_eq := by
      -- Flip the goal to `(List.replicate nvars 0).toArray.foldl ... = 0`
      symm
      -- Apply our version-proof helper lemma
      exact array_replicate_zero_foldl nvars
  }
  nsmul n a := {
    -- FIX: Function comes first in Array.map
    degrees := Array.map (· * n) a.degrees
    correct := by simp [a.correct]
    totalDegree := a.totalDegree * n
    totalDegree_eq := by
      -- 1. Unfold the proven totalDegree equality from `a`
      rw [a.totalDegree_eq]

      -- 2. Apply our symmetric helper lemma!
      -- (It proves Sum(map) = Sum * n, so symm flips it to Sum * n = Sum(map))
      exact (array_map_mul_foldl a.degrees n).symm
  }

  add_assoc a b c := by
    apply MvDegrees.ext
    · -- Goal 1: Prove the arrays are equal.
      -- `change` forces Lean to unfold the `+` operator into our exact Array definition
      change Array.zipWith (· + ·) (Array.zipWith (· + ·) a.degrees b.degrees) c.degrees =
             Array.zipWith (· + ·) a.degrees (Array.zipWith (· + ·) b.degrees c.degrees)

      -- Now our bridge lemma matches 100% perfectly!
      exact array_zipWith_add_assoc a.degrees b.degrees c.degrees

    · -- Goal 2: Prove the total degrees are equal.
      -- `change` forces the `+` operator to unfold into Nat addition
      change (a.totalDegree + b.totalDegree) + c.totalDegree =
             a.totalDegree + (b.totalDegree + c.totalDegree)

      -- `omega` instantly solves natural number associativity
      omega

  zero_add a := by
    apply MvDegrees.ext
    · -- 1. Expose the zero array definition
      change Array.zipWith (· + ·) (List.replicate nvars 0).toArray a.degrees = a.degrees
      exact array_zipWith_zero_add a.degrees nvars a.correct
    · -- 2. Expose the totalDegree addition
      change 0 + a.totalDegree = a.totalDegree
      omega

  add_zero a := by
    apply MvDegrees.ext
    · change Array.zipWith (· + ·) a.degrees (List.replicate nvars 0).toArray = a.degrees
      exact array_zipWith_add_zero a.degrees nvars a.correct
    · change a.totalDegree + 0 = a.totalDegree
      omega

  add_comm a b := by
    apply MvDegrees.ext
    · change Array.zipWith (· + ·) a.degrees b.degrees = Array.zipWith (· + ·) b.degrees a.degrees
      exact array_zipWith_add_comm a.degrees b.degrees
    · change a.totalDegree + b.totalDegree = b.totalDegree + a.totalDegree
      omega

  nsmul_zero a := by
    apply MvDegrees.ext
    · change a.degrees.map (· * 0) = (List.replicate nvars 0).toArray
      exact array_map_zero a.degrees nvars a.correct
    · change a.totalDegree * 0 = 0
      omega

  nsmul_succ n a := by
    apply MvDegrees.ext
    · -- Notice the map (* n) is now on the LEFT of the zipWith
      change a.degrees.map (· * (n + 1)) = Array.zipWith (· + ·) (a.degrees.map (· * n)) a.degrees
      exact array_nsmul_succ a.degrees n
    · -- The totalDegree addition is also swapped to match
      change a.totalDegree * (n + 1) = a.totalDegree * n + a.totalDegree
      grind


-- @[ext] structure MvMonomial (R : Type) (nvars : ℕ) where
--   coeff : R
--   degrees : MvDegrees nvars

@[ext] class WOrdering (nvars : ℕ) extends LinearOrder (MvDegrees nvars) where
  zero_le {x : MvDegrees nvars} : 0 ≤ x
  add_le_add {x y z : MvDegrees nvars} : x ≤ y → x + z ≤ y + z
  -- The order is well-founded (a genuine admissible monomial order). Discharged for the
  -- concrete lexicographic instance below by `mvDegrees_lex_wf`.
  wf : WellFounded (fun (a b : MvDegrees nvars) => a < b)

-- --  weakcomparison ≤ in TeX
-- def lexorder (a : MvDegrees nvars) (b : MvDegrees nvars) : Bool := Id.run do
--   for ai in a.degrees, bi in b.degrees do
--      if ai < bi then return true
--      else if ai > bi then return false
--   return true

-- 1. Pure List functional definition of Lexicographic Order
def list_lex : List ℕ → List ℕ → Bool
| [], _ => true
| _, [] => true
| (x::xs), (y::ys) =>
  if x < y then true
  else if y < x then false
  else list_lex xs ys

-- 2. Prove totality perfectly on the pure lists
lemma list_lex_total (l1 l2 : List ℕ) : list_lex l1 l2 = true ∨ list_lex l2 l1 = true := by
  induction l1 generalizing l2 with
  | nil => simp [list_lex]
  | cons x xs ih =>
    cases l2 with
    | nil => simp [list_lex]
    | cons y ys =>
      -- Unfold the recursive definition for this step
      unfold list_lex

      -- Split into the 3 mathematical possibilities: x < y, x = y, or x > y
      rcases Nat.lt_trichotomy x y with hlt | heq | hgt
      · -- Case 1: x < y
        have h_not_gt : ¬(y < x) := by omega
        -- simp instantly sees `x < y` is true and solves the left side of the OR
        simp [hlt, h_not_gt]

      · -- Case 2: x = y
        subst heq -- Replaces y with x everywhere
        have h_not_lt : ¬(x < x) := by omega
        -- Both sides of the OR reduce to checking the tails of the lists
        simp
        grind

      · -- Case 3: x > y
        have h_not_lt : ¬(x < y) := by omega
        -- simp sees `y < x` is true and solves the right side of the OR!
        simp [h_not_lt, hgt]

-- Intermediate 1: Isolate the state machine body of your loop
-- This exactly mirrors what Lean generates for `if ... return ... else return ...`
def lex_step (p : ℕ × ℕ) (_acc : Bool) : ForInStep Bool :=
  if p.1 < p.2 then ForInStep.done true
  else if p.1 > p.2 then ForInStep.done false
  else ForInStep.yield true

-- -- Intermediate 2: Prove the loop state machine exactly matches `list_lex` on Lists!
-- lemma list_forIn_eq_list_lex (la lb : List ℕ) :
--     Id.run (ForIn.forIn (la.zip lb) true lex_step) = list_lex la lb := by
--   -- We do structural induction on the lists, dragging `lb` along
--   induction la generalizing lb with
--   | nil => rfl
--   | cons x xs ih =>
--     cases lb with
--     | nil => rfl
--     | cons y ys =>
--       -- Unfold the lists one step to expose the current loop iteration
--       unfold ForIn.forIn
--       unfold lex_step
--       unfold list_lex

--       -- Force Lean to evaluate the 3 mathematical realities of x and y
--       rcases Nat.lt_trichotomy x y with hlt | heq | hgt
--       · -- Case: x < y
--         simp [hlt]
--         sorry
--       · -- Case: x = y
--         have h_not_lt : ¬(x < y) := by omega
--         have h_not_gt : ¬(x > y) := by omega
--         -- The current iteration yields, so we apply the induction hypothesis to the rest
--         simp [heq]
--         sorry
--       · -- Case: x > y
--         have h_not_lt : ¬(x < y) := by omega
--         simp [h_not_lt, hgt]
--         sorry



-- Intermediate 3: Bridge the Array loop to the List loop
-- This handles the low-level Array index shifting so you don't have to
lemma array_forIn_eq_list_forIn (a b : Array ℕ) :
    Id.run (ForIn.forIn (a.zip b) true lex_step) =
    Id.run (ForIn.forIn (a.toList.zip b.toList) true lex_step) := by
  -- Mathlib natively knows how to convert Array loops to List loops
  grind [Array.toList_zip]


-- 1. YOUR EXACT DEFINITION (Preserved for fast C++ execution)
-- We just rename it to `_impl` so the compiler knows it's the execution engine.
def lexorder_impl (a b : MvDegrees nvars) : Bool := Id.run do
  for ai in a.degrees, bi in b.degrees do
     if ai < bi then return true
     else if ai > bi then return false
  return true

--instance : LE (MvDegrees nvars) where le a b := lexorder_impl a b

-- 3. THE LEAN 4 MAGIC TRICK
-- This tells Lean: "When evaluating math, use `list_lex`.
-- But when actually running the code, run your exact `lexorder_impl` loop!"
@[implemented_by lexorder_impl]
def lexorder (a b : MvDegrees nvars) : Bool :=
  list_lex a.degrees.toList b.degrees.toList


-- 1. Anti-symmetry on pure lists
lemma list_lex_antisymm {l1 l2 : List ℕ} (hlen : l1.length = l2.length)
    (h1 : list_lex l1 l2 = true) (h2 : list_lex l2 l1 = true) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      unfold list_lex at h1 h2
      -- Split the conditionals and delete impossible math
      split_ifs at h1 h2 <;> try omega
      -- If we survived, x must equal y.
      have hxy : x = y := by omega
      subst hxy
      -- Apply induction to the tails!
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have := ih hlen h1 h2
      subst this
      rfl


-- 3. The Equivalence Bridge
lemma lexorder_eq_list_lex (a b : MvDegrees nvars) :
    lexorder a b = list_lex a.degrees.toList b.degrees.toList := by
  unfold lexorder
  have h_len : a.degrees.toList.length = b.degrees.toList.length := by
    aesop
  have ha_arr : a.degrees = a.degrees.toList.toArray := by apply array_eq_of_toList_eq; simp
  have hb_arr : b.degrees = b.degrees.toList.toArray := by apply array_eq_of_toList_eq; simp
  rw [ha_arr, hb_arr]

-- 2. Transitivity on pure lists
lemma list_lex_trans {l1 l2 l3 : List ℕ} (h12 : l1.length = l2.length) (h23 : l2.length = l3.length)
    (h1 : list_lex l1 l2 = true) (h2 : list_lex l2 l3 = true) : list_lex l1 l3 = true := by
  induction l1 generalizing l2 l3 with
  | nil => rfl
  | cons x xs ih =>
    cases l2 with | nil => simp at h12 | cons y ys =>
    cases l3 with | nil => simp at h23 | cons z zs =>
      unfold list_lex at h1 h2 ⊢
      -- This single line proves all 27 combinations of x, y, and z inequalities!
      split_ifs at h1 h2 ⊢ <;> try omega
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h12 h23
      exact ih h12 h23 h1 h2

-- 3. Zero ≤ X on pure lists
lemma list_lex_zero_le (l : List ℕ) : list_lex (List.replicate l.length 0) l = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change list_lex (0 :: List.replicate xs.length 0) (x :: xs) = true
    unfold list_lex
    split_ifs <;> try omega
    grind

-- 4. Additive preservation on pure lists
lemma list_lex_add_le_add (la lb lc : List ℕ) (h1 : la.length = lb.length) (h2 : lb.length = lc.length)
    (hab : list_lex la lb = true) :
    list_lex (List.zipWith (· + ·) la lc) (List.zipWith (· + ·) lb lc) = true := by
  induction la generalizing lb lc with
  | nil => cases lb; cases lc; rfl; all_goals { simp at * }
  | cons x xs ih =>
    cases lb with | nil => simp at h1 | cons y ys =>
    cases lc with | nil => simp at h2 | cons z zs =>
      unfold list_lex at hab ⊢
      simp only [List.zipWith]
      -- omega natively knows that if x < y, then x + z < y + z !
      split_ifs at hab ⊢ <;> try omega
      simp at h1 h2
      grind


--instance : LE (MvDegrees nvars) where le a b := lexorder a b = true

-- theorem lexorder_total (a b : MvDegrees nvars) : a ≤ b ∨ b ≤ a := by
--   change list_lex a.degrees.toList b.degrees.toList = true ∨
--          list_lex b.degrees.toList a.degrees.toList = true
--   exact list_lex_total a.degrees.toList b.degrees.toList

-- FIX: We use `lexorder a b = true` instead of `≤` so we don't need LE yet.
theorem lexorder_total (a b : MvDegrees nvars) : lexorder a b = true ∨ lexorder b a = true := by
  change list_lex a.degrees.toList b.degrees.toList = true ∨
         list_lex b.degrees.toList a.degrees.toList = true
  exact list_lex_total a.degrees.toList b.degrees.toList


-- Intermediate Lemma: Anti-symmetry for MvDegrees
lemma lexorder_antisymm (a b : MvDegrees nvars) (hab : lexorder a b = true)
    (hba : lexorder b a = true) : a = b := by
  have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop --[← a.correct, ← b.correct]
  have hlist := list_lex_antisymm h1 hab hba
  apply MvDegrees.ext
  · exact array_eq_of_toList_eq hlist
  · rw [a.totalDegree_eq, b.totalDegree_eq, array_eq_of_toList_eq hlist]

-- The strict lexicographic order is witnessed by the first differing coordinate.
lemma list_lex_strict_first_diff : ∀ {l1 l2 : List ℕ}, l1.length = l2.length →
    list_lex l1 l2 = true → ¬ (list_lex l2 l1 = true) →
    ∃ n, n < l1.length ∧ (∀ m, m < n → l1[m]! = l2[m]!) ∧ l1[n]! < l2[n]! := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 hlen h1 h2
    cases l2 with
    | nil => exact absurd rfl h2
    | cons y ys => simp at hlen
  | cons x xs ih =>
    intro l2 hlen h1 h2
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [list_lex] at h1 h2
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · exact ⟨0, by simp, fun m hm => absurd hm (by omega), by simpa using hxy⟩
      · subst hxy
        simp only [lt_self_iff_false, if_false] at h1 h2
        obtain ⟨n, hn, heq, hlt⟩ := ih hlen' h1 h2
        refine ⟨n + 1, by simpa using hn, fun m hm => ?_, by simpa using hlt⟩
        cases m with
        | zero => rfl
        | succ k => simpa using heq k (by omega)
      · exfalso
        rw [if_neg (asymm hxy), if_pos hxy] at h1
        exact absurd h1 (by simp)

-- Bridge `toList[k]!` to the bounded array access.
private lemma mvDegrees_getElem!_toList (d : MvDegrees nvars) (k : ℕ) (hk : k < nvars) :
    d.degrees.toList[k]! = d.degrees[k]'(by rw [d.correct]; exact hk) := by
  rw [getElem!_pos d.degrees.toList k (by rw [Array.length_toList, d.correct]; exact hk)]
  exact (Array.getElem_toList ..).symm

-- Well-foundedness of the lexicographic monomial order, via `Pi.Lex.wellFounded` on
-- `Fin nvars → ℕ` (a finite index ordering each well-founded `ℕ`).
lemma mvDegrees_lex_wf :
    WellFounded (fun a b : MvDegrees nvars => lexorder a b = true ∧ ¬ (lexorder b a = true)) := by
  let f : MvDegrees nvars → (Fin nvars → ℕ) :=
    fun d k => d.degrees[(k : ℕ)]'(by rw [d.correct]; exact k.2)
  have hpi := Pi.Lex.wellFounded (α := fun _ : Fin nvars => ℕ) (· < ·)
    (fun _ => wellFounded_lt)
  refine Subrelation.wf ?_ (InvImage.wf f hpi)
  intro a b hab
  obtain ⟨hab1, hab2⟩ := hab
  change list_lex a.degrees.toList b.degrees.toList = true at hab1
  change ¬ (list_lex b.degrees.toList a.degrees.toList = true) at hab2
  have hlen : a.degrees.toList.length = b.degrees.toList.length := by
    rw [Array.length_toList, Array.length_toList, a.correct, b.correct]
  obtain ⟨n, hn, heq, hlt⟩ := list_lex_strict_first_diff hlen hab1 hab2
  have hn' : n < nvars := by rwa [Array.length_toList, a.correct] at hn
  refine ⟨⟨n, hn'⟩, fun j hj => ?_, ?_⟩
  · have hjn : (j : ℕ) < n := hj
    have hh := heq (j : ℕ) hjn
    rwa [mvDegrees_getElem!_toList a (j : ℕ) (lt_trans hjn hn'),
      mvDegrees_getElem!_toList b (j : ℕ) (lt_trans hjn hn')] at hh
  · have hh := hlt
    rwa [mvDegrees_getElem!_toList a n hn', mvDegrees_getElem!_toList b n hn'] at hh

instance : WOrdering nvars where
  le a b := lexorder a b
  le_refl a := or_self_iff.1 (lexorder_total _ _)

  le_trans a b c hab hbc := by
    change list_lex a.degrees.toList b.degrees.toList = true at hab
    change list_lex b.degrees.toList c.degrees.toList = true at hbc
    change list_lex a.degrees.toList c.degrees.toList = true
    have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
    have h2 : b.degrees.toList.length = c.degrees.toList.length := by aesop
    exact list_lex_trans h1 h2 hab hbc

  le_antisymm a b hab hba := by
    have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
    change list_lex a.degrees.toList b.degrees.toList = true at hab
    change list_lex b.degrees.toList a.degrees.toList = true at hba
    -- 1. Use the list lemma to prove the pure lists are equal
    have hlist := list_lex_antisymm h1 hab hba
    -- 2. Expand MvDegrees equality and map it to the lists
    apply MvDegrees.ext
    · exact array_eq_of_toList_eq hlist
    · rw [a.totalDegree_eq, b.totalDegree_eq]
      rw [array_eq_of_toList_eq hlist]

  -- Boilerplate LinearOrder logic
  min a b := if lexorder a b = true then a else b
  max a b := if lexorder a b = true then b else a
  compare a b :=
    if lexorder a b = true ∧ ¬(lexorder b a = true) then .lt
    else if lexorder a b = true then .eq
    else .gt

  le_total := lexorder_total
  toDecidableLE := fun a b => inferInstanceAs (Decidable (lexorder a b = true))
  compare_eq_compareOfLessAndEq a b := by
    -- 1. Fetch our standalone anti-symmetry lemma
    have h_anti := lexorder_antisymm a b

    -- 2. Unfold the definitions
    dsimp [compare, compareOfLessAndEq]

    -- 3. Convert Mathlib's generic `<` into our `lexorder` logic natively
    --simp only [lt_iff_le_not_le]

    -- 4. Split all the if/then/else statements at once
    split_ifs

    -- Case 1: Both sides agree (rfl instantly solves the valid branches)
    · rfl

    -- Case 2: Impossible Contradiction (a = b, but lexorder says a > b)
    · -- The `‹a = b›` syntax lets us grab Lean's hidden `✝` variable!
      subst ‹a = b›
      -- By totality, lexorder a a MUST be true
      have h_refl : lexorder a a = true := by
        rcases lexorder_total a a with h | h <;> exact h
      -- This contradicts the `¬lexorder a a = true` branch we are in.
      grind

    -- Case 3: Impossible Contradiction (lexorder says a = b, but Mathlib says a ≠ b)
    · -- If we are in this branch, lexorder a b = true, but a < b is false.
      -- This mathematically forces lexorder b a to also be true!
      have hba : lexorder b a = true := by tauto
      -- If both are true, our anti-symmetry lemma says a = b!
      have heq := h_anti ‹lexorder a b = true› hba
      -- This contradicts the `¬(a = b)` branch we are in.
      contradiction

    -- Case 4: Both sides agree on .gt
    · -- 1. Grab the hidden `a = b` variable
      subst ‹a = b›
      -- 2. Prove that lexorder a a is always true
      have h_refl : lexorder a a = true := by
        rcases lexorder_total a a with h | h <;> exact h
      -- 3. Lean instantly sees this contradicts h✝¹ (¬lexorder a a = true)
      contradiction
    · rfl

  -- The WOrdering specific properties
  zero_le {a} := by
    -- 1. Expose the zero definition and drop the Array wrappers natively!
    -- (Lean allows this because .toArray.toList is definitionally equal to doing nothing)
    change list_lex (List.replicate nvars 0) (a : MvDegrees nvars).degrees.toList = true

    -- 2. Extract the array length equality from our `correct` property
    have h : nvars = (a : MvDegrees nvars).degrees.toList.length := by aesop-- [← a.correct]

    -- 3. Swap `nvars` for the actual list length
    --rw [h]

    -- 4. Now the goal is a 100% perfect match for our pure list lemma!
    grind [list_lex_zero_le (a : MvDegrees nvars).degrees.toList]

  -- FIX: Use {a b c} to match the implicit {x y z} in your class definition
  add_le_add {a b c} hab := by
    change list_lex a.degrees.toList b.degrees.toList = true at hab
    change list_lex (Array.zipWith (· + ·) a.degrees c.degrees).toList
      (Array.zipWith (· + ·) b.degrees c.degrees).toList = true
    simp only [Array.toList_zipWith]

    have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
    have h2 : b.degrees.toList.length = c.degrees.toList.length := by aesop

    exact list_lex_add_le_add a.degrees.toList b.degrees.toList c.degrees.toList h1 h2 hab

  wf := mvDegrees_lex_wf

@[ext] structure MvSparsePoly (R : Type) [CommRing R] (nvars : ℕ)
    [WOrdering nvars] : Type where
  terms : List (MvDegrees nvars × R)
  sorted : terms.Pairwise (·.1 > ·.1)
  nonzero : ∀ x ∈ terms, x.2 ≠ 0

namespace MvSparsePoly

open MvPolynomial

--instance [CommRing R] [Lean.ToFormat R] : Lean.ToFormat (MvSparsePoly R nvars) where
--  format x :=
--    have := x.terms.foldl (init := none) fun (f : Option Lean.Format) (i, x) =>
--      let monomial := if i = 0 then f!"({x})" else if i = 1 then f!"({x})*X" else f!"({x})*X^{i}"
--      match f with
--      | none => monomial
--      | some f => f ++ " + " ++ monomial
--    this.getD f!"0"
--instance [CommRing R] [Lean.ToFormat R] : Repr (SparsePoly R) where
--  reprPrec x _ := Lean.format x

variable {R : Type} [CommRing R] [DecidableEq R]

def ofSortedList
    (terms : List (MvDegrees nvars × R)) (sorted : terms.Pairwise (·.1 > ·.1)) :
    MvSparsePoly R nvars where
  terms := terms.filter (·.2 ≠ 0)
  -- FIX: Remove the `_`. List.filter_sublist is already fully applied implicitly!
  sorted := sorted.sublist List.filter_sublist
  nonzero := by simp [List.mem_filter]

-- def ofSortedList
--     (terms : List (MvDegrees nvars × R)) (sorted : terms.Pairwise (·.1 > ·.1)) :
--     MvSparsePoly R nvars where
--   terms := terms.filter (·.2 ≠ 0)
--   sorted := sorted.sublist (List.filter_sublist _)
--   nonzero := by simp [List.mem_filter]

instance : Zero (MvSparsePoly R nvars) where
  zero := { terms := [], sorted := .nil, nonzero := nofun }

def C (r : R) : MvSparsePoly R nvars := ofSortedList [(0, r)] (by simp)
-- Need the ofSortedList to deal with r=0; note that 0 is the 0 of the MvDegrees monoid

instance : One (MvSparsePoly R nvars) where
  one := C 1

-- def degLt (a : ℕ) (l : List (ℕ × R)) : Prop := ∀ x ∈ l, x.1 < a

-- 1. Multivariate version of Degree Less-Than
def degLt (a : MvDegrees nvars) (l : List (MvDegrees nvars × R)) : Prop :=
  ∀ x ∈ l, x.1 < a

-- Relate our structures to the MvPolynomial of Mathlib
noncomputable def MvDegrees.toFinsupp (deg : MvDegrees nvars) : Fin nvars →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => deg.degrees[i]'(by simp [deg.correct, i.2])) (by simp)

noncomputable def toPolyCore : List (MvDegrees nvars × R) → MvPolynomial (Fin nvars) R
  | [] => 0
  | (i, a) :: x => monomial (MvDegrees.toFinsupp i) a + toPolyCore x

noncomputable def toPoly (x : MvSparsePoly R nvars) : MvPolynomial (Fin nvars) R :=
  toPolyCore x.terms

def addCore : List (MvDegrees nvars × R) → List (MvDegrees nvars × R) → List (MvDegrees nvars × R)
  | [], yy => yy
  | xx, [] => xx
  | xx@((i, a) :: x), yy@((j, b) :: y) =>
    if i < j then
      (j, b) :: addCore xx y
    else if j < i then
      (i, a) :: addCore x yy
    else  -- check for a+b=0
      ( fun c => if c=0 then addCore x y else (i, c) :: addCore x y) (a+b)
    termination_by xx yy => xx.length + yy.length

-- 2. Multivariate version of the preservation theorem
theorem addCore_degLt {n : MvDegrees nvars} : ∀ {x y : List (MvDegrees nvars × R)},
    degLt n x → degLt n y → degLt n (addCore x y) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x' j b y' =>
    -- Extract the head and tail hypotheses
    let ⟨hi, hx'⟩ := List.forall_mem_cons.1 hx
    let ⟨hj, hy'⟩ := List.forall_mem_cons.1 hy
    split
    · next ij =>
      -- Direct proof using degLt definition
      unfold degLt
      intro x hx_mem
      cases hx_mem with
      | head => exact hj
      | tail h => exact addCore_degLt hx hy' x (by aesop)
    split
    · next ji =>
      unfold degLt
      intro x hx_mem
      cases hx_mem with
      | head => exact hi
      | tail h => exact addCore_degLt hx' hy x (by aesop)
    · next h_not_ij h_not_ji =>
      dsimp only
      split
      · exact addCore_degLt hx' hy'
      · unfold degLt
        intro x hx_mem
        cases hx_mem with
        | head => exact hi
        | tail h => exact addCore_degLt hx' hy' x (by aesop)
termination_by x y => x.length + y.length

-- theorem addCore_degLt' {n : ℕ} : ∀ {x y : List (ℕ × R)},
--     degLt n x → degLt n y → degLt n (addCore x y) := by
--   intro x y hx hy
--   unfold addCore
--   split
--   · exact hy
--   · exact hx
--   · next i a x j b y =>
--     let ⟨hi, hx'⟩ := List.forall_mem_cons.1 hx
--     --sorry
--     let .cons hj hy' := hy
--     split
--     · next ij =>
--       constructor
--       · apply addCore_degLt
--         · intro
--           | _, .head _ => exact ij
--           | p, .tail _ hp => exact (hi _ hp).trans ij
--         · exact hj
--       · exact addCore_sorted hx hy'
--     split
--     · next ij =>
--       constructor
--       · apply addCore_degLt
--         · exact hi
--         · intro
--         | _, .head _ => exact ij
--         | p, .tail _ hp => exact (hj _ hp).trans ij
--       · exact addCore_sorted hx' hy
--     · cases (by omega : i = j)
--       constructor
--       · exact addCore_degLt hi hj
--       · exact addCore_sorted hx' hy'
-- termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (MvDegrees nvars × R)},
    x.Pairwise (·.1 > ·.1) → y.Pairwise (·.1 > ·.1) →
    (addCore x y).Pairwise (·.1 > ·.1) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x j b y =>
    let .cons hi hx' := hx
    let .cons hj hy' := hy
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    split
    · next ji =>
      constructor
      · apply addCore_degLt
        · exact hi
        · intro
          | _, .head _ => exact ji
          | p, .tail _ hp => exact (hj _ hp).trans ji
      · exact addCore_sorted hx' hy
    · -- Because we are in a LinearOrder, if ¬(i < j) and ¬(j < i), then i = j.
      -- lt_trichotomy splits into the 3 mathematical realities.
      have eq_ij : i = j := by
        rcases lt_trichotomy i j with hlt | heq | hgt
        · contradiction -- Contradicts the first `split` failure ¬(i < j)
        · exact heq
        · contradiction -- Contradicts the second `split` failure ¬(j < i)

      subst eq_ij
      dsimp only

      -- Now handle the `if a + b = 0` generated by `addCore`
      split
      · -- Case 1: a + b = 0 (Term cancels out, return tail)
        exact addCore_sorted hx' hy'
      · -- Case 2: a + b ≠ 0 (Term stays, return term :: tail)
        constructor
        · exact addCore_degLt hi hj
        · exact addCore_sorted hx' hy'
termination_by x y => x.length + y.length

instance : Add (MvSparsePoly R nvars) where
  add x y :=
    let terms := addCore x.terms y.terms
    ofSortedList terms (addCore_sorted x.sorted y.sorted)


-- 0. Update dedupList to use MvDegrees
def dedupList : List (MvDegrees nvars × R) → List (MvDegrees nvars × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

-- Helper 1: Proves that dedupList never increases the maximum degree of the list.
omit [DecidableEq R] in
lemma dedupList_bound : ∀ (terms : List (MvDegrees nvars × R)) (k : MvDegrees nvars),
    (∀ p ∈ terms, k ≥ p.1) → ∀ p ∈ dedupList terms, k ≥ p.1
  | [], k, h => by
    simp [dedupList]
  | [(i, a)], k, h => by
    intro x hx
    have : dedupList [(i, a)] = [(i, a)] := by unfold dedupList; rfl
    rw [this] at hx
    exact h x hx
  | (i, a) :: (j, b) :: x, k, h => by
    unfold dedupList
    split
    · next heq =>
      apply dedupList_bound ((i, a + b) :: x) k
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_in_x
      · exact h (i, a) (by simp)
      · exact h p (by simp [hp_in_x])
    · next hneq =>
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_in_dedup
      · exact h (i, a) (by simp)
      · apply dedupList_bound ((j, b) :: x) k _ p hp_in_dedup
        intro p' hp'
        exact h p' (by simp [hp'])
termination_by terms => terms.length

-- Helper 2: The recursive proof engine
omit [DecidableEq R] in
lemma dedupList_sorted_aux : ∀ (terms : List (MvDegrees nvars × R)),
    terms.Pairwise (fun p1 p2 => p2.1 ≤ p1.1) →
    (dedupList terms).Pairwise (fun p1 p2 => p2.1 < p1.1)
  | [] => fun _ => by unfold dedupList; constructor
  | [(i, a)] => fun _ => by

    have : dedupList [(i, a)] = [(i, a)] := by unfold dedupList; rfl
    rw [this]
    constructor
    grind
    grind
  | (i, a) :: (j, b) :: x => fun h => by
    unfold dedupList
    split
    · next heq =>
      have h_next : ((i, a + b) :: x).Pairwise (fun p1 p2 => p2.1 ≤ p1.1) := by
        simp only [List.pairwise_cons] at h ⊢
        rcases h with ⟨hi, hj_x⟩
        constructor
        · intro p hp
          exact hi p (List.mem_cons_of_mem _ hp)
        · grind
      exact dedupList_sorted_aux ((i, a + b) :: x) h_next

    · next hneq =>
      have h_next : ((j, b) :: x).Pairwise (fun p1 p2 => p2.1 ≤ p1.1) := h.of_cons
      have ih := dedupList_sorted_aux ((j, b) :: x) h_next

      simp only [List.pairwise_cons] at h ⊢
      rcases h with ⟨hi, hj_x⟩
      constructor
      · intro p hp
        have hj_bound : ∀ p' ∈ ((j, b) :: x), p'.1 ≤ j := by
          intro p' hp'
          simp only [List.mem_cons] at hp'
          rcases hp' with rfl | hp_x
          · exact le_rfl
          · exact hj_x.1 p' hp_x

        have hp_le_j : p.1 ≤ j := dedupList_bound ((j, b) :: x) j hj_bound p hp
        have hi_ge_j : j ≤ i := hi (j, b) (List.mem_cons_self)

        have j_lt_i : j < i := lt_of_le_of_ne hi_ge_j (Ne.symm hneq)
        exact lt_of_le_of_lt hp_le_j j_lt_i
      · exact ih

termination_by terms => terms.length



omit [DecidableEq R] in
theorem dedupList_sorted (terms : List (MvDegrees nvars × R))
  (sorted : terms.Pairwise (·.1 ≥ ·.1)) :
  (dedupList terms).Pairwise (·.1 > ·.1) := dedupList_sorted_aux terms sorted


def ofList (terms : List (MvDegrees nvars × R)) : MvSparsePoly R nvars :=
  -- 1. Use `decide` to turn the abstract `≤` math into
  -- the `Bool` that mergeSort needs
  let terms' := terms.mergeSort (fun a b => decide (b.1 ≤ a.1))

  have hSorted : terms'.Pairwise (·.1 ≥ ·.1) := by
    -- 2. Bridge the Bool logic back to the Math logic
    apply List.Pairwise.imp (R := fun a b => decide (b.1 ≤ a.1) = true)

    -- Subgoal 1: Prove that if the Bool is true, the Math is true
    · intro a b h
      change b.1 ≤ a.1
      -- `of_decide_eq_true` is Lean's built-in bridge from (decide P = true) to P
      exact of_decide_eq_true h

    -- Subgoal 2: Prove the sorting theorem on the booleans
    · apply List.pairwise_mergeSort

      -- Transitivity requirement
      · intro a b c hab hbc
        -- Pull the booleans back into math
        have h1 : b.1 ≤ a.1 := of_decide_eq_true hab
        have h2 : c.1 ≤ b.1 := of_decide_eq_true hbc
        -- Use abstract transitivity, then push back to a boolean
        exact decide_eq_true (le_trans h2 h1)

      -- Totality requirement
      · intro a b
        -- Get the abstract mathematical totality
        have h_tot : b.1 ≤ a.1 ∨ a.1 ≤ b.1 := le_total b.1 a.1

        -- Split the OR and resolve the boolean `||`
        rcases h_tot with h1 | h2
        · simp only [decide_eq_true h1, Bool.true_or]
        · simp only [decide_eq_true h2, Bool.or_true]

  -- 3. Feed the sorted list into the constructor
  ofSortedList (dedupList terms')
    (dedupList_sorted terms' hSorted)

-- Helper: Summing a list of zeros with exactly one '1' results in 1
lemma list_set_one_zero_foldl : ∀ (n : ℕ) (i : ℕ) (_h : i < n),
    ((List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
  | 0, i, h => by omega -- Base case: 0 < 0 is impossible
  | n + 1, 0, h => by
    -- Case: We are setting the very first element (index 0) to 1
    -- The list is definitionally `1 :: List.replicate n 0`
    change (1 :: List.replicate n 0).foldl (· + ·) 0 = 1
    simp only [List.foldl_cons]

    -- Pull the accumulated (0 + 1) out of the foldl
    rw [list_foldl_add_acc (List.replicate n 0) (0 + 1)]

    -- We already proved that folding zeros is 0!
    rw [list_replicate_zero_foldl n]
  | n + 1, i + 1, h => by
    -- Case: We are setting an element deeper in the list
    -- The list is definitionally `0 :: (List.replicate n 0).set i 1`
    change (0 :: (List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
    simp only [List.foldl_cons]

    -- (0 + 0) is just 0, so we cleanly pass it to the induction hypothesis
    change ((List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
    exact list_set_one_zero_foldl n i (by omega)


-- 1. Helper to create a degree array where exactly one variable has degree 1
def singleDegree (v : Fin nvars) : MvDegrees nvars := {
  degrees := ((List.replicate nvars 0).set v.val 1).toArray
  correct := by simp
  totalDegree := 1
  totalDegree_eq := by
    -- 1. Flip the goal to `Array.foldl ... = 1`
    symm

    -- 2. Convert the Array.foldl into a List.foldl
    simp only [← Array.foldl_toList]

    -- 3. `.toArray.toList` is definitionally the identity, so we just `change` it away!
    change ((List.replicate nvars 0).set v.val 1).foldl (· + ·) 0 = 1

    -- 4. Apply our rock-solid list proof!
    exact list_set_one_zero_foldl nvars v.val v.isLt
}

-- 2. Multivariate X requires knowing WHICH variable you want!
def X (v : Fin nvars) : MvSparsePoly R nvars :=
  ofSortedList [(singleDegree v, 1)] (List.pairwise_singleton _ _)

--def X : MvSparsePoly R nvars := ofSortedList [(1, 1)] (List.sorted_singleton _)

-- Exponent addition is right-cancellative (proved on the underlying arrays).
lemma mvDegrees_add_right_cancel {a b c : MvDegrees nvars} (h : a + c = b + c) : a = b := by
  have hd : a.degrees = b.degrees := by
    apply array_eq_of_toList_eq
    apply list_zipWith_add_right_cancel (lc := c.degrees.toList)
    · simp [a.correct, c.correct]
    · simp [b.correct, c.correct]
    · show List.zipWith (· + ·) a.degrees.toList c.degrees.toList
        = List.zipWith (· + ·) b.degrees.toList c.degrees.toList
      rw [← Array.toList_zipWith, ← Array.toList_zipWith]
      change (a + c).degrees.toList = (b + c).degrees.toList
      rw [h]
  obtain ⟨ad, hac, at_, hae⟩ := a
  obtain ⟨bd, hbc, bt, hbe⟩ := b
  subst hd
  simp only [MvDegrees.mk.injEq, true_and]
  rw [hae, hbe]

-- Addition by a fixed exponent is strictly monotone in the monomial order.
lemma mvDegrees_add_lt_add_left {i j₁ j₂ : MvDegrees nvars} (h : j₂ < j₁) : i + j₂ < i + j₁ := by
  rw [add_comm i j₂, add_comm i j₁]
  refine lt_of_le_of_ne (WOrdering.add_le_add (le_of_lt h)) ?_
  intro he
  exact (ne_of_lt h) (mvDegrees_add_right_cancel he)

-- Multiplying a sorted term-list by a single monomial `(i, a)` keeps it sorted (the map
-- `t ↦ (i + t.1, a * t.2)` is strictly order-preserving on degrees).
omit [DecidableEq R] in
lemma monomialMul_sorted (i : MvDegrees nvars) (a : R) (y : MvSparsePoly R nvars) :
    (y.terms.map (fun t => (i + t.1, a * t.2))).Pairwise (·.1 > ·.1) :=
  List.Pairwise.map _ (fun _ _ hpq => mvDegrees_add_lt_add_left hpq) y.sorted

/-- `monomialMul i a y = (a · Xⁱ) * y`, computed directly (no re-sort, since the result is
already sorted). The building block of the fast Johnson/Monagan–Pearce multiplication. -/
def monomialMul (i : MvDegrees nvars) (a : R) (y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofSortedList (y.terms.map (fun t => (i + t.1, a * t.2))) (monomialMul_sorted i a y)

private def balancedSumGo : ℕ → List (MvSparsePoly R nvars) → MvSparsePoly R nvars
  | _, [] => 0
  | _, [p] => p
  | 0, l => l.foldl (· + ·) 0
  | fuel + 1, l => balancedSumGo fuel (l.take (l.length / 2)) +
    balancedSumGo fuel (l.drop (l.length / 2))

/-- Sum a list of polynomials by a balanced (divide-and-conquer)
 -- merge tree, so building an
`n`-term result costs `O(n log #summands)` merges instead of the
 -- `O(n · #summands)` of a left
fold. -/
def balancedSum (l : List (MvSparsePoly R nvars)) : MvSparsePoly R nvars :=
  balancedSumGo l.length l

/-- Fast multiplication by a **balanced merge** (mergesort tree): multiply `y` by each term of `x`
(each product `monomialMul tᵢ y` is already sorted), then merge the `#x` sorted rows pairwise in a
balanced tree. Same result as the reference `mulCore` (each polynomial has a unique sorted normal
form), but `O(#x · #y · log #x)` *time* instead of generating all `#x·#y` products and sorting
them.

Relation to Davenport's notes (Ch. 2, "What are polynomials?"): he notes the sorted approach is
`O(mn log m)`, and that "naïve construction of all the terms followed by sorting would take `O(mn)`
space ... we can do better with heapsort [Joh74]". This `balancedSum` achieves the *time* bound but
NOT the space bound — it still materialises all `#x` rows (so peak `O(#x·#y)`). A true Johnson heap
of size `#x` would stream the output in `O(#x)` working space. For multiplication the rows have
equal size `#y`, so the balanced merge is efficient (unlike the division case — see the note on
`normalForm`); the only thing a real heap would buy here is peak memory, so we keep the simpler,
verifiable merge. -/
def mulFast (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  balancedSum (x.terms.map (fun t => monomialMul t.1 t.2 y))

/-- Runtime-only **packed** multiplication — the Davenport / Monagan–Pearce exponent-packing trick.

`mulFast` represents each monomial as an `Array ℕ`, so every one of the `#x·#y` partial products
allocates a fresh boxed-`Nat` array and every merge comparison walks an array. When the product's
exponents are small enough that each variable fits in a `b`-bit field with `nvars·b ≤ 64`, we instead
encode a whole monomial as a single `UInt64` (variable `0` in the most-significant field). Then:

* the monomial order is plain `UInt64` comparison (`lexorder` is lex with var `0` most significant),
* monomial multiplication `i + j` is a single `UInt64` add (fields can't carry, since each field sum
  `≤ 2·maxDeg < 2^b`).

So the whole `#x·#y` inner loop runs on unboxed machine words; we merge/dedup in packed space and
only unpack the `≤ #product` survivors back to `MvDegrees`. When the exponents don't fit in 64 bits
(or `nvars = 0`) we fall back to `mulFast`. This is the *time*-constant-factor win Davenport's notes
point at (Ch. 2, exponent encoding); same result as `mulCore` (wired via `@[implemented_by]`), and
cross-checked against `mulFast`/`mulCore` by `#guard`. -/
def mulPacked (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  if nvars = 0 then mulFast x y else
  Id.run do
    -- 1. largest exponent occurring in either operand
    let mut maxDeg : ℕ := 0
    for t in x.terms do
      for e in t.1.degrees do
        if e > maxDeg then maxDeg := e
    for t in y.terms do
      for e in t.1.degrees do
        if e > maxDeg then maxDeg := e
    -- 2. field width `b` with `2^b > 2·maxDeg` (so a product field never carries into the next)
    let fieldBound : ℕ := 2 * maxDeg + 1
    let b : ℕ := Nat.log2 fieldBound + 1
    -- 3. bail to the array path when a monomial won't fit in a 64-bit word
    if nvars * b > 64 then
      return mulFast x y
    let bb : UInt64 := b.toUInt64
    let mask : UInt64 := (1 <<< bb) - 1
    -- pack a monomial into one `UInt64`, variable 0 in the most-significant field
    let pack : MvDegrees nvars → UInt64 := fun d => Id.run do
      let mut k : UInt64 := 0
      for e in d.degrees do
        k := (k <<< bb) ||| (e.toUInt64 &&& mask)
      return k
    -- unpack a key back to a genuine `MvDegrees` (proof fields discharged by construction)
    let unpack : UInt64 → MvDegrees nvars := fun k =>
      let degs : Array ℕ := Array.ofFn (n := nvars) (fun j : Fin nvars =>
        ((k >>> (((nvars - 1 - j.val) * b).toUInt64)) &&& mask).toNat)
      { degrees := degs, correct := by simp [degs], totalDegree := degs.foldl (· + ·) 0,
        totalDegree_eq := rfl }
    -- 4. all `#x·#y` partial products as `(packed key, coeff)` — the hot loop, now on machine words
    let yk : Array (UInt64 × R) := (y.terms.map (fun t => (pack t.1, t.2))).toArray
    let mut prods : Array (UInt64 × R) := Array.mkEmpty (x.terms.length * yk.size)
    for t in x.terms do
      let xkey := pack t.1
      let xc := t.2
      for p in yk do
        prods := prods.push (xkey + p.1, xc * p.2)
    -- 5. sort by key (descending) and merge equal keys, all on `UInt64`
    let sorted := prods.qsort (fun a c => decide (c.1 < a.1))
    let mut merged : Array (UInt64 × R) := Array.mkEmpty sorted.size
    for p in sorted do
      match merged.back? with
      | some q => if q.1 == p.1 then merged := merged.set! (merged.size - 1) (p.1, q.2 + p.2)
                  else merged := merged.push p
      | none => merged := merged.push p
    -- 6. drop cancelled terms and unpack the survivors (only `≤ #product` array allocations)
    let mut out : List (MvDegrees nvars × R) := []
    for p in merged do
      if p.2 ≠ 0 then out := (unpack p.1, p.2) :: out
    return ofList out

/-- Reference multiplication: generate every product term,
--then sort/dedup/filter via `ofList`.
The proofs use this; compiled code uses the equivalent
--`mulFast` via `@[implemented_by]`. -/
@[implemented_by mulPacked]
def mulCore (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofList do
    let (i, a) ← x.terms
    let (j, b) ← y.terms
    return (i + j, a * b)

instance : Mul (MvSparsePoly R nvars) where
  mul := mulCore

instance : Neg (MvSparsePoly R nvars) where
  neg x := C (-1) * x


-- -- 1. Native Computational Negation (O(N) time, lightning fast)
-- def negCore (x : List (MvDegrees nvars × R)) : List (MvDegrees nvars × R) :=
--   x.map (fun p => (p.1, -p.2))

-- -- 2. Mapping doesn't change degrees, so the list stays perfectly sorted
-- lemma negCore_sorted {x : List (MvDegrees nvars × R)} (h : x.Pairwise (·.1 > ·.1)) :
--     (negCore x).Pairwise (·.1 > ·.1) := by
--   induction x with
--   | nil => exact List.Pairwise.nil
--   | cons head tail ih =>
--     simp only [negCore, List.map_cons, List.pairwise_cons] at h ⊢
--     constructor
--     · intro p hp
--       -- Extract the original element before the map
--       rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
--       subst heq
--       exact h.1 p' hp'
--     · exact ih h.2

-- -- 3. Negating non-zero elements keeps them non-zero
-- lemma negCore_filter (x : List (MvDegrees nvars × R)) (hx : ∀ p ∈ x, p.2 ≠ 0) :
--     (negCore x).filter (·.2 ≠ 0) = negCore x := by
--   apply List.filter_eq_self.mpr
--   intro p hp
--   rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
--   subst heq
--   have h_not_zero := hx p' hp'
--   grind

-- -- 4. Adding a polynomial to its negation perfectly cancels out to an empty list
-- lemma addCore_negCore (x : List (MvDegrees nvars × R)) :
--     addCore x (negCore x) = [] := by
--   induction x with
--   | nil => simp [addCore, negCore]
--   | cons head tail ih =>
--     rcases head with ⟨i, a⟩
--     change addCore ((i, a) :: tail) ((i, -a) :: negCore tail) = []

--     -- Expand the addCore logic for equal degrees
--     have h_not_lt : ¬(i < i) := lt_irrefl i
--     simp only [h_not_lt, addCore]

--     -- Lean knows that `a + -a = 0`
--     have h_zero : a + -a = 0 := by simp
--     simp only [h_zero, ite_true]

--     -- Apply induction to the tail
--     exact ih

-- ==========================================
-- BATCH 2: NATIVE NEGATION (FIXED)
-- ==========================================

-- ==========================================
-- BATCH 2: NATIVE NEGATION (FIXED FOR LEAN 4)
-- ==========================================

-- 1. Native Computational Negation (O(N) time, lightning fast)
def negCore (x : List (MvDegrees nvars × R)) : List (MvDegrees nvars × R) :=
  x.map (fun p => (p.1, -p.2))

-- 2. Mapping doesn't change degrees, so the list stays perfectly sorted
omit [DecidableEq R] in
lemma negCore_sorted {x : List (MvDegrees nvars × R)} (h : x.Pairwise (·.1 > ·.1)) :
    (negCore x).Pairwise (·.1 > ·.1) := by
  induction x with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
    simp only [negCore, List.map_cons, List.pairwise_cons] at h ⊢
    constructor
    · intro p hp
      rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
      subst heq
      exact h.1 p' hp'
    · exact ih h.2

-- 3. Negating non-zero elements keeps them non-zero
lemma negCore_filter (x : List (MvDegrees nvars × R)) (hx : ∀ p ∈ x, p.2 ≠ 0) :
    (negCore x).filter (·.2 ≠ 0) = negCore x := by
  apply List.filter_eq_self.mpr
  intro p hp
  rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
  subst heq
  have h_not_zero := hx p' hp'
  grind
-- 4. Adding a polynomial to its negation perfectly cancels out to an empty list
lemma addCore_negCore (x : List (MvDegrees nvars × R)) :
    addCore x (negCore x) = [] := by
  induction x with
  | nil => simp [addCore, negCore]
  | cons head tail ih =>
    rcases head with ⟨i, a⟩
    unfold addCore

    have h_not_lt : ¬(i < i) := lt_irrefl i
    simp only [negCore]

    -- ✨ THE FIX: Lean 4 uses add_neg_cancel instead of add_right_neg ✨
    have h_zero : a + -a = 0 := add_neg_cancel a
    aesop


-- 5. Define the Neg instance BEFORE the lemma so it knows what `-p` means
instance : Neg (MvSparsePoly R nvars) where
  neg p := ofSortedList (negCore p.terms) (negCore_sorted p.sorted)


-- 1. Helper: addCore handles empty lists cleanly
lemma addCore_nil_left (x : List (MvDegrees nvars × R)) : addCore [] x = x := by
  cases x <;> simp [addCore]

lemma addCore_nil_right (x : List (MvDegrees nvars × R)) : addCore x [] = x := by
  cases x <;> simp [addCore]

-- 2. Helper: addCore is mathematically commutative on lists
lemma addCore_comm : ∀ (x y : List (MvDegrees nvars × R)),
    addCore x y = addCore y x
  | [], yy => by cases yy <;> simp [addCore]
  | (i, a) :: x, [] => by simp [addCore] -- FIX: Forced computation instead of `rfl`
  | (i, a) :: x, (j, b) :: y => by
    -- FIX: Use unfold instead of change. This perfectly exposes both sides of
    -- the equation safely without worrying about the equation compiler's internal naming.
    unfold addCore

    -- Split the 3 mathematical realities using bulletproof LinearOrder theorems
    rcases lt_trichotomy i j with hlt | heq | hgt
    · -- Case: i < j
      have h_not_ji : ¬(j < i) := fun h => lt_irrefl i (lt_trans hlt h)
      simp only [hlt, h_not_ji, ite_true, ite_false]
      rw [addCore_comm ((i, a) :: x) y]

    · -- Case: i = j
      subst heq
      have h_not_lt : ¬(i < i) := lt_irrefl i
      -- FIX: By adding `add_comm` and `addCore_comm` to the simp list,
      -- Lean automatically beta-reduces the `(fun c => ...)(a + b)` block!
      simp only [h_not_lt, ite_false, add_comm a b, addCore_comm x y]

    · -- Case: j < i
      have h_not_ij : ¬(i < j) := fun h => lt_irrefl j (lt_trans hgt h)
      simp only [hgt, h_not_ij, ite_true, ite_false]
      rw [addCore_comm x ((j, b) :: y)]
termination_by x y => x.length + y.length

-- 3. Bridge: The `ofSortedList` constructor does not change an
-- already valid polynomial.
lemma filter_nonzero_eq_self (p : MvSparsePoly R nvars) :
    p.terms.filter (·.2 ≠ 0) = p.terms := by
  apply List.filter_eq_self.mpr
  intro x hx
  -- Use `decide_eq_true` to convert the Prop proof into a Bool proof!
  exact decide_eq_true (p.nonzero x hx)

-- 4. The 3 Addition CommRing Proofs
lemma poly_zero_add (p : MvSparsePoly R nvars) : 0 + p = p := by
  apply MvSparsePoly.ext
  change (addCore [] p.terms).filter (·.2 ≠ 0) = p.terms
  rw [addCore_nil_left]
  exact filter_nonzero_eq_self p

lemma poly_add_zero (p : MvSparsePoly R nvars) : p + 0 = p := by
  apply MvSparsePoly.ext
  change (addCore p.terms []).filter (·.2 ≠ 0) = p.terms
  rw [addCore_nil_right]
  exact filter_nonzero_eq_self p

lemma poly_add_comm (p q : MvSparsePoly R nvars) : p + q = q + p := by
  apply MvSparsePoly.ext
  change (addCore p.terms q.terms).filter (·.2 ≠ 0) =
    (addCore q.terms p.terms).filter (·.2 ≠ 0)
  rw [addCore_comm]

-- 6. The final Polynomial theorem now natively proves `-p + p = 0`
lemma poly_add_left_neg (p : MvSparsePoly R nvars) : -p + p = 0 := by
  apply MvSparsePoly.ext

  -- Expose the addition definition
  change (addCore ((negCore p.terms).filter (·.2 ≠ 0)) p.terms).filter
    (·.2 ≠ 0) = []

  -- Drop the filter on the negative terms
  rw [negCore_filter p.terms p.nonzero]

  -- Explicitly flip `addCore (-p) p` into `addCore p (-p)`
  rw [addCore_comm (negCore p.terms) p.terms]

  -- Use our cancellation helper
  rw [addCore_negCore p.terms]
  rfl


--1. Helper: `ofList` on an empty list safely evaluates to the `0` polynomial
lemma ofList_nil : ofList (R := R) (nvars := nvars) [] = 0 := by
  apply MvSparsePoly.ext
  simp [ofList]
  simp [ofSortedList, dedupList]
  --unfold terms
  rfl

-- 2. 0 * p = 0
lemma poly_zero_mul (p : MvSparsePoly R nvars) : 0 * p = 0 := by
  -- `0.terms` is `[]`. The outer loop of our `mul` macro instantly evaluates to `[]`.
  change ofList [] = 0
  exact ofList_nil

-- 3. p * 0 = 0
lemma poly_mul_zero (p : MvSparsePoly R nvars) : p * 0 = 0 := by
  -- The inner loop of `mul` evaluates to `[]`.
  change ofList (p.terms.flatMap (fun _ => [])) = 0

  -- Quick induction to prove that flatMapping `[]` over any list results in `[]`
  have h_bind : p.terms.flatMap
    (fun _ => ([] : List (MvDegrees nvars × R))) = [] := by
    induction p.terms with
    | nil => rfl
    | cons head tail ih => exact ih

  rw [h_bind]
  exact ofList_nil


-- ==========================================
-- BATCH 4.2: IDENTITY AND INJECTIVITY
-- ==========================================

-- ==========================================
-- BATCH 4.1: THE MATHLIB FINSUPP BRIDGE
-- ==========================================
open MvPolynomial

-- ==========================================
-- BATCH 4.1: THE MATHLIB FINSUPP BRIDGE
-- ==========================================
open MvPolynomial

lemma toFinsupp_inj {i j : MvDegrees nvars} :
    MvDegrees.toFinsupp i = MvDegrees.toFinsupp j ↔ i = j := by
  constructor
  · intro h
    -- 1. First, prove the underlying arrays are identical
    have h_arr : i.degrees = j.degrees := by
      apply Array.ext
      · -- Sizes are equal because both must equal `nvars`
        exact i.correct.trans j.correct.symm
      · -- Elements are equal point-by-point via Finsupp equality
        intro v hv1 hv2
        have hv_fin : v < nvars := by aesop
        exact Finsupp.ext_iff.mp h ⟨v, hv_fin⟩

    -- 2. Because the arrays are identical, their folded sums MUST be identical
    have h_tot : i.totalDegree = j.totalDegree := by
      rw [i.totalDegree_eq, j.totalDegree_eq, h_arr]

    -- 3. With both data fields proven equal, unpack the structures and
    -- close the goal!
    cases i
    cases j
    simp_all

  · intro h
    rw [h]

lemma toFinsupp_add (i j : MvDegrees nvars) :
    MvDegrees.toFinsupp (i + j) =
    MvDegrees.toFinsupp i + MvDegrees.toFinsupp j := by
  ext v
  rw [Finsupp.add_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]

  -- 1. Unfold the generic `+` symbol into your specific MvDegrees addition logic
  dsimp only [HAdd.hAdd, Add.add]

  -- 2. At this point, Lean sees exactly what your addition function is doing
  -- (e.g., `Array.zipWith`, a recursive loop, etc.).
  -- We just need to tell `simp` to evaluate the array at index `v`.
  simp

lemma toFinsupp_zero :
    MvDegrees.toFinsupp (0 : MvDegrees nvars) = 0 := by
  ext v
  rw [Finsupp.zero_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]
  -- 1. Force Lean to see the constructor of the Zero instance
  -- This "rcases" trick is more powerful than simp for opaque instances
  have h_zero_def : (0 : MvDegrees nvars).degrees =
    (List.replicate nvars 0).toArray := by
    -- Point this exactly at your Zero definition for MvDegrees
    --unfold Zero.zero
    rfl
  simp only [h_zero_def]
  grind


-- Helper 1: toPoly of a constant SparsePoly is the constant MvPolynomial
theorem toPoly_C (r : R) : toPoly (C r : MvSparsePoly R nvars) =
    MvPolynomial.C r := by
  unfold C toPoly ofSortedList
  dsimp only
  by_cases hr : r = 0
  · -- Case: r = 0
    subst hr
    -- Because 0 ≠ 0 is false, the list natively filters to empty
    --change toPolyCore [] = MvPolynomial.C 0
    unfold toPolyCore
    grind
    --exact map_zero MvPolynomial.C

  · -- Case: r ≠ 0
    -- Because r ≠ 0 is true, the filter natively keeps the element
    have h_filter : ([(0, r)] : List (MvDegrees nvars × R)).filter (·.2 ≠ 0) = [(0, r)] := by
      simp [hr]
    rw [h_filter]

    -- Expose exactly one step of our polynomial translation
    change MvPolynomial.monomial (MvDegrees.toFinsupp 0) r +
      toPolyCore [] = MvPolynomial.C r
    unfold toPolyCore
    rw [add_zero]

    -- Translate our compiled Array 0 into Mathlib's Finsupp 0
    have h_zero : MvDegrees.toFinsupp (0 : MvDegrees nvars) = 0 := toFinsupp_zero
    aesop
    --rw [h_zero, MvPolynomial.C_eq_monomial]

-- Helper 1.5: The One Identity
lemma toPoly_one : toPoly (1 : MvSparsePoly R nvars) = 1 := by
  change toPoly (C 1 : MvSparsePoly R nvars) = 1
  rw [toPoly_C]
  exact map_one (MvPolynomial.C)

omit [DecidableEq R] in
theorem coeff_toPolyCore_of_degLt {n : MvDegrees nvars}
     (xs : List (MvDegrees nvars × R)) (h : degLt n xs) :
    MvPolynomial.coeff (MvDegrees.toFinsupp n) (toPolyCore xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    dsimp only [toPolyCore]
    -- FIX: Use the specific coefficient addition lemma
    rw [MvPolynomial.coeff_add]

    have h_deg : i < n := h (i, a) List.mem_cons_self
    have h_ne : i ≠ n := ne_of_lt h_deg

    -- Prove the Finsupps are not equal using our bridge
    have h_finsupp_ne : MvDegrees.toFinsupp i ≠ MvDegrees.toFinsupp n := by
      intro h_eq
      exact h_ne (toFinsupp_inj.mp h_eq)

    -- Now simplify the monomial coefficient
    rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne]

    -- Apply the inductive hypothesis
    have h_tl : degLt n tl := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [ih h_tl, zero_add]

-- Helper 3: The coefficient of the head of the list at its
-- own exponent `i` is exactly `a`.
omit [DecidableEq R] in
theorem coeff_toPolyCore_head {i : MvDegrees nvars} {a : R}
  (xs : List (MvDegrees nvars × R)) (h : degLt i xs) :
    MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) = a := by
  -- 1. Unfold the definition to see the addition
  dsimp only [toPolyCore]

  -- 2. Use 'simp only' instead of 'rw' for the addition.
  -- This is more robust for MvPolynomial coefficients.
  simp only [MvPolynomial.coeff_add]

  -- 3. Evaluate the coefficient of the monomial (which is exactly 'a')
  rw [MvPolynomial.coeff_monomial, if_pos rfl]

  -- 4. Evaluate the coefficient of the tail (which is 0 because i > all degrees in xs)
  rw [coeff_toPolyCore_of_degLt xs h, add_zero]

-- Helper 4: Extract `degLt` from `Pairwise`
omit [CommRing R] [DecidableEq R] in
lemma degLt_of_sorted_cons {i : MvDegrees nvars} {a : R}
  {xs : List (MvDegrees nvars × R)}
    (h : ((i, a) :: xs).Pairwise (·.1 > ·.1)) : degLt i xs :=
  fun x hx => (List.pairwise_cons.1 h).1 x hx

-- The Main Boss Fight (Exactly mirroring your univariate logic)
omit [DecidableEq R] in
theorem toPolyCore_injective_of_sorted : ∀ (l1 l2 : List (MvDegrees nvars × R)),
    l1.Pairwise (·.1 > ·.1) → l2.Pairwise (·.1 > ·.1) →
    (∀ x ∈ l1, x.2 ≠ 0) → (∀ x ∈ l2, x.2 ≠ 0) →
    toPolyCore l1 = toPolyCore l2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: ys, _, s2, _, nz2, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore []) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp j)
                   (toPolyCore ((j, b) :: ys)) := by
                    rw [heq]
    change 0 = _ at h_coeff
    rw [coeff_toPolyCore_head ys (degLt_of_sorted_cons s2)] at h_coeff
    have hb_nz := nz2 (j, b) List.mem_cons_self
    exact False.elim (hb_nz h_coeff.symm)
  | (i, a) :: xs, [], s1, _, nz1, _, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i)
                   (toPolyCore ((i, a) :: xs)) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp i)
                   (toPolyCore []) := by rw [heq]
    change _ = 0 at h_coeff
    rw [coeff_toPolyCore_head xs (degLt_of_sorted_cons s1)] at h_coeff
    have ha_nz := nz1 (i, a) List.mem_cons_self
    exact False.elim (ha_nz h_coeff)
  | (i, a) :: xs, (j, b) :: ys, s1, s2, nz1, nz2, heq => by
    have h_deg_x : degLt i xs := degLt_of_sorted_cons s1
    have h_deg_y : degLt j ys := degLt_of_sorted_cons s2
    obtain hij | rfl | hji := lt_trichotomy i j
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j)
                     (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((j, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head ys h_deg_y] at h_coeff
      have h_xs_j : degLt j xs := fun e he => lt_trans (h_deg_x e he) hij
      have h_lhs : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((i, a) :: xs)) = 0 := by
        dsimp only [toPolyCore]
        -- 1. Use simp only with the specific MvPolynomial lemma
        simp only [MvPolynomial.coeff_add]

        -- 2. Prove the degrees are distinct
        have h_finsupp_ne : MvDegrees.toFinsupp i ≠ MvDegrees.toFinsupp j := by
          intro h_eq
          exact (ne_of_lt hij) (toFinsupp_inj.mp h_eq)

        -- 3. Evaluate the monomial coefficient (0 because degrees don't match)
        rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne]

        -- 4. Evaluate the tail coefficient (0 by Helper 2)
        rw [coeff_toPolyCore_of_degLt xs h_xs_j, zero_add]
      rw [h_lhs] at h_coeff
      have hb_nz := nz2 (j, b) List.mem_cons_self
      exact False.elim (hb_nz h_coeff.symm)
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, b) :: ys)) := by
                     rw [heq]
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
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x] at h_coeff
      have h_ys_i : degLt i ys := fun e he => lt_trans (h_deg_y e he) hji
      have h_rhs : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) = 0 := by
        dsimp only [toPolyCore]
        -- 1. Use 'simp only' with the specific MvPolynomial lemma
        simp only [MvPolynomial.coeff_add]

        -- 2. Prove the degrees are distinct (i ≠ j)
        have h_finsupp_ne : MvDegrees.toFinsupp j ≠ MvDegrees.toFinsupp i := by
          intro h_eq
          exact (ne_of_lt hji) (toFinsupp_inj.mp h_eq)
        rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne]
        rw [coeff_toPolyCore_of_degLt ys h_ys_i, zero_add]
      rw [h_rhs] at h_coeff
      have ha_nz := nz1 (i, a) List.mem_cons_self
      exact False.elim (ha_nz h_coeff)

omit [DecidableEq R] in
lemma toPoly_injective : Function.Injective (toPoly (R := R) (nvars := nvars)) := by
  intro x y h
  ext1
  exact toPolyCore_injective_of_sorted x.terms y.terms x.sorted y.sorted x.nonzero y.nonzero h


-- ==========================================
-- BATCH 4.0: MULTIVARIATE BRIDGE HELPERS
-- ==========================================

-- Helper: Filtering out coefficients that are 0 doesn't change the MvPolynomial
theorem toPolyCore_filter_nonzero (l : List (MvDegrees nvars × R)) :
    toPolyCore (l.filter (·.2 ≠ 0)) = toPolyCore l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    simp only [List.filter_cons]
    split
    · next h_nonzero =>
      -- Case: a ≠ 0. Term is kept.
      unfold toPolyCore; rw [ih]
    · next h_zero =>
      -- Case: a = 0. Term is dropped.
      -- In MvPolynomial, monomial d 0 is 0.
      have ha0 : a = 0 := by aesop
      unfold toPolyCore
      rw [ha0, map_zero, zero_add]
      aesop

-- Lemma: addCore perfectly mirrors MvPolynomial addition
theorem toPolyCore_addCore : ∀ (x y : List (MvDegrees nvars × R)),
    toPolyCore (addCore x y) = toPolyCore x + toPolyCore y
  | [], yy => by simp [addCore, toPolyCore]
  | (i, a) :: x, [] => by simp [addCore, toPolyCore]
  | (i, a) :: x, (j, b) :: y => by
    simp only [addCore]
    rcases lt_trichotomy i j with hlt | heq | hgt

    · -- Case 1: i < j
      -- Build the proof that j < i is false manually
      have h_not_ji : ¬(j < i) := fun h_contra => lt_irrefl i (lt_trans hlt h_contra)
      simp only [hlt, ↓reduceIte]
      dsimp only [toPolyCore]
      rw [toPolyCore_addCore]
      simp only [toPolyCore]
      ring

    · -- Case 2: i = j
      subst heq
      -- Clear the trichotomy conditions
      simp only [lt_self_iff_false, ↓reduceIte]

      -- Explicitly split the `if a + b = 0` branch from your addCore definition
      split

      · -- Subcase 2.1: a + b = 0 (The term is dropped)
        next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore]

          -- Group the two monomials together
          have h_rearrange : (MvPolynomial.monomial (MvDegrees.toFinsupp i) a + toPolyCore x) +
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) b + toPolyCore y) =
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) a +
                              MvPolynomial.monomial (MvDegrees.toFinsupp i) b) +
                             (toPolyCore x + toPolyCore y) := by ring
          rw [h_rearrange]

          -- Combine them into a single monomial, apply a + b = 0, and clear it
          rw [← map_add, hab, map_zero, zero_add]

      · -- Subcase 2.2: a + b ≠ 0 (The merged term is kept)
        next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore]

          -- Distribute the combined coefficient into two separate monomials
          rw [map_add]

          -- The terms are now identical on both sides, just out of order
          ring

    · -- Case 3: j < i
      -- Build the proof that i < j is false manually
      have h_not_ij : ¬(i < j) := fun h_contra => lt_irrefl j (lt_trans hgt h_contra)
      simp only [h_not_ij, ↓reduceIte, hgt]
      dsimp only [toPolyCore]
      rw [toPolyCore_addCore]
      simp only [toPolyCore]

      ring
termination_by x y => x.length + y.length

lemma toPoly_add (a b : MvSparsePoly R nvars) : toPoly (a + b) = toPoly a + toPoly b := by
  unfold toPoly
  change toPolyCore ((addCore a.terms b.terms).filter (·.2 ≠ 0)) =
         toPolyCore a.terms + toPolyCore b.terms
  rw [toPolyCore_filter_nonzero]
  exact toPolyCore_addCore a.terms b.terms

-- 1. Sorting/Permuting the list doesn't change the polynomial
omit [DecidableEq R] in
theorem toPolyCore_perm {l1 l2 : List (MvDegrees nvars × R)} (h : l1.Perm l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => dsimp [toPolyCore]; rw [ih]
  | swap x y l => dsimp [toPolyCore]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- 2. mergeSort is just a permutation
omit [DecidableEq R] in
theorem toPolyCore_mergeSort (l : List (MvDegrees nvars × R))
  (r : (MvDegrees nvars × R) → (MvDegrees nvars × R) → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l :=
  toPolyCore_perm (l.mergeSort_perm r)

-- 3. Combining like-terms (dedupList) preserves the polynomial via the distributive law
omit [DecidableEq R] in
theorem toPolyCore_dedupList : ∀ (l : List (MvDegrees nvars × R)),
    toPolyCore (dedupList l) = toPolyCore l
  | [] => by simp [dedupList, toPolyCore]
  | [x] => by simp [dedupList, toPolyCore]
  | (i, a) :: (j, b) :: xs => by
      unfold dedupList
      split
      · next heq => -- Case: i = j, terms are merged
        subst heq
        rw [toPolyCore_dedupList ((i, a + b) :: xs)]
        dsimp [toPolyCore]
        rw [map_add] -- (a + b)X^i = aX^i + bX^i
        ring
      · next hneq => -- Case: i ≠ j, terms stay separate
        dsimp [toPolyCore]
        rw [toPolyCore_dedupList ((j, b) :: xs)]
        simp only [toPolyCore]

-- 4. THE MASTER BRIDGE: toPoly (ofList l) = toPolyCore l
theorem toPoly_ofList (l : List (MvDegrees nvars × R)) :
    toPoly (ofList l) = toPolyCore l := by
  -- ofList calls ofSortedList (which filters) on a sorted/deduplicated list
  unfold toPoly ofList ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero]
  rw [toPolyCore_dedupList]
  rw [toPolyCore_mergeSort]

-- Helper 1: Multiplying a list of terms by a single monomial (i, a)
omit [DecidableEq R] in
theorem toPolyCore_monomial_mul (l : List (MvDegrees nvars × R)) (i : MvDegrees nvars) (a : R) :
    toPolyCore (l.map fun ⟨j, b⟩ => (i + j, a * b)) =
    (MvPolynomial.monomial (MvDegrees.toFinsupp i) a) * toPolyCore l := by
  induction l with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨j, b⟩
    dsimp [toPolyCore]
    -- Distribute: monomial i a * (monomial j b + toPolyCore tl)
    rw [mul_add, ← ih]
    congr 1
    -- Use the bridge: i + j in MvDegrees is addition in Finsupp
    rw [MvPolynomial.monomial_mul, toFinsupp_add, mul_comm a b, add_comm]


theorem toPolyCore_ofList_terms (l : List (MvDegrees nvars × R)) :
    toPolyCore (ofList l).terms = toPolyCore l := by
  unfold ofList ofSortedList
  dsimp
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

-- Helper 1: toPolyCore distributes over list append
omit [DecidableEq R] in
theorem toPolyCore_append (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    dsimp [toPolyCore]
    rw [ih, add_assoc]

-- 2. New FlatMap Monomial Helper (Using `change` to outsmart the elaborator)
omit [DecidableEq R] in
theorem toPolyCore_monomial_mul_flatMap (l : List (MvDegrees nvars × R))
      (i : MvDegrees nvars) (a : R) :
    toPolyCore (l.flatMap fun x => [(i + x.1, a * x.2)]) =
    (MvPolynomial.monomial (MvDegrees.toFinsupp i) a) * toPolyCore l := by
  induction l with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    change (MvPolynomial.monomial (MvDegrees.toFinsupp (i + hd.1))) (a * hd.2) +
           toPolyCore (tl.flatMap fun x => [(i + x.1, a * x.2)]) = _
    rw [ih]
    erw [mul_add]
    congr 1
    rw [MvPolynomial.monomial_mul, toFinsupp_add, mul_comm a hd.2, add_comm]

-- 3. New Master FlatMap Helper
omit [DecidableEq R] in
theorem toPolyCore_mul_flatMap (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1.flatMap fun x => l2.flatMap fun y => [(x.1 + y.1, x.2 * y.2)]) =
    toPolyCore l1 * toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    change toPolyCore ((l2.flatMap fun y => [(hd.1 + y.1, hd.2 * y.2)]) ++
                       (tl.flatMap fun x => l2.flatMap fun y => [(x.1 + y.1, x.2 * y.2)])) = _

    rw [toPolyCore_append]
    rw [toPolyCore_monomial_mul_flatMap]
    rw [ih]

    dsimp [toPolyCore]
    rw [add_mul]

lemma toPoly_mul (a b : MvSparsePoly R nvars) :
    toPoly (a * b) = toPoly a * toPoly b := by
  unfold toPoly
  dsimp [HMul.hMul, Mul.mul, mulCore]
  rw [toPolyCore_ofList_terms]
  -- Use exact with the new _flatMap theorem
  exact toPolyCore_mul_flatMap a.terms b.terms


instance : CommRing (MvSparsePoly R nvars) where
  -- 1. The Addition Foundations
  add := (·+·)
  zero := 0
  zero_add := poly_zero_add
  add_zero := poly_add_zero
  add_comm := poly_add_comm

  -- 2. The Negation Foundations
  neg := (-·)
  neg_add_cancel := poly_add_left_neg -- (This is the Lean 4 name for add_left_neg!)

  -- 3. The Zero Multiplication Foundations
  mul := (·*·)
  one := 1
  zero_mul := poly_zero_mul
  mul_zero := poly_mul_zero

  nsmul := nsmulRec

  zsmul := zsmulRec
  nsmul_zero := by intros; rfl

  nsmul_succ := by intros; rfl

  zsmul_zero' := by intros; rfl

  zsmul_succ' := by intros; rfl

  natCast n := nsmulRec n 1
  natCast_zero := rfl
  natCast_succ := by intros; rfl
  zsmul_neg' := by intros; rfl
  add_assoc a b c := toPoly_injective (by simp only [toPoly_add, add_assoc])
  mul_assoc a b c := toPoly_injective (by simp only [toPoly_mul, mul_assoc])
  mul_comm a b := toPoly_injective (by simp only [toPoly_mul, mul_comm])
  left_distrib a b c := toPoly_injective (by simp only [toPoly_add, toPoly_mul, left_distrib])
  right_distrib a b c := toPoly_injective (by simp only [toPoly_add, toPoly_mul, right_distrib])
  one_mul a := toPoly_injective (by simp only [toPoly_mul, toPoly_one, one_mul])
  mul_one a := toPoly_injective (by simp only [toPoly_mul, toPoly_one, mul_one])



--#print AddMonoidWithOne

-- instance : Algebra R (MvSparsePoly R nvars) := by
--   refine' { toFun := C, smul := fun a r => C a * r, ..} <;> sorry
omit [DecidableEq R] in
lemma toPoly_zero : toPoly (0 : MvSparsePoly R nvars) = 0 := rfl
-- First, we bundle your `C` constructor into a formal RingHom
def C_hom : R →+* MvSparsePoly R nvars where
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
instance : Algebra R (MvSparsePoly R nvars) where
  smul r p := C r * p
  algebraMap := C_hom
  commutes' r p := mul_comm (C r) p
  smul_def' _ _ := rfl

-- instance : Algebra R (MvSparsePoly R nvars) := by
--   refine' { smul_def' := sorry, smul := fun a r => C a * r, ..} <;> sorry

class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

/-For algebra we use :-/
def multidegree (a : MvSparsePoly R nvars) : MvDegrees nvars :=
  (a.terms.headD (0, 0)).1

/- For proofs, we use : -/
def totalDegree (a : MvSparsePoly R nvars) : ℕ :=
  (a.terms.headD (0, 0)).1.totalDegree

-- def degree (a : MvSparsePoly R nvars) : ℕ := (a.terms.headD (0, 0)).1

-- def degree (a : MvSparsePoly R nvars) : MvDegrees nvars :=
--   (a.terms.headD (0, 0)).1

def degree (a : MvSparsePoly R nvars) : ℕ := (a.terms.headD (0, 0)).1.totalDegree

instance : Sub (MvDegrees nvars) where
  sub a b := {
    -- Point-wise subtraction of the exponent arrays
    degrees := Array.zipWith (· - ·) a.degrees b.degrees
    correct := by simp [a.correct, b.correct]
    -- Calculate the new total degree of the subtracted array
    totalDegree := (Array.zipWith (· - ·) a.degrees b.degrees).foldl (· + ·) 0
    totalDegree_eq := rfl
  }

def sparseMonomial (d : MvDegrees nvars) (r : R) : MvSparsePoly R nvars :=
  ofSortedList [(d, r)] (by simp)

def MvDegrees.divides (a b : MvDegrees nvars) : Bool :=
  Array.zipWith (fun x y => decide (x ≤ y)) a.degrees b.degrees |>.all id


-- 2. The Cancel Lemma (No shadow variables, just Field R)

-- `0` is the minimum degree. Exposed here, before `WOrdering` is shadowed by the
-- redefinition below (after which `WOrdering.zero_le` would refer to the new class,
-- which has no global instance).
lemma mvDegrees_zero_le (i : MvDegrees nvars) : (0 : MvDegrees nvars) ≤ i := WOrdering.zero_le

-- Addition is monotone in the monomial order. Exposed before the shadowing redefinition.
lemma mvDegrees_add_le_add {x y z : MvDegrees nvars} (h : x ≤ y) : x + z ≤ y + z :=
  WOrdering.add_le_add h

-- -- 1. Define the custom typeclass mentioned in the paper
-- class Wordering (nvars : ℕ) where
--   lt : MvDegrees nvars → MvDegrees nvars → Prop
--   wf : WellFounded lt


-- (The `WOrdering` class with its `wf` field is now defined once, above, with the global
-- lexicographic instance `instWOrdering` discharging `wf` via `mvDegrees_lex_wf`.)

-- The well-founded relation on `MvDegrees` used for termination (`a < b` in the monomial
-- order). High priority so Lean does not fall back to `sizeOf`.
instance (priority := high) mvDegreesWF {nvars : ℕ} :
    WellFoundedRelation (MvDegrees nvars) where
  rel := (· < ·)
  wf := WOrdering.wf

-- The termination relation for `MvSparsePoly`: compare by `(multidegree, #terms)` lexically.
-- Built with the `invImage` combinator so `rel` and `wf` are tied together automatically.
local instance (priority := high) customPolyWF :
    WellFoundedRelation (MvSparsePoly R nvars) :=
  invImage (fun (p : MvSparsePoly R nvars) => (p.multidegree, p.terms.length)) inferInstance

-- Helper 1: Filtering a list for a condition never increases its length.
lemma length_filter_le {α} (p : α → Bool) (l : List α) : (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons]
    split
    · -- Kept the element: length increases by 1 on both sides
      simp only [List.length_cons]
      omega
    · -- Dropped the element: left side stays same, right side increases
      simp only [List.length_cons]
      omega

-- Helper 2: The length of `ofSortedList` is always ≤ the length of the raw list.
lemma ofSortedList_length_le (l : List (MvDegrees nvars × R)) (h) :
  (ofSortedList l h).terms.length ≤ l.length := by
  -- Because `terms` is definitionally just a filter, we apply Helper 1 directly!
  exact length_filter_le (fun p => decide (p.2 ≠ 0)) l

lemma addCore_cancel_head (i : MvDegrees nvars) (x : R) (as bs : List (MvDegrees nvars × R)) :
  addCore ((i, x) :: as) ((i, -x) :: bs) = addCore as bs := by
  -- 1. Unfold addCore ONLY on the left-hand side
  conv =>
    lhs
    unfold addCore

  -- 2. Provide our mathematical facts
  have h_not_lt : ¬(i < i) := lt_irrefl i
  have h_zero : x + -x = 0 := add_neg_cancel x

  -- 3. With the Ghost Instance gone, simp easily crushes the if/else logic!
  simp only [h_not_lt, h_zero, ite_false, ite_true]


-- Helper 2: The Master Bridge Lemma!
omit [DecidableEq R] in
lemma lex_drop_of_degLt_with_hA
  {a : MvSparsePoly R nvars} {i : MvDegrees nvars} {x : R} {as}
  (hA : a.terms = (i, x) :: as)
  {l : List (MvDegrees nvars × R)}
  (h_deg : degLt i l) :
  Prod.Lex (fun (u v : MvDegrees nvars) => u < v) (fun (u v : ℕ) => u < v)
    ((l.headD (0, 0)).1, l.length) (i, a.terms.length) := by
  cases l with
  | nil =>
    -- Case 1: The remainder list is completely empty (multidegree is 0)
    rcases lt_trichotomy (0 : MvDegrees nvars) i with hlt | heq | hgt
    · exact Prod.Lex.left _ _ hlt
    · subst heq
      -- If i = 0, we check the list lengths!
      apply Prod.Lex.right
      rw [hA]
      simp only [List.length_cons]
      aesop
    · -- `i < 0` is impossible since `0` is the minimum degree.
      exact absurd hgt (not_lt.mpr (mvDegrees_zero_le i))
  | cons hd tl =>
    -- Case 2: The remainder list is NOT empty.
    have h_hd_lt : hd.1 < i := h_deg hd List.mem_cons_self
    exact Prod.Lex.left _ _ h_hd_lt

-- `toPolyCore` of a negated term-list is the negation.
omit [DecidableEq R] in
lemma toPolyCore_negCore (l : List (MvDegrees nvars × R)) :
    toPolyCore (negCore l) = - toPolyCore l := by
  induction l with
  | nil => change toPolyCore [] = -toPolyCore []; rw [toPolyCore, neg_zero]
  | cons hd tl ih =>
    obtain ⟨d, r⟩ := hd
    change MvPolynomial.monomial (MvDegrees.toFinsupp d) (-r) + toPolyCore (negCore tl)
       = - (MvPolynomial.monomial (MvDegrees.toFinsupp d) r + toPolyCore tl)
    rw [ih, map_neg]
    ring

lemma toPoly_neg (p : MvSparsePoly R nvars) : toPoly (-p) = - toPoly p := by
  change toPolyCore ((negCore p.terms).filter (·.2 ≠ 0)) = - toPolyCore p.terms
  rw [toPolyCore_filter_nonzero, toPolyCore_negCore]

lemma toPoly_sub (p q : MvSparsePoly R nvars) : toPoly (p - q) = toPoly p - toPoly q := by
  rw [sub_eq_add_neg, toPoly_add, toPoly_neg, ← sub_eq_add_neg]

-- `toPoly` of a single monomial is the corresponding `MvPolynomial.monomial`.
lemma toPoly_sparseMonomial (d : MvDegrees nvars) (r : R) :
    toPoly (sparseMonomial d r) = MvPolynomial.monomial (MvDegrees.toFinsupp d) r := by
  change toPolyCore (([(d, r)]).filter (·.2 ≠ 0)) = MvPolynomial.monomial (MvDegrees.toFinsupp d) r
  rw [toPolyCore_filter_nonzero]
  simp only [toPolyCore, add_zero]

-- `divides j i` gives the pointwise exponent inequality.
lemma divides_pointwise {i j : MvDegrees nvars} (h : MvDegrees.divides j i = true) (k : ℕ)
    (hk : k < nvars) :
    j.degrees[k]'(by rw [j.correct]; exact hk) ≤ i.degrees[k]'(by rw [i.correct]; exact hk) := by
  unfold MvDegrees.divides at h
  rw [Array.all_eq_true] at h
  have hk' : k < (Array.zipWith (fun x y => decide (x ≤ y)) j.degrees i.degrees).size := by
    rw [Array.size_zipWith]; simp [i.correct, j.correct, hk]
  have hb := h k hk'
  rw [Array.getElem_zipWith] at hb
  simpa using hb

-- The key arithmetic identity: if `j` divides `i` then `(i - j) + j = i`. Proved by
-- transporting through `toFinsupp` (injective) to avoid array `foldl` reasoning.
lemma toFinsupp_sub_add {i j : MvDegrees nvars} (h : MvDegrees.divides j i = true) :
    MvDegrees.toFinsupp i = MvDegrees.toFinsupp (i - j) + MvDegrees.toFinsupp j := by
  ext v
  rw [Finsupp.add_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]
  rw [Fin.getElem_fin, Fin.getElem_fin, Fin.getElem_fin]
  change i.degrees[(v : ℕ)] = (Array.zipWith (· - ·) i.degrees j.degrees)[(v : ℕ)] + _
  rw [Array.getElem_zipWith]
  have := divides_pointwise h v v.2
  grind

lemma MvDegrees.sub_add_cancel_of_divides {i j : MvDegrees nvars}
    (h : MvDegrees.divides j i = true) : (i - j) + j = i := by
  apply toFinsupp_inj.mp
  rw [toFinsupp_add]
  exact (toFinsupp_sub_add h).symm

-- If `(d, v)` is a (sorted) term, then the `toPolyCore` coefficient at `d` is exactly `v`.
omit [DecidableEq R] in
theorem coeff_toPolyCore_mem {d : MvDegrees nvars} {v : R} {l : List (MvDegrees nvars × R)}
    (hsorted : l.Pairwise (·.1 > ·.1)) (hmem : (d, v) ∈ l) :
    MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPolyCore l) = v := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨e, w⟩ := hd
    rw [List.mem_cons] at hmem
    rcases hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ : d = e ∧ v = w := Prod.ext_iff.mp heq
      exact coeff_toPolyCore_head tl (degLt_of_sorted_cons hsorted)
    · have hd_lt : d < e := (List.pairwise_cons.mp hsorted).1 (d, v) htl
      dsimp only [toPolyCore]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial]
      have hne : MvDegrees.toFinsupp e ≠ MvDegrees.toFinsupp d := fun he =>
        (ne_of_lt hd_lt) (toFinsupp_inj.mp he).symm
      rw [if_neg hne, zero_add]
      exact ih (List.pairwise_cons.mp hsorted).2 htl

-- `ofList` never increases the maximum degree.
lemma ofList_degLe {n : MvDegrees nvars} (l : List (MvDegrees nvars × R))
    (h : ∀ p ∈ l, p.1 ≤ n) : ∀ p ∈ (ofList l).terms, p.1 ≤ n := by
  intro p hp
  have hp' : p ∈ dedupList (l.mergeSort (fun a b => decide (b.1 ≤ a.1))) :=
    List.mem_of_mem_filter hp
  refine dedupList_bound (l.mergeSort (fun a b => decide (b.1 ≤ a.1))) n ?_ p hp'
  intro q hq
  exact h q ((l.mergeSort_perm _).mem_iff.mp hq)

-- Every term of `sparseMonomial (i-j) c * b` has degree `≤ i` (when `j ∣ i` and `j` is
-- the leading degree of `b`).
lemma mul_sparseMonomial_degLe {b : MvSparsePoly R nvars} {i j : MvDegrees nvars} {c y : R} {bs}
    (hB : b.terms = (j, y) :: bs) (hDiv : MvDegrees.divides j i = true) :
    ∀ p ∈ (sparseMonomial (i - j) c * b).terms, p.1 ≤ i := by
  have hqb_le : ∀ q ∈ b.terms, q.1 ≤ j := by
    intro q hq; rw [hB] at hq
    rcases List.mem_cons.mp hq with h | h
    · rw [h]
    · exact le_of_lt ((List.pairwise_cons.mp (hB ▸ b.sorted)).1 q h)
  have hterms : (sparseMonomial (i - j) c * b).terms =
      (ofList ((sparseMonomial (i - j) c).terms.flatMap
        fun p => b.terms.flatMap fun q => [(p.1 + q.1, p.2 * q.2)])).terms := rfl
  rw [hterms]
  apply ofList_degLe
  intro p hp
  simp only [List.mem_flatMap, List.mem_singleton] at hp
  obtain ⟨pc, hpc, qb, hqb, rfl⟩ := hp
  have hpc1 : pc.1 = i - j := by
    have hpc' : pc ∈ ([((i - j : MvDegrees nvars), c)].filter (·.2 ≠ 0)) := hpc
    have hmem : pc ∈ [((i - j : MvDegrees nvars), c)] := List.mem_of_mem_filter hpc'
    rw [List.mem_singleton] at hmem; rw [hmem]
  change pc.1 + qb.1 ≤ i
  rw [hpc1]
  calc (i - j) + qb.1 ≤ (i - j) + j := by
          rw [add_comm (i - j) qb.1, add_comm (i - j) j]
          exact mvDegrees_add_le_add (hqb_le qb hqb)
       _ = i := MvDegrees.sub_add_cancel_of_divides hDiv

-- The leading coefficient of `sparseMonomial (i-j) (x/y) * b` (at degree `i`) is `x`.
lemma coeff_mul_sparseMonomial_leading {b : MvSparsePoly R nvars}
    {i j : MvDegrees nvars} {x y cf : R} {bs}
    (hB : b.terms = (j, y) :: bs) (hDiv : MvDegrees.divides j i = true)
    (h_div : y * cf = x) :
    MvPolynomial.coeff (MvDegrees.toFinsupp i)
      (toPoly (sparseMonomial (i - j) cf * b)) = x := by
  rw [toPoly_mul, toPoly_sparseMonomial, mul_comm (MvPolynomial.monomial _ _) (toPoly b)]
  have hi : MvDegrees.toFinsupp i
      = MvDegrees.toFinsupp j + MvDegrees.toFinsupp (i - j) := by
    rw [toFinsupp_sub_add hDiv, add_comm]
  rw [hi, MvPolynomial.coeff_mul_monomial]
  have hbj : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPoly b) = y := by
    change MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore b.terms) = y
    rw [hB]
    exact coeff_toPolyCore_head bs (degLt_of_sorted_cons (hB ▸ b.sorted))
  rw [hbj]
  exact h_div

-- The Cancel Lemma: subtracting `sparseMonomial (i-j) cf * b` (whose leading term cancels
-- `a`'s) strictly lowers the lex measure `(multidegree, length)`. Stated over an opaque
-- coefficient `cf` with `y * cf = x` (the division stays at the call site).
lemma multidegree_sub_cancel
  {a b : MvSparsePoly R nvars} {i j : MvDegrees nvars} {x y cf : R} {as bs}
  (hA : a.terms = (i, x) :: as)
  (hB : b.terms = (j, y) :: bs)
  (hDiv : MvDegrees.divides j i = true)
  (h_div : y * cf = x) :
  Prod.Lex (fun (u v : MvDegrees nvars) => u < v) (fun (u v : ℕ) => u < v)
    ((a - sparseMonomial (i - j) cf * b).multidegree,
     (a - sparseMonomial (i - j) cf * b).terms.length)
    (a.multidegree, a.terms.length) := by
  have ha_deg : a.multidegree = i := by unfold multidegree; rw [hA]; rfl
  rw [ha_deg]
  unfold multidegree
  apply lex_drop_of_degLt_with_hA hA
  -- Goal: `degLt i (a - sparseMonomial (i-j) cf * b).terms`.
  intro p hp
  obtain ⟨d, v⟩ := p
  have hv : v ≠ 0 := (a - sparseMonomial (i - j) cf * b).nonzero (d, v) hp
  have hcoeff_v : MvPolynomial.coeff (MvDegrees.toFinsupp d)
      (toPoly (a - sparseMonomial (i - j) cf * b)) = v :=
    coeff_toPolyCore_mem (a - sparseMonomial (i - j) cf * b).sorted hp
  by_contra hge
  push Not at hge
  -- `hge : i ≤ d`. Show the coefficient at `d` is `0`, contradicting `v ≠ 0`.
  have hcoeff_0 : MvPolynomial.coeff (MvDegrees.toFinsupp d)
      (toPoly (a - sparseMonomial (i - j) cf * b)) = 0 := by
    rw [toPoly_sub, MvPolynomial.coeff_sub]
    rcases eq_or_lt_of_le hge with rfl | hlt
    · -- `d = i`: leading terms of `a` and `c*b` are both `x`, so they cancel.
      have h1 : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPoly a) = x := by
        change MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore a.terms) = x
        rw [hA]; exact coeff_toPolyCore_head as (degLt_of_sorted_cons (hA ▸ a.sorted))
      have h2 : MvPolynomial.coeff (MvDegrees.toFinsupp i)
          (toPoly (sparseMonomial (i - j) cf * b)) = x :=
        coeff_mul_sparseMonomial_leading hB hDiv h_div
      rw [h1, h2, sub_self]
    · -- `i < d`: both polynomials have all degrees `≤ i < d`, so both coefficients are `0`.
      have h1 : MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly a) = 0 := by
        change MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPolyCore a.terms) = 0
        apply coeff_toPolyCore_of_degLt
        intro q hq
        rw [hA] at hq
        rcases List.mem_cons.mp hq with h | h
        · rw [h]; exact hlt
        · exact lt_trans ((List.pairwise_cons.mp (hA ▸ a.sorted)).1 q h) hlt
      have h2 : MvPolynomial.coeff (MvDegrees.toFinsupp d)
          (toPoly (sparseMonomial (i - j) cf * b)) = 0 := by
        change MvPolynomial.coeff (MvDegrees.toFinsupp d)
          (toPolyCore (sparseMonomial (i - j) cf * b).terms) = 0
        apply coeff_toPolyCore_of_degLt
        intro q hq
        exact lt_of_le_of_lt (mul_sparseMonomial_degLe hB hDiv q hq) hlt
      rw [h1, h2, sub_zero]
  rw [hcoeff_0] at hcoeff_v
  exact hv hcoeff_v.symm

-- The tail of a sorted polynomial term-list is itself sorted.
omit [DecidableEq R] in
lemma sorted_tail {a : MvSparsePoly R nvars} {i : MvDegrees nvars} {x : R} {as}
    (hA : a.terms = (i, x) :: as) : as.Pairwise (·.1 > ·.1) :=
  (List.pairwise_cons.mp (hA ▸ a.sorted)).2

lemma tail_terminates
  {a : MvSparsePoly R nvars} {i : MvDegrees nvars} {x : R} {as}
  (hA : a.terms = (i, x) :: as) :
  Prod.Lex (fun (u v : MvDegrees nvars) => u < v) (fun (u v : ℕ) => u < v)
    ((ofSortedList as (sorted_tail hA)).multidegree,
     (ofSortedList as (sorted_tail hA)).terms.length)
    (a.multidegree, a.terms.length) := by
  -- Step 1: The length strictly drops (filtering the tail is no longer than the tail).
  have h_len : (ofSortedList as (sorted_tail hA)).terms.length < a.terms.length := by
    rw [hA]
    simp only [List.length_cons]
    have h_bound := ofSortedList_length_le as (sorted_tail hA)
    grind
  -- The leading degree of `a` is `i`, and every degree in the tail is `< i`.
  have ha_deg : a.multidegree = i := by unfold multidegree; rw [hA]; rfl
  have hlt_as : ∀ p ∈ as, p.1 < i := (List.pairwise_cons.mp (hA ▸ a.sorted)).1
  -- Step 2: Split the multidegree comparison into the three cases.
  rcases lt_trichotomy ((ofSortedList as (sorted_tail hA)).multidegree) a.multidegree
    with h_lt | h_eq | h_gt
  · -- Multidegree strictly dropped.
    exact Prod.Lex.left _ _ h_lt
  · -- Multidegree unchanged: use the length drop.
    rw [h_eq]
    exact Prod.Lex.right _ h_len
  · -- Multidegree increased: impossible, the tail's degrees are all `< i = a.multidegree`.
    exfalso
    have h_od_le : (ofSortedList as (sorted_tail hA)).multidegree ≤ i := by
      have key : ∀ q ∈ (ofSortedList as (sorted_tail hA)).terms, q.1 < i :=
        fun q hq => hlt_as q (List.mem_of_mem_filter hq)
      unfold multidegree
      cases hf : (ofSortedList as (sorted_tail hA)).terms with
      | nil =>
        change (0 : MvDegrees nvars) ≤ i
        exact mvDegrees_zero_le i
      | cons p ps =>
        exact le_of_lt (key p (by rw [hf]; exact List.mem_cons_self))
    rw [ha_deg] at h_gt
    exact absurd h_gt (not_lt.mpr h_od_le)

-- 4. The Clean Function (uses the global lexicographic `WOrdering` instance).
-- Only `[Div R]` is needed (for `x / y`); avoiding `[Field R]` keeps the ambient `CommRing`
-- as the sole source of `*`, so `h_div`'s multiplication matches `multidegree_sub_cancel`.
def mvDivRem [Div R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars × MvSparsePoly R nvars :=
  match hA : a.terms with
  | [] => (0, 0)
  | (i, x) :: as =>
    match hB : b.terms with
    | [] => (0, a)
    | (j, y) :: _bs =>
      if hDiv : MvDegrees.divides j i then
        let c := sparseMonomial (i - j) (x / y)
        if h_div : y * (x / y) = x then
          let (q', r') := mvDivRem (a - c * b) b
          (q' + c, r')
        else
          (0, a)
      else
        let (q', r') := mvDivRem (ofSortedList as (sorted_tail hA)) b
        (q', sparseMonomial i x + r')
termination_by a
decreasing_by
  · exact multidegree_sub_cancel hA hB hDiv h_div
  · exact tail_terminates hA

-- The pencil-reduction GCD step. It cancels the head of whichever polynomial has the larger
-- leading monomial. A sound well-founded measure for this reduction is not available in the
-- flat multivariate representation (cancelling a leading term lowers the lex multidegree but
-- not the total degree, and `i - j` is only meaningful when `j` divides `i`), so we make the
-- recursion structural via an explicit fuel parameter, bounded by the total degrees.
def gcdPrimFuel : ℕ → MvSparsePoly R nvars → MvSparsePoly R nvars → MvSparsePoly R nvars
  | 0, a, _ => a
  | fuel + 1, a, b =>
    match a.terms, b.terms with
    | [], _ => b
    | _, [] => a
    | (i, x) :: _, (j, y) :: _ =>
      if i > j then
        gcdPrimFuel fuel (y • a - sparseMonomial (i - j) x * b) b
      else
        gcdPrimFuel fuel a (x • b - sparseMonomial (j - i) y * a)

def gcdPrim (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  gcdPrimFuel (a.degree + b.degree + 1) a b

-- The running gcd-fold divides its accumulator (multivariate analogue of the
-- univariate `foldl_gcd_dvd_acc`).
omit [DecidableEq R] in
lemma mv_foldl_gcd_dvd_acc [IsDomain R] [GCDMonoid R]
    (l : List (MvDegrees nvars × R)) (acc : R) :
    l.foldl (fun a x => gcd a x.2) acc ∣ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact (ih (gcd acc hd.2)).trans (gcd_dvd_left _ _)

-- The gcd-fold divides every coefficient present in the list.
omit [DecidableEq R] in
lemma mv_foldl_gcd_dvd_mem [IsDomain R] [GCDMonoid R] {l : List (MvDegrees nvars × R)}
    {i : MvDegrees nvars} {c : R} (h : (i, c) ∈ l) (acc : R) :
    l.foldl (fun a x => gcd a x.2) acc ∣ c := by
  induction l generalizing acc with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h_mem
    · exact (mv_foldl_gcd_dvd_acc tl (gcd acc c)).trans (gcd_dvd_right _ _)
    · exact ih h_mem (gcd acc hd.2)

-- `content` divides each coefficient.
omit [DecidableEq R] in
lemma mv_content_dvd_coeff [IsDomain R] [GCDMonoid R] {l : List (MvDegrees nvars × R)}
    {i : MvDegrees nvars} {c : R} (h : (i, c) ∈ l) :
    l.foldl (init := 0) (fun acc x => gcd acc x.2) ∣ c :=
  mv_foldl_gcd_dvd_mem h 0

def content [IsDomain R] [GCDMonoid R] (a : MvSparsePoly R nvars) : R :=
  a.terms.foldl (init := 0) (gcd · ·.2)

def primitivePart [IsDomain R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : MvSparsePoly R nvars) : MvSparsePoly R nvars where
  terms :=
    let b := a.content
    a.terms.map fun (i, a) => (i, a / b)
  sorted := by
    refine List.Pairwise.map _ (fun _ _ h => h) a.sorted
  nonzero := by
    intro x hx
    simp only [List.mem_map, Prod.exists] at hx
    rcases hx with ⟨i, c, h_mem, rfl⟩
    have hc_nz := a.nonzero (i, c) h_mem
    intro h_div_zero
    -- If `c / content = 0` then `content * (c / content) = 0`, but it also equals `c ≠ 0`.
    have h_mul := congr_arg (fun (z : R) => a.content * z) h_div_zero
    simp only [mul_zero] at h_mul
    have h_dvd : a.content ∣ c := mv_content_dvd_coeff h_mem
    rw [IsExactDiv.mul_div_cancel h_dvd] at h_mul
    exact hc_nz h_mul

nonrec def gcd [IsDomain R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  gcd a.content b.content • (gcdPrim a b).primitivePart

instance : IsExactDiv ℤ where
  mul_div_cancel := Int.mul_ediv_cancel'

instance {R} [CommGroupWithZero R] : IsExactDiv R where
  mul_div_cancel h := by
    apply mul_div_cancel_of_imp'; rintro rfl
    simpa only [zero_dvd_iff] using h

-- divRem a b = (q, r) -> a = b * q + r
def divRem [Div R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars × MvSparsePoly R nvars :=
  match hA : a.terms, hB : b.terms with
  | (i, x) :: _as, (j, y) :: _bs =>
    if hDiv : MvDegrees.divides j i then
      let c := sparseMonomial (i - j) (x / y)
      if h_div : y * (x / y) = x then
        let (q', r') := divRem (a - c * b) b
        (q' + c, r')
      else
        (0, a)
    else
      (0, a)
  | _, _ => (0, a)
termination_by a
decreasing_by exact multidegree_sub_cancel hA hB hDiv h_div

-- `divRem` satisfies the division identity `a = b * q + r`.
theorem divRem_spec [Div R] (a b : MvSparsePoly R nvars) :
    b * (divRem a b).1 + (divRem a b).2 = a := by
  fun_induction divRem a b with
  | case1 a i x as j y bs ha hb hDiv c h_exact q' r' hqr ih =>
    rw [hqr] at ih
    linear_combination ih
  | _ => simp

-- ==========================================================================
-- MULTI-DIVISOR NORMAL FORM (the reduction step of Buchberger's algorithm)
--
-- Given a polynomial `f` and a list of divisors `G = [g₁,…,gₖ]`, repeatedly cancel the leading
-- term of `f` using whichever `gᵢ` has a leading term dividing it; terms that cannot be reduced
-- are moved to the remainder. The result `normalForm f G` is `f` reduced modulo the ideal `⟨G⟩`.
-- The key verified fact (`normalForm_span`) is `toPoly f - toPoly (normalForm f G) ∈ ⟨G⟩`, hence
-- `normalForm f G = 0 → toPoly f ∈ ⟨G⟩` — a computable, *proof-producing* ideal-membership test.
-- ==========================================================================

/-- The ideal of `MvPolynomial` generated by the images of the divisor list `G`. -/
noncomputable def idealOf (G : List (MvSparsePoly R nvars)) :
    Ideal (MvPolynomial (Fin nvars) R) :=
  Ideal.span { p | ∃ g ∈ G, toPoly g = p }

omit [DecidableEq R] in
lemma idealOf_mono {G G' : List (MvSparsePoly R nvars)} (h : G ⊆ G') :
    idealOf G ≤ idealOf G' :=
  Ideal.span_mono (fun _ ⟨g, hg, hgp⟩ => ⟨g, h hg, hgp⟩)

lemma toPoly_ofSortedList (l : List (MvDegrees nvars × R)) (h : l.Pairwise (·.1 > ·.1)) :
    toPoly (ofSortedList l h) = toPolyCore l :=
  toPolyCore_filter_nonzero l

/-- Try to cancel the leading term `(i, x)` of `f` using the first divisor in `G` whose leading
term divides it; returns the reduced polynomial `f - (i-j)·(x/y)·g`, or `none` if no divisor
applies. Structural recursion on `G`. -/
def reduceLeadByList [Div R] (i : MvDegrees nvars) (x : R) (f : MvSparsePoly R nvars) :
    List (MvSparsePoly R nvars) → Option (MvSparsePoly R nvars)
  | [] => none
  | g :: gs =>
    match g.terms with
    | (j, y) :: _ =>
      if MvDegrees.divides j i then
        if y * (x / y) = x then some (f - sparseMonomial (i - j) (x / y) * g)
        else reduceLeadByList i x f gs
      else reduceLeadByList i x f gs
    | [] => reduceLeadByList i x f gs

/-- A successful reduction strictly decreases the `(multidegree, length)` measure: this is what
makes the well-founded recursion in `normalForm` terminate. -/
lemma reduceLeadByList_lex [Div R] {i : MvDegrees nvars} {x : R} {f : MvSparsePoly R nvars}
    {as : List (MvDegrees nvars × R)} (hA : f.terms = (i, x) :: as) :
    ∀ {G : List (MvSparsePoly R nvars)} {f' : MvSparsePoly R nvars},
      reduceLeadByList i x f G = some f' →
      Prod.Lex (fun u v : MvDegrees nvars => u < v) (fun u v : ℕ => u < v)
        (f'.multidegree, f'.terms.length) (f.multidegree, f.terms.length) := by
  intro G
  induction G with
  | nil => intro f' h; simp [reduceLeadByList] at h
  | cons g gs ih =>
    intro f' h
    cases hB : g.terms with
    | nil => simp only [reduceLeadByList, hB] at h; exact ih h
    | cons hd tl =>
      obtain ⟨j, y⟩ := hd
      simp only [reduceLeadByList, hB] at h
      by_cases hDiv : MvDegrees.divides j i
      · rw [if_pos hDiv] at h
        by_cases h_div : y * (x / y) = x
        · rw [if_pos h_div] at h
          injection h with h; subst h
          exact multidegree_sub_cancel hA hB hDiv h_div
        · rw [if_neg h_div] at h; exact ih h
      · rw [if_neg hDiv] at h; exact ih h

/-- A successful reduction changes `f` by an element of the ideal `⟨G⟩`. -/
lemma reduceLeadByList_span [Div R] {i : MvDegrees nvars} {x : R} {f : MvSparsePoly R nvars} :
    ∀ {G : List (MvSparsePoly R nvars)} {f' : MvSparsePoly R nvars},
      reduceLeadByList i x f G = some f' → toPoly f - toPoly f' ∈ idealOf G := by
  intro G
  induction G with
  | nil => intro f' h; simp [reduceLeadByList] at h
  | cons g gs ih =>
    intro f' h
    cases hB : g.terms with
    | nil =>
      simp only [reduceLeadByList, hB] at h
      exact idealOf_mono (fun _ ha => List.mem_cons_of_mem g ha) (ih h)
    | cons hd tl =>
      obtain ⟨j, y⟩ := hd
      simp only [reduceLeadByList, hB] at h
      by_cases hDiv : MvDegrees.divides j i
      · rw [if_pos hDiv] at h
        by_cases h_div : y * (x / y) = x
        · rw [if_pos h_div] at h
          injection h with h; subst h
          rw [toPoly_sub, sub_sub_cancel, toPoly_mul]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, List.mem_cons_self, rfl⟩)
        · rw [if_neg h_div] at h
          exact idealOf_mono (fun _ ha => List.mem_cons_of_mem g ha) (ih h)
      · rw [if_neg hDiv] at h
        exact idealOf_mono (fun _ ha => List.mem_cons_of_mem g ha) (ih h)

-- Every term's degree is `≤` the leading degree.
omit [DecidableEq R] in
lemma degree_le_multidegree {a : MvSparsePoly R nvars} {p : MvDegrees nvars × R}
    (hp : p ∈ a.terms) : p.1 ≤ multidegree a := by
  cases hA : a.terms with
  | nil => rw [hA] at hp; exact absurd hp List.not_mem_nil
  | cons hd tl =>
    have hmd : multidegree a = hd.1 := by unfold multidegree; rw [hA]; rfl
    rw [hmd]
    rw [hA] at hp
    rcases List.mem_cons.mp hp with h | h
    · rw [h]
    · exact le_of_lt ((List.pairwise_cons.mp (hA ▸ a.sorted)).1 p h)

-- A nonzero coefficient of `toPolyCore l` is realized by a term of `l`.
omit [DecidableEq R] in
lemma coeff_toPolyCore_support {m : Fin nvars →₀ ℕ} :
    ∀ {l : List (MvDegrees nvars × R)},
    MvPolynomial.coeff m (toPolyCore l) ≠ 0 → ∃ p ∈ l, m = MvDegrees.toFinsupp p.1 := by
  intro l
  induction l with
  | nil => intro h; simp [toPolyCore] at h
  | cons hd tl ih =>
    intro h
    obtain ⟨d, v⟩ := hd
    rw [toPolyCore, MvPolynomial.coeff_add] at h
    by_cases hm : MvDegrees.toFinsupp d = m
    · exact ⟨(d, v), List.mem_cons_self, hm.symm⟩
    · rw [MvPolynomial.coeff_monomial, if_neg hm, zero_add] at h
      obtain ⟨p, hp, hpm⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpm⟩

-- ── Geobucket reduction (verified-total fast path for `normalForm`) ──────────
-- A geobucket is a list of polynomial "buckets" whose sum is the represented polynomial. Inserting
-- a small polynomial only touches one bucket (cheap), so the reduction loop avoids re-merging the
-- whole dividend each step. We prove enough about it to discharge termination of `normalFormFast`,
-- which then serves as the `@[implemented_by]` runtime for `normalForm`.

/-- The polynomial represented by a geobucket: the sum of its buckets. -/
def gbSum : List (MvSparsePoly R nvars) → MvSparsePoly R nvars
  | [] => 0
  | b :: bs => b + gbSum bs

/-- Insert `p` into a geobucket, cascading when a bucket grows too large. Preserves the sum. -/
def gbInsert : List (MvSparsePoly R nvars) → MvSparsePoly R nvars →
    List (MvSparsePoly R nvars)
  | [], p => [p]
  | b :: bs, p =>
    if (b + p).terms.length ≤ 2 * b.terms.length + 8 then (b + p) :: bs
    else (0 : MvSparsePoly R nvars) :: gbInsert bs (b + p)

@[simp] lemma gbSum_nil : gbSum ([] : List (MvSparsePoly R nvars)) = 0 := rfl

lemma gbInsert_sum (bs : List (MvSparsePoly R nvars)) (p : MvSparsePoly R nvars) :
    gbSum (gbInsert bs p) = gbSum bs + p := by
  induction bs generalizing p with
  | nil => simp [gbSum, gbInsert]
  | cons b bs ih =>
    simp only [gbInsert]
    split
    · simp only [gbSum]; abel
    · simp only [gbSum]; rw [ih]; abel

omit [DecidableEq R] in
/-- The coefficient of a single bucket at a degree `d` that upper-bounds all its terms: it is the
leading coefficient if `d` is the leading degree, else `0`. -/
lemma coeff_toPoly_at (b : MvSparsePoly R nvars) (d : MvDegrees nvars)
    (hle : ∀ t ∈ b.terms, t.1 ≤ d) :
    MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly b)
      = if multidegree b = d then (b.terms.headD (0, 0)).2 else 0 := by
  cases hb : b.terms with
  | nil => simp [toPoly, hb, toPolyCore, multidegree]
  | cons hd tl =>
    obtain ⟨d0, c0⟩ := hd
    have hmd : multidegree b = d0 := by simp [multidegree, hb]
    have hsorted : ((d0, c0) :: tl).Pairwise (·.1 > ·.1) := hb ▸ b.sorted
    rw [hmd]
    by_cases h : d0 = d
    · subst h
      rw [if_pos rfl]
      change MvPolynomial.coeff (MvDegrees.toFinsupp d0) (toPolyCore b.terms) = c0
      rw [hb]; exact coeff_toPolyCore_head tl (degLt_of_sorted_cons hsorted)
    · rw [if_neg h]
      change MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPolyCore b.terms) = 0
      have hd0d : d0 < d := lt_of_le_of_ne (hle (d0, c0) (by rw [hb]; exact List.mem_cons_self)) h
      rw [hb]; apply coeff_toPolyCore_of_degLt
      intro q hq
      rcases List.mem_cons.mp hq with rfl | htl
      · exact hd0d
      · exact lt_trans ((List.pairwise_cons.mp hsorted).1 q htl) hd0d

omit [DecidableEq R] in
/-- A nonzero coefficient of `toPoly b` occurs at a degree `≤ multidegree b`. -/
lemma coeff_ne_zero_le_multidegree (b : MvSparsePoly R nvars) (d : MvDegrees nvars)
    (h : MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly b) ≠ 0) : d ≤ multidegree b := by
  obtain ⟨p, hp, hpe⟩ := coeff_toPolyCore_support h
  rw [toFinsupp_inj.mp hpe]
  exact degree_le_multidegree hp

/-- The candidate leading term of a geobucket: the largest degree among the bucket heads, with the
coefficients at that degree summed. (Cheap — only looks at heads.) -/
def gbTop : List (MvSparsePoly R nvars) → Option (MvDegrees nvars × R)
  | [] => none
  | b :: bs =>
    match b.terms, gbTop bs with
    | [], r => r
    | (d, c) :: _, none => some (d, c)
    | (d, c) :: _, some (d', c') =>
      if d = d' then some (d, c + c')
      else if d < d' then some (d', c') else some (d, c)

/-- **Correctness of `gbTop`.** Either the geobucket sums to `0` (head search yields `none`), or the
returned `(d, cf)` records the coefficient of the sum at `d` and `d` upper-bounds the sum's support
(via the coefficient form). This is what lets the cheap head-search stand in for the true leading
term, even when coefficients cancel across buckets. -/
lemma gbTop_spec (buckets : List (MvSparsePoly R nvars)) :
    match gbTop buckets with
    | none => gbSum buckets = 0
    | some (d, cf) =>
        MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly (gbSum buckets)) = cf ∧
        ∀ dd : MvDegrees nvars,
          MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly (gbSum buckets)) ≠ 0 → dd ≤ d := by
  induction buckets with
  | nil => simp [gbTop, gbSum]
  | cons b bs ih =>
    have hsplit : ∀ dd : MvDegrees nvars,
        MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly (gbSum (b :: bs)))
        = MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly b)
          + MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly (gbSum bs)) := by
      intro dd; simp only [gbSum, toPoly_add, MvPolynomial.coeff_add]
    cases hbt : b.terms with
    | nil =>
      have hb0 : b = 0 := by ext1; rw [hbt]; rfl
      have hsum : gbSum (b :: bs) = gbSum bs := by rw [gbSum, hb0, zero_add]
      simp only [gbTop, hbt]
      rw [hsum]; exact ih
    | cons hd tl =>
      obtain ⟨d0, c0⟩ := hd
      have hb_le : ∀ t ∈ b.terms, t.1 ≤ d0 := by
        rw [hbt]; intro t ht; rcases List.mem_cons.mp ht with rfl | htl
        · exact le_refl _
        · exact le_of_lt ((List.pairwise_cons.mp (hbt ▸ b.sorted)).1 t htl)
      have hmd : multidegree b = d0 := by simp [multidegree, hbt]
      have hcoeff_b : MvPolynomial.coeff (MvDegrees.toFinsupp d0) (toPoly b) = c0 := by
        rw [coeff_toPoly_at b d0 hb_le, hmd]; simp [hbt]
      have hub_b : ∀ dd : MvDegrees nvars,
          MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly b) ≠ 0 → dd ≤ d0 := by
        intro dd hdd; rw [← hmd]; exact coeff_ne_zero_le_multidegree b dd hdd
      cases hbs : gbTop bs with
      | none =>
        rw [hbs] at ih
        simp only [gbTop, hbt, hbs]
        refine ⟨?_, ?_⟩
        · rw [hsplit, hcoeff_b, ih, toPoly_zero, MvPolynomial.coeff_zero, add_zero]
        · intro dd hdd
          rw [hsplit, ih, toPoly_zero, MvPolynomial.coeff_zero, add_zero] at hdd
          exact hub_b dd hdd
      | some p =>
        obtain ⟨d', c'⟩ := p
        rw [hbs] at ih
        obtain ⟨ih_c, ih_ub⟩ := ih
        by_cases hdd' : d0 = d'
        · subst hdd'
          simp only [gbTop, hbt, hbs, if_true]
          refine ⟨?_, ?_⟩
          · rw [hsplit, hcoeff_b, ih_c]
          · intro dd hdd
            rw [hsplit] at hdd
            by_cases hb0 : MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly b) = 0
            · rw [hb0, zero_add] at hdd; exact ih_ub dd hdd
            · exact hub_b dd hb0
        · simp only [gbTop, hbt, hbs, if_neg hdd']
          by_cases hlt : d0 < d'
          · have hcb : MvPolynomial.coeff (MvDegrees.toFinsupp d') (toPoly b) = 0 := by
              by_contra hc; exact absurd (hub_b d' hc) (not_le.mpr hlt)
            simp only [if_pos hlt]
            refine ⟨?_, ?_⟩
            · rw [hsplit, hcb, ih_c, zero_add]
            · intro dd hdd
              rw [hsplit] at hdd
              by_cases hb0 : MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly b) = 0
              · rw [hb0, zero_add] at hdd; exact ih_ub dd hdd
              · exact le_trans (hub_b dd hb0) (le_of_lt hlt)
          · have hd'd0 : d' < d0 := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hdd' h.symm)
            have hcs : MvPolynomial.coeff (MvDegrees.toFinsupp d0) (toPoly (gbSum bs)) = 0 := by
              by_contra hc; exact absurd (ih_ub d0 hc) (not_le.mpr hd'd0)
            simp only [if_neg hlt]
            refine ⟨?_, ?_⟩
            · rw [hsplit, hcoeff_b, hcs, add_zero]
            · intro dd hdd
              rw [hsplit] at hdd
              by_cases hb0 : MvPolynomial.coeff (MvDegrees.toFinsupp dd) (toPoly b) = 0
              · rw [hb0, zero_add] at hdd; exact le_trans (ih_ub dd hdd) (le_of_lt hd'd0)
              · exact hub_b dd hb0

/-- Remove the leading term of `p`. -/
def dropLead (p : MvSparsePoly R nvars) : MvSparsePoly R nvars where
  terms := p.terms.tail
  sorted := p.sorted.sublist (List.tail_sublist p.terms)
  nonzero := fun x hx => p.nonzero x ((List.tail_sublist p.terms).subset hx)

omit [DecidableEq R] in
lemma toPoly_dropLead (p : MvSparsePoly R nvars) :
    toPoly (dropLead p) = toPolyCore p.terms.tail := rfl

lemma sparseMonomial_zero (d : MvDegrees nvars) : sparseMonomial d (0 : R) = 0 := by
  apply toPoly_injective
  rw [toPoly_sparseMonomial, toPoly_zero, MvPolynomial.monomial_zero]

/-- Drop, from each bucket whose leading degree is `d`, that leading term. -/
def cleanTop (d : MvDegrees nvars) (buckets : List (MvSparsePoly R nvars)) :
    List (MvSparsePoly R nvars) :=
  buckets.map (fun b => if multidegree b = d then dropLead b else b)

/-- Cleaning a single bucket at `d` subtracts exactly its coefficient at `d`. -/
lemma cleanBucket_eq (d : MvDegrees nvars) (b : MvSparsePoly R nvars)
    (hle : ∀ t ∈ b.terms, t.1 ≤ d) :
    (if multidegree b = d then dropLead b else b)
      = b - sparseMonomial d (MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly b)) := by
  apply toPoly_injective
  rw [toPoly_sub, toPoly_sparseMonomial, coeff_toPoly_at b d hle]
  by_cases h : multidegree b = d
  · rw [if_pos h, if_pos h, toPoly_dropLead]
    cases hb : b.terms with
    | nil => simp [hb, toPoly, toPolyCore]
    | cons hd tl =>
      obtain ⟨d0, c0⟩ := hd
      have h2 : multidegree b = d0 := by simp [multidegree, hb]
      have hmd : d0 = d := h2 ▸ h
      have hbtoPoly : toPoly b
          = MvPolynomial.monomial (MvDegrees.toFinsupp d0) c0 + toPolyCore tl := by
        change toPolyCore b.terms = _; rw [hb]; rfl
      simp only [List.tail_cons, List.headD_cons]
      rw [hbtoPoly, hmd]
      abel
  · rw [if_neg h, if_neg h, MvPolynomial.monomial_zero, sub_zero]

/-- **Cleaning preserves the sum**, up to subtracting the (single) coefficient at `d`. -/
lemma cleanTop_sum (d : MvDegrees nvars) (buckets : List (MvSparsePoly R nvars))
    (hub : ∀ b ∈ buckets, ∀ t ∈ b.terms, t.1 ≤ d) :
    gbSum (cleanTop d buckets)
      = gbSum buckets - sparseMonomial d (MvPolynomial.coeff (MvDegrees.toFinsupp d)
          (toPoly (gbSum buckets))) := by
  induction buckets with
  | nil => simp [cleanTop, gbSum, toPoly_zero, sparseMonomial_zero]
  | cons b bs ih =>
    have hbub : ∀ t ∈ b.terms, t.1 ≤ d := hub b List.mem_cons_self
    have hbsub : ∀ b' ∈ bs, ∀ t ∈ b'.terms, t.1 ≤ d :=
      fun b' hb' => hub b' (List.mem_cons_of_mem _ hb')
    have key : gbSum (cleanTop d (b :: bs))
        = (b - sparseMonomial d (MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly b)))
          + (gbSum bs - sparseMonomial d (MvPolynomial.coeff (MvDegrees.toFinsupp d)
              (toPoly (gbSum bs)))) := by
      simp only [cleanTop, List.map_cons, gbSum]
      rw [cleanBucket_eq d b hbub]
      congr 1
      exact ih hbsub
    rw [key]
    apply toPoly_injective
    simp only [gbSum, toPoly_sub, toPoly_add, toPoly_sparseMonomial, MvPolynomial.coeff_add,
      map_add]
    abel

omit [DecidableEq R] in
/-- The maximal degree found by `gbTop` is achieved by some (nonempty) bucket. -/
lemma gbTop_mem : ∀ {buckets : List (MvSparsePoly R nvars)} {d cf},
    gbTop buckets = some (d, cf) → ∃ b ∈ buckets, b.terms ≠ [] ∧ multidegree b = d := by
  intro buckets
  induction buckets with
  | nil => intro d cf h; simp [gbTop] at h
  | cons b bs ih =>
    intro d cf h
    cases hbt : b.terms with
    | nil =>
      simp only [gbTop, hbt] at h
      obtain ⟨b', hb', hne', hmd'⟩ := ih h
      exact ⟨b', List.mem_cons_of_mem _ hb', hne', hmd'⟩
    | cons hd tl =>
      obtain ⟨d0, c0⟩ := hd
      have hmd0 : multidegree b = d0 := by simp [multidegree, hbt]
      have hbne : b.terms ≠ [] := by rw [hbt]; simp
      cases hbs : gbTop bs with
      | none =>
        simp only [gbTop, hbt, hbs, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨b, List.mem_cons_self, hbne, hmd0⟩
      | some p =>
        obtain ⟨d', c'⟩ := p
        simp only [gbTop, hbt, hbs] at h
        by_cases hdd : d0 = d'
        · rw [if_pos hdd, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨b, List.mem_cons_self, hbne, hmd0⟩
        · rw [if_neg hdd] at h
          by_cases hlt : d0 < d'
          · rw [if_pos hlt, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨b', hb', hne', hmd'⟩ := ih hbs
            exact ⟨b', List.mem_cons_of_mem _ hb', hne', hmd'⟩
          · rw [if_neg hlt, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact ⟨b, List.mem_cons_self, hbne, hmd0⟩

omit [DecidableEq R] in
/-- `dropLead` strictly shortens a nonempty polynomial. -/
lemma dropLead_terms_length_lt {p : MvSparsePoly R nvars} (hp : p.terms ≠ []) :
    (dropLead p).terms.length < p.terms.length := by
  cases hh : p.terms with
  | nil => exact absurd hh hp
  | cons a l => simp [dropLead, hh]

omit [DecidableEq R] in
/-- Cleaning at `d` strictly drops the total term count, when some bucket has leading degree `d`. -/
lemma cleanTop_terms_lt (d : MvDegrees nvars) (buckets : List (MvSparsePoly R nvars))
    (hex : ∃ b ∈ buckets, b.terms ≠ [] ∧ multidegree b = d) :
    ((cleanTop d buckets).map (fun b => b.terms.length)).sum
      < (buckets.map (fun b => b.terms.length)).sum := by
  induction buckets with
  | nil => obtain ⟨b, hb, -⟩ := hex; exact absurd hb List.not_mem_nil
  | cons b bs ih =>
    simp only [cleanTop, List.map_cons, List.sum_cons]
    have hle : ∀ b' : MvSparsePoly R nvars,
        (if multidegree b' = d then dropLead b' else b').terms.length ≤ b'.terms.length := by
      intro b'; by_cases h : multidegree b' = d
      · rw [if_pos h]
        by_cases hb' : b'.terms = []
        · simp [dropLead, hb']
        · exact le_of_lt (dropLead_terms_length_lt hb')
      · rw [if_neg h]
    have hbsle : ((cleanTop d bs).map (fun b => b.terms.length)).sum
        ≤ (bs.map (fun b => b.terms.length)).sum := by
      clear ih hex
      induction bs with
      | nil => simp [cleanTop]
      | cons c cs ihs => simp only [cleanTop, List.map_cons, List.sum_cons]; exact add_le_add (hle c) ihs
    obtain ⟨w, hw, hwne, hwd⟩ := hex
    rcases List.mem_cons.mp hw with rfl | hwbs
    · rw [if_pos hwd]
      exact add_lt_add_of_lt_of_le (dropLead_terms_length_lt hwne) hbsle
    · have hlt : ((cleanTop d bs).map (fun b => b.terms.length)).sum
          < (bs.map (fun b => b.terms.length)).sum := ih ⟨w, hwbs, hwne, hwd⟩
      exact add_lt_add_of_le_of_lt (hle b) hlt

/-- When `gbTop` reports a nonzero coefficient, that `(d, cf)` is the genuine leading term of the
geobucket sum. -/
lemma gbTop_lead {buckets : List (MvSparsePoly R nvars)} {d : MvDegrees nvars} {cf : R}
    (h : gbTop buckets = some (d, cf)) (hcf : cf ≠ 0) :
    (gbSum buckets).terms = (d, cf) :: (gbSum buckets).terms.tail := by
  have hspec := gbTop_spec buckets
  rw [h] at hspec
  obtain ⟨hc, hub⟩ := hspec
  have hne : (gbSum buckets).terms ≠ [] := by
    intro he; apply hcf
    rw [← hc]
    change MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPolyCore (gbSum buckets).terms) = 0
    rw [he]; rfl
  obtain ⟨⟨md, lc⟩, rest, hP⟩ := List.exists_cons_of_ne_nil hne
  have hmd : multidegree (gbSum buckets) = md := by simp [multidegree, hP]
  have hlc_ne : lc ≠ 0 := (gbSum buckets).nonzero (md, lc) (hP ▸ List.mem_cons_self)
  have hcoeff_md : MvPolynomial.coeff (MvDegrees.toFinsupp md) (toPoly (gbSum buckets)) = lc := by
    change MvPolynomial.coeff (MvDegrees.toFinsupp md) (toPolyCore (gbSum buckets).terms) = lc
    rw [hP]; exact coeff_toPolyCore_head rest (degLt_of_sorted_cons (hP ▸ (gbSum buckets).sorted))
  have hmdd : md ≤ d := hub md (by rw [hcoeff_md]; exact hlc_ne)
  have hdmd : d ≤ md := by
    rw [← hmd]
    obtain ⟨p, hp, hpe⟩ := coeff_toPolyCore_support (hc.symm ▸ hcf :
      MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPolyCore (gbSum buckets).terms) ≠ 0)
    rw [toFinsupp_inj.mp hpe]; exact degree_le_multidegree hp
  have hdeq : md = d := le_antisymm hmdd hdmd
  have hlceq : lc = cf := by rw [← hcoeff_md, hdeq, hc]
  rw [hP, List.tail_cons, hdeq, hlceq]

/-- Removing the leading term `(d, cf)` of `P` strictly decreases the `(multidegree, length)`
measure. -/
lemma sub_lead_lex {P : MvSparsePoly R nvars} {d : MvDegrees nvars} {cf : R}
    {rest : List (MvDegrees nvars × R)} (hP : P.terms = (d, cf) :: rest) :
    Prod.Lex (fun u v : MvDegrees nvars => u < v) (fun u v : ℕ => u < v)
      ((P - sparseMonomial d cf).multidegree, (P - sparseMonomial d cf).terms.length)
      (P.multidegree, P.terms.length) := by
  have hP_deg : P.multidegree = d := by unfold multidegree; rw [hP]; rfl
  rw [hP_deg]
  unfold multidegree
  apply lex_drop_of_degLt_with_hA hP
  intro p hp
  obtain ⟨e, v⟩ := p
  have hv : v ≠ 0 := (P - sparseMonomial d cf).nonzero (e, v) hp
  have hcoeff_v : MvPolynomial.coeff (MvDegrees.toFinsupp e) (toPoly (P - sparseMonomial d cf)) = v :=
    coeff_toPolyCore_mem (P - sparseMonomial d cf).sorted hp
  by_contra hge
  rw [not_lt] at hge
  have hcoeff_0 : MvPolynomial.coeff (MvDegrees.toFinsupp e) (toPoly (P - sparseMonomial d cf)) = 0 := by
    rw [toPoly_sub, toPoly_sparseMonomial, MvPolynomial.coeff_sub]
    rcases eq_or_lt_of_le hge with rfl | hlt
    · have h1 : MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly P) = cf := by
        change MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPolyCore P.terms) = cf
        rw [hP]; exact coeff_toPolyCore_head rest (degLt_of_sorted_cons (hP ▸ P.sorted))
      rw [h1, MvPolynomial.coeff_monomial, if_pos rfl, sub_self]
    · have h1 : MvPolynomial.coeff (MvDegrees.toFinsupp e) (toPoly P) = 0 := by
        change MvPolynomial.coeff (MvDegrees.toFinsupp e) (toPolyCore P.terms) = 0
        apply coeff_toPolyCore_of_degLt
        intro q hq
        rw [hP] at hq
        rcases List.mem_cons.mp hq with hh | hh
        · rw [hh]; exact hlt
        · exact lt_trans ((List.pairwise_cons.mp (hP ▸ P.sorted)).1 q hh) hlt
      have h2 : MvPolynomial.coeff (MvDegrees.toFinsupp e)
          (MvPolynomial.monomial (MvDegrees.toFinsupp d) cf) = 0 := by
        rw [MvPolynomial.coeff_monomial, if_neg (fun he => ne_of_lt hlt (toFinsupp_inj.mp he))]
      rw [h1, h2, sub_zero]
  rw [hcoeff_0] at hcoeff_v
  exact hv hcoeff_v.symm

omit [DecidableEq R] in
/-- `gbTop = none` exactly when every bucket is empty. -/
lemma gbTop_eq_none : ∀ {bs : List (MvSparsePoly R nvars)},
    gbTop bs = none → ∀ b ∈ bs, b.terms = [] := by
  intro bs
  induction bs with
  | nil => intro _ b hb; exact absurd hb List.not_mem_nil
  | cons c cs ih =>
    intro h b hb
    cases hct : c.terms with
    | nil =>
      simp only [gbTop, hct] at h
      rcases List.mem_cons.mp hb with rfl | hbcs
      · exact hct
      · exact ih h b hbcs
    | cons hd tl =>
      obtain ⟨d0, c0⟩ := hd
      exfalso
      cases hcs : gbTop cs with
      | none =>
        rw [show gbTop (c :: cs) = some (d0, c0) from by simp [gbTop, hct, hcs]] at h
        exact absurd h (by simp)
      | some p =>
        obtain ⟨d', c'⟩ := p
        by_cases hdd : d0 = d'
        · rw [show gbTop (c :: cs) = some (d0, c0 + c') from by simp [gbTop, hct, hcs, hdd]] at h
          exact absurd h (by simp)
        · by_cases hlt : d0 < d'
          · rw [show gbTop (c :: cs) = some (d', c') from by simp [gbTop, hct, hcs, hdd, hlt]] at h
            exact absurd h (by simp)
          · rw [show gbTop (c :: cs) = some (d0, c0) from by simp [gbTop, hct, hcs, hdd, hlt]] at h
            exact absurd h (by simp)

omit [DecidableEq R] in
/-- Every term in every bucket has degree `≤` the maximum reported by `gbTop`. -/
lemma gbTop_terms_le : ∀ {buckets : List (MvSparsePoly R nvars)} {d cf},
    gbTop buckets = some (d, cf) → ∀ b ∈ buckets, ∀ t ∈ b.terms, t.1 ≤ d := by
  intro buckets
  induction buckets with
  | nil => intro d cf h; simp [gbTop] at h
  | cons b bs ih =>
    intro d cf h b' hb' t ht
    have hble : ∀ d0, b.terms ≠ [] → multidegree b = d0 → d0 ≤ d → ∀ t ∈ b.terms, t.1 ≤ d :=
      fun d0 _ hmd hled t ht => le_trans (hmd ▸ degree_le_multidegree ht) hled
    cases hbt : b.terms with
    | nil =>
      simp only [gbTop, hbt] at h
      rcases List.mem_cons.mp hb' with rfl | hb'bs
      · rw [hbt] at ht; exact absurd ht List.not_mem_nil
      · exact ih h b' hb'bs t ht
    | cons hd tl =>
      obtain ⟨d0, c0⟩ := hd
      have hmd0 : multidegree b = d0 := by simp [multidegree, hbt]
      cases hbs : gbTop bs with
      | none =>
        simp only [gbTop, hbt, hbs, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rcases List.mem_cons.mp hb' with rfl | hb'bs
        · exact hmd0 ▸ degree_le_multidegree ht
        · rw [gbTop_eq_none hbs b' hb'bs] at ht; exact absurd ht List.not_mem_nil
      | some p =>
        obtain ⟨d', c'⟩ := p
        have htail : ∀ b'' ∈ bs, ∀ t ∈ b''.terms, t.1 ≤ d' := ih hbs
        simp only [gbTop, hbt, hbs] at h
        by_cases hdd : d0 = d'
        · rw [if_pos hdd, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rcases List.mem_cons.mp hb' with rfl | hb'bs
          · exact hmd0 ▸ degree_le_multidegree ht
          · exact le_trans (htail b' hb'bs t ht) (le_of_eq hdd.symm)
        · rw [if_neg hdd] at h
          by_cases hlt : d0 < d'
          · rw [if_pos hlt, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            rcases List.mem_cons.mp hb' with rfl | hb'bs
            · exact le_trans (hmd0 ▸ degree_le_multidegree ht) (le_of_lt hlt)
            · exact htail b' hb'bs t ht
          · rw [if_neg hlt, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            have hd'd0 : d' ≤ d0 := not_lt.mp hlt
            rcases List.mem_cons.mp hb' with rfl | hb'bs
            · exact hmd0 ▸ degree_le_multidegree ht
            · exact le_trans (htail b' hb'bs t ht) hd'd0

/-- The geobucket reduction loop: `buckets` carries the dividend (lazily, as a geobucket), `rem`
accumulates the remainder. Terminates by well-founded recursion on `(gbSum buckets, totalTerms)`. -/
def normalFormFastGo [Div R] (buckets : List (MvSparsePoly R nvars))
    (rem : MvSparsePoly R nvars) (G : List (MvSparsePoly R nvars)) : MvSparsePoly R nvars :=
  match h : gbTop buckets with
  | none => rem
  | some (d, cf) =>
    if hcf : cf = 0 then
      normalFormFastGo (cleanTop d buckets) rem G
    else
      match hfind : G.find? (fun g => !g.terms.isEmpty && MvDegrees.divides (multidegree g) d
          && decide ((g.terms.headD (0, 0)).2 * (cf / (g.terms.headD (0, 0)).2) = cf)) with
      | some g =>
        normalFormFastGo (gbInsert buckets
          (-(sparseMonomial (d - multidegree g) (cf / (g.terms.headD (0, 0)).2) * g))) rem G
      | none =>
        normalFormFastGo (gbInsert buckets (-(sparseMonomial d cf)))
          (rem + sparseMonomial d cf) G
termination_by (gbSum buckets, (buckets.map (fun b => b.terms.length)).sum)
decreasing_by
  · -- cancellation step (cf = 0): same `gbSum`, fewer bucket terms
    have hub : ∀ b ∈ buckets, ∀ t ∈ b.terms, t.1 ≤ d := gbTop_terms_le h
    have hcoeff : MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly (gbSum buckets)) = cf := by
      have hs := gbTop_spec buckets; rw [h] at hs; exact hs.1
    have hsum_eq : gbSum (cleanTop d buckets) = gbSum buckets := by
      rw [cleanTop_sum d buckets hub, hcoeff, hcf, sparseMonomial_zero, sub_zero]
    rw [hsum_eq]
    exact Prod.Lex.right _ (cleanTop_terms_lt d buckets (gbTop_mem h))
  · -- reduction step: `gbSum` strictly drops (leading term cancelled)
    have hlead : (gbSum buckets).terms = (d, cf) :: (gbSum buckets).terms.tail := gbTop_lead h hcf
    have hpred := List.find?_some hfind
    rw [Bool.and_eq_true, Bool.and_eq_true] at hpred
    obtain ⟨⟨hne, hdiv⟩, hcoeffp⟩ := hpred
    have hgne : g.terms ≠ [] := by simpa using hne
    obtain ⟨⟨j0, y0⟩, bs, hgt⟩ := List.exists_cons_of_ne_nil hgne
    have hmdg : multidegree g = j0 := by simp [multidegree, hgt]
    have hy : (g.terms.headD (0, 0)).2 = y0 := by simp [hgt]
    rw [gbInsert_sum, ← sub_eq_add_neg, hmdg, hy]
    refine Prod.Lex.left _ _ (multidegree_sub_cancel hlead hgt ?_ ?_)
    · rw [← hmdg]; exact hdiv
    · rw [← hy]; exact of_decide_eq_true hcoeffp
  · -- move-to-remainder step: `gbSum` strictly drops (leading term removed)
    have hlead : (gbSum buckets).terms = (d, cf) :: (gbSum buckets).terms.tail := gbTop_lead h hcf
    rw [gbInsert_sum, ← sub_eq_add_neg]
    exact Prod.Lex.left _ _ (sub_lead_lex hlead)

/-- **Geobucket reduction** — the runtime fast path for `normalForm`. -/
def normalFormFast [Div R] (f : MvSparsePoly R nvars)
    (G : List (MvSparsePoly R nvars)) : MvSparsePoly R nvars :=
  normalFormFastGo [f] 0 G

/-- **Multi-divisor normal form.** Reduce `f` modulo the divisor list `G`. -/
@[implemented_by normalFormFast]
def normalForm [Div R] (f : MvSparsePoly R nvars) (G : List (MvSparsePoly R nvars)) :
    MvSparsePoly R nvars :=
  match hA : f.terms with
  | [] => 0
  | (i, x) :: as =>
    match h : reduceLeadByList i x f G with
    | some f' => normalForm f' G
    | none => sparseMonomial i x + normalForm (ofSortedList as (sorted_tail hA)) G
termination_by f
decreasing_by
  · exact reduceLeadByList_lex hA h
  · exact tail_terminates hA

/-- **Correctness of the normal form.** `f` and its normal form differ by an element of `⟨G⟩`. -/
theorem normalForm_span [Div R] (f : MvSparsePoly R nvars) (G : List (MvSparsePoly R nvars)) :
    toPoly f - toPoly (normalForm f G) ∈ idealOf G := by
  fun_induction normalForm f G with
  | case1 f hA =>
    have hf0 : toPoly f = 0 := by change toPolyCore f.terms = 0; rw [hA]; rfl
    rw [hf0, toPoly_zero, sub_zero]
    exact Submodule.zero_mem _
  | case2 f i x as hA f' h ih =>
    have h1 := reduceLeadByList_span h
    have hsum := Submodule.add_mem _ h1 ih
    rwa [show toPoly f - toPoly (normalForm f' G)
          = (toPoly f - toPoly f') + (toPoly f' - toPoly (normalForm f' G)) from by ring]
  | case3 f i x as hA h ih =>
    have htf : toPoly f
        = toPoly (sparseMonomial i x) + toPoly (ofSortedList as (sorted_tail hA)) := by
      rw [toPoly_sparseMonomial, toPoly_ofSortedList]
      change toPolyCore f.terms = _
      rw [hA]; rfl
    rw [toPoly_add, htf,
      show (toPoly (sparseMonomial i x) + toPoly (ofSortedList as (sorted_tail hA)))
          - (toPoly (sparseMonomial i x)
            + toPoly (normalForm (ofSortedList as (sorted_tail hA)) G))
        = toPoly (ofSortedList as (sorted_tail hA))
          - toPoly (normalForm (ofSortedList as (sorted_tail hA)) G) from by ring]
    exact ih

/-- **Verified ideal-membership test.** If the normal form is zero, `f` lies in `⟨G⟩`. -/
theorem mem_idealOf_of_normalForm_eq_zero [Div R] (f : MvSparsePoly R nvars)
    (G : List (MvSparsePoly R nvars)) (h : normalForm f G = 0) :
    toPoly f ∈ idealOf G := by
  have hspec := normalForm_span f G
  rwa [h, toPoly_zero, sub_zero] at hspec

-- The leading coefficient (coefficient of the leading monomial).
def leadCoeff (a : MvSparsePoly R nvars) : R := (a.terms.headD (0, 0)).2

-- (`mvDegrees_add_right_cancel` is proved earlier, on the underlying arrays.)

-- If `da ≤ ma`, `db ≤ mb` and `da + db = ma + mb` then both inequalities are equalities.
lemma mvDegrees_le_le_add_eq {da db ma mb : MvDegrees nvars} (h1 : da ≤ ma) (h2 : db ≤ mb)
    (h : da + db = ma + mb) : da = ma ∧ db = mb := by
  have hle1 : da + db ≤ ma + db := mvDegrees_add_le_add h1
  have hle2 : ma + db ≤ ma + mb := by
    rw [add_comm ma db, add_comm ma mb]; exact mvDegrees_add_le_add h2
  have hda : da = ma := mvDegrees_add_right_cancel (le_antisymm hle1 (h.symm ▸ hle2))
  refine ⟨hda, ?_⟩
  have heq : ma + db = ma + mb := hda ▸ h
  rw [add_comm ma db, add_comm ma mb] at heq
  exact mvDegrees_add_right_cancel heq

-- The coefficient at the leading monomial is the leading coefficient.
lemma coeff_at_multidegree {a : MvSparsePoly R nvars} (ha : a.terms ≠ []) :
    MvPolynomial.coeff (MvDegrees.toFinsupp (multidegree a)) (toPoly a) = leadCoeff a := by
  obtain ⟨hd, tl, hA⟩ := List.exists_cons_of_ne_nil ha
  have hmd : multidegree a = hd.1 := by unfold multidegree; rw [hA]; rfl
  have hlc : leadCoeff a = hd.2 := by unfold leadCoeff; rw [hA]; rfl
  rw [hmd, hlc]
  exact coeff_toPolyCore_mem a.sorted (hA ▸ List.mem_cons_self)

-- Every term of `a * b` has degree `≤ multidegree a + multidegree b`.
lemma mul_terms_degLe (a b : MvSparsePoly R nvars) :
    ∀ p ∈ (a * b).terms, p.1 ≤ multidegree a + multidegree b := by
  have hterms : (a * b).terms =
      (ofList (a.terms.flatMap fun p => b.terms.flatMap fun q =>
        [(p.1 + q.1, p.2 * q.2)])).terms := rfl
  rw [hterms]
  apply ofList_degLe
  intro p hp
  simp only [List.mem_flatMap, List.mem_singleton] at hp
  obtain ⟨pa, hpa, qb, hqb, rfl⟩ := hp
  change pa.1 + qb.1 ≤ multidegree a + multidegree b
  calc pa.1 + qb.1 ≤ multidegree a + qb.1 := mvDegrees_add_le_add (degree_le_multidegree hpa)
    _ ≤ multidegree a + multidegree b := by
        rw [add_comm (multidegree a) qb.1, add_comm (multidegree a) (multidegree b)]
        exact mvDegrees_add_le_add (degree_le_multidegree hqb)

-- The leading coefficient of a product is the product of leading coefficients (needs a domain
-- so the leading coefficients do not annihilate).
set_option maxHeartbeats 1000000 in
-- The `MvPolynomial.coeff_mul` antidiagonal sum over `Finsupp` exponents is defeq-heavy.
lemma coeff_leadingTerm_mul [IsDomain R] {a b : MvSparsePoly R nvars}
    (ha : a.terms ≠ []) (hb : b.terms ≠ []) :
    MvPolynomial.coeff (MvDegrees.toFinsupp (multidegree a + multidegree b)) (toPoly (a * b))
      = leadCoeff a * leadCoeff b := by
  have hmem : (MvDegrees.toFinsupp (multidegree a), MvDegrees.toFinsupp (multidegree b)) ∈
      Finset.antidiagonal
        (MvDegrees.toFinsupp (multidegree a) + MvDegrees.toFinsupp (multidegree b)) :=
    Finset.mem_antidiagonal.mpr rfl
  rw [toPoly_mul, toFinsupp_add, MvPolynomial.coeff_mul, Finset.sum_eq_single_of_mem _ hmem]
  · rw [coeff_at_multidegree ha, coeff_at_multidegree hb]
  · intro w hw hwne
    rw [Finset.mem_antidiagonal] at hw
    by_contra hprod
    have h1 : MvPolynomial.coeff w.1 (toPoly a) ≠ 0 := fun h => hprod (by rw [h, zero_mul])
    have h2 : MvPolynomial.coeff w.2 (toPoly b) ≠ 0 := fun h => hprod (by rw [h, mul_zero])
    obtain ⟨pa, hpa, hpa_eq⟩ := coeff_toPolyCore_support h1
    obtain ⟨pb, hpb, hpb_eq⟩ := coeff_toPolyCore_support h2
    rw [hpa_eq, hpb_eq, ← toFinsupp_add, ← toFinsupp_add] at hw
    have hsum : pa.1 + pb.1 = multidegree a + multidegree b := toFinsupp_inj.mp hw
    obtain ⟨e1, e2⟩ := mvDegrees_le_le_add_eq (degree_le_multidegree hpa)
      (degree_le_multidegree hpb) hsum
    exact hwne (Prod.ext (hpa_eq.trans (by rw [e1])) (hpb_eq.trans (by rw [e2])))

-- A nonempty polynomial has a nonzero leading coefficient.
omit [DecidableEq R] in
lemma leadCoeff_ne_zero {a : MvSparsePoly R nvars} (ha : a.terms ≠ []) : leadCoeff a ≠ 0 := by
  obtain ⟨hd, tl, hA⟩ := List.exists_cons_of_ne_nil ha
  have hlc : leadCoeff a = hd.2 := by unfold leadCoeff; rw [hA]; rfl
  rw [hlc]
  exact a.nonzero hd (hA ▸ List.mem_cons_self)

-- The monomial order is multiplicative: `multidegree (a*b) = multidegree a + multidegree b`.
lemma multidegree_mul [IsDomain R] {a b : MvSparsePoly R nvars}
    (ha : a.terms ≠ []) (hb : b.terms ≠ []) :
    multidegree (a * b) = multidegree a + multidegree b := by
  apply le_antisymm
  · cases hab : (a * b).terms with
    | nil =>
      have h0 : multidegree (a * b) = 0 := by unfold multidegree; rw [hab]; rfl
      rw [h0]; exact mvDegrees_zero_le _
    | cons hd tl =>
      have hh : multidegree (a * b) = hd.1 := by unfold multidegree; rw [hab]; rfl
      rw [hh]; exact mul_terms_degLe a b hd (hab ▸ List.mem_cons_self)
  · have hcoeff : MvPolynomial.coeff (MvDegrees.toFinsupp (multidegree a + multidegree b))
        (toPoly (a * b)) ≠ 0 := by
      rw [coeff_leadingTerm_mul ha hb]
      exact mul_ne_zero (leadCoeff_ne_zero ha) (leadCoeff_ne_zero hb)
    obtain ⟨p, hp, hp_eq⟩ := coeff_toPolyCore_support hcoeff
    rw [toFinsupp_inj.mp hp_eq]
    exact degree_le_multidegree hp

lemma leadCoeff_mul [IsDomain R] {a b : MvSparsePoly R nvars}
    (ha : a.terms ≠ []) (hb : b.terms ≠ []) :
    leadCoeff (a * b) = leadCoeff a * leadCoeff b := by
  have hab : (a * b).terms ≠ [] := by
    intro hnil
    have h0 : MvPolynomial.coeff (MvDegrees.toFinsupp (multidegree a + multidegree b))
        (toPoly (a * b)) = 0 := by
      change MvPolynomial.coeff _ (toPolyCore (a * b).terms) = 0
      rw [hnil]; simp [toPolyCore]
    rw [coeff_leadingTerm_mul ha hb] at h0
    exact mul_ne_zero (leadCoeff_ne_zero ha) (leadCoeff_ne_zero hb) h0
  rw [← coeff_at_multidegree hab, multidegree_mul ha hb, coeff_leadingTerm_mul ha hb]

omit [DecidableEq R] in
lemma terms_eq_nil_iff_eq_zero {a : MvSparsePoly R nvars} : a.terms = [] ↔ a = 0 := by
  constructor
  · intro h; apply MvSparsePoly.ext; rw [h]; rfl
  · intro h; rw [h]; rfl

-- Pointwise `≤` on exponents implies `divides`.
lemma divides_of_pointwise {x y : MvDegrees nvars}
    (h : ∀ (k : ℕ) (hk : k < nvars),
      x.degrees[k]'(by rw [x.correct]; exact hk) ≤ y.degrees[k]'(by rw [y.correct]; exact hk)) :
    MvDegrees.divides x y = true := by
  unfold MvDegrees.divides
  rw [Array.all_eq_true]
  intro k hk
  have hsize : (Array.zipWith (fun a b => decide (a ≤ b)) x.degrees y.degrees).size = nvars := by
    rw [Array.size_zipWith]; simp [x.correct, y.correct]
  rw [Array.getElem_zipWith]
  simp only [id_eq, decide_eq_true_eq]
  exact h k (hsize ▸ hk)

lemma divides_self_add (x y : MvDegrees nvars) : MvDegrees.divides x (x + y) = true := by
  apply divides_of_pointwise
  intro k hk
  simp only [show (x + y).degrees = Array.zipWith (· + ·) x.degrees y.degrees from rfl,
    Array.getElem_zipWith]
  exact Nat.le_add_right _ _

-- `b ∣ a` (with `a ≠ 0`) forces `b`'s leading monomial to divide `a`'s.
lemma dvd_imp_divides [IsDomain R] {a b : MvSparsePoly R nvars} (h : b ∣ a) (ha : a.terms ≠ []) :
    MvDegrees.divides (multidegree b) (multidegree a) = true := by
  obtain ⟨d, hd⟩ := h
  have hb : b.terms ≠ [] := fun hbnil => ha
    (by rw [hd, terms_eq_nil_iff_eq_zero.mp hbnil, zero_mul]; rfl)
  have hdd : d.terms ≠ [] := fun hdnil => ha
    (by rw [hd, terms_eq_nil_iff_eq_zero.mp hdnil, mul_zero]; rfl)
  have hmd : multidegree a = multidegree b + multidegree d := by rw [hd]; exact multidegree_mul hb hdd
  rw [hmd]; exact divides_self_add _ _

lemma dvd_imp_leadCoeff_dvd [IsDomain R] {a b : MvSparsePoly R nvars} (h : b ∣ a)
    (ha : a.terms ≠ []) : leadCoeff b ∣ leadCoeff a := by
  obtain ⟨d, hd⟩ := h
  have hb : b.terms ≠ [] := fun hbnil => ha
    (by rw [hd, terms_eq_nil_iff_eq_zero.mp hbnil, zero_mul]; rfl)
  have hdd : d.terms ≠ [] := fun hdnil => ha
    (by rw [hd, terms_eq_nil_iff_eq_zero.mp hdnil, mul_zero]; rfl)
  rw [hd, leadCoeff_mul hb hdd]
  exact dvd_mul_right _ _

instance [Div R] : Div (MvSparsePoly R nvars) where
  div a b := (divRem a b).1

-- If `b ∣ a` then the division is exact: the remainder is zero. Each step that could leave a
-- remainder is ruled out because `b ∣ a` forces `b`'s leading monomial/coefficient to divide
-- `a`'s (via `multidegree_mul` / `leadCoeff_mul`, hence the `[IsDomain R]` requirement).
lemma divRem_rem_zero [IsDomain R] [Div R] [IsExactDiv R] (a b : MvSparsePoly R nvars) :
    b ∣ a → (divRem a b).2 = 0 := by
  fun_induction divRem a b with
  | case1 a i x as j y bs ha hb hDiv c h_exact q' r' hqr ih =>
    intro hdvd
    have hr := ih (dvd_sub hdvd (dvd_mul_left b c))
    rwa [hqr] at hr
  | case2 a i x as j y bs ha hb hDiv h_nexact =>
    intro hdvd
    exfalso
    have ha' : a.terms ≠ [] := by rw [ha]; simp
    have hlcb : leadCoeff b = y := by unfold leadCoeff; rw [hb]; rfl
    have hlca : leadCoeff a = x := by unfold leadCoeff; rw [ha]; rfl
    have hydvd : y ∣ x := by have := dvd_imp_leadCoeff_dvd hdvd ha'; rwa [hlcb, hlca] at this
    exact h_nexact (IsExactDiv.mul_div_cancel hydvd)
  | case3 a i x as j y bs ha hb h_ndiv =>
    intro hdvd
    exfalso
    have ha' : a.terms ≠ [] := by rw [ha]; simp
    have hmda : multidegree a = i := by unfold multidegree; rw [ha]; rfl
    have hmdb : multidegree b = j := by unfold multidegree; rw [hb]; rfl
    have := dvd_imp_divides hdvd ha'
    rw [hmda, hmdb] at this
    exact h_ndiv this
  | case4 a hcond =>
    intro hdvd
    change a = 0
    rcases ha : a.terms with _ | ⟨⟨pi, px⟩, as⟩
    · exact terms_eq_nil_iff_eq_zero.mp ha
    · rcases hb : b.terms with _ | ⟨⟨pj, py⟩, bs⟩
      · rw [terms_eq_nil_iff_eq_zero.mp hb] at hdvd
        exact zero_dvd_iff.mp hdvd
      · exact (hcond pi px as pj py bs ha hb).elim

instance [IsDomain R] [Div R] [IsExactDiv R] : IsExactDiv (MvSparsePoly R nvars) where
  mul_div_cancel {a b} h := by
    have hspec := divRem_spec a b
    rw [divRem_rem_zero a b h, add_zero] at hspec
    exact hspec

instance : DecidableEq (MvSparsePoly R nvars) := fun a b =>
  decidable_of_iff' (a.terms = b.terms) (MvSparsePoly.ext_iff ..)

-- The Finsupp of a single-variable degree array is exactly `Finsupp.single v 1`.
lemma toFinsupp_singleDegree (v : Fin nvars) :
    MvDegrees.toFinsupp (singleDegree v) = Finsupp.single v 1 := by
  ext i
  rw [Finsupp.single_apply]
  unfold MvDegrees.toFinsupp singleDegree
  simp only [Finsupp.onFinset_apply]
  rw [Fin.getElem_fin, ← Array.getElem_toList]
  simp only [List.getElem_set, List.getElem_replicate]
  by_cases h : v = i
  · subst h; simp
  · rw [if_neg h]
    split
    · rename_i hc
      exact absurd (Fin.ext (show (v : ℕ) = (i : ℕ) by omega)) h
    · rfl

-- `X v` maps to Mathlib's `MvPolynomial.X v`.  (Uses `toPolyCore_filter_nonzero` so it
-- also holds in the trivial ring where `1 = 0`.)
@[simp]
theorem toPoly_X (v : Fin nvars) :
    (X v : MvSparsePoly R nvars).toPoly = MvPolynomial.X v := by
  unfold X toPoly ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero]
  simp only [toPolyCore, add_zero]
  rw [toFinsupp_singleDegree]
  rfl

-- The inverse `eval₂` is a left inverse of `toPoly` (round-trip on `MvPolynomial`).
theorem toPoly_eval₂ (p : MvPolynomial (Fin nvars) R) :
    toPoly (p.eval₂ (algebraMap R (MvSparsePoly R nvars)) X) = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C]
    exact toPoly_C a
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, toPoly_add, hp, hq]
  | mul_X p v ih =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, toPoly_mul, ih, toPoly_X]

noncomputable def toPolyEquiv : MvSparsePoly R nvars ≃ₐ[R] MvPolynomial (Fin nvars) R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap R (MvSparsePoly R nvars)) X
  left_inv p := toPoly_injective (toPoly_eval₂ (toPoly p))
  right_inv p := toPoly_eval₂ p
  map_add' := toPoly_add
  map_mul' := toPoly_mul
  commutes' r := toPoly_C r

@[simp]
theorem ofPoly_X (v : Fin nvars) :
    toPolyEquiv.symm (MvPolynomial.X v) = (X v : MvSparsePoly R nvars) := by
  have h : toPolyEquiv (X v : MvSparsePoly R nvars) = MvPolynomial.X v := toPoly_X v
  rw [← h, toPolyEquiv.symm_apply_apply]

/-! ### Evaluation

A *computable* evaluation map (`toPoly` is `noncomputable`), proven to agree with Mathlib's
`MvPolynomial.eval` through the `toPoly` bridge. -/

/-- Evaluate the monomial `Xᵈ` at a point `vs` by reading the exponent array directly. -/
def evalMonomial (vs : Fin nvars → R) (d : MvDegrees nvars) : R :=
  ∏ k : Fin nvars, vs k ^ d.degrees[(k : ℕ)]'(by rw [d.correct]; exact k.2)

/-- Evaluate a term-list at `vs`. -/
def evalCore (vs : Fin nvars → R) : List (MvDegrees nvars × R) → R
  | [] => 0
  | (d, c) :: t => c * evalMonomial vs d + evalCore vs t

/-- Runtime fast path for `eval`: precompute, per variable, a table of powers `vs k ^ e` once, then
evaluate each monomial by table lookup instead of re-exponentiating. Same result as `eval` (wired in
via `@[implemented_by]`), but avoids the repeated `^` of the naive `evalMonomial`. -/
def evalFast (vs : Fin nvars → R) (p : MvSparsePoly R nvars) : R :=
  haveI : Inhabited R := ⟨0⟩
  Id.run do
  let mut maxExp : ℕ := 0
  for t in p.terms do
    for e in t.1.degrees do
      maxExp := Nat.max maxExp e
  let powTbl : Array (Array R) := (List.finRange nvars).toArray.map (fun k => Id.run do
    let mut a : Array R := #[1]
    let mut cur : R := 1
    for _ in [0:maxExp] do
      cur := cur * vs k
      a := a.push cur
    pure a)
  let mut acc : R := 0
  for t in p.terms do
    let mut m : R := t.2
    for k in [0:nvars] do
      m := m * (powTbl[k]!)[t.1.degrees[k]!]!
    acc := acc + m
  pure acc

/-- Evaluate a polynomial at a point `vs : Fin nvars → R`. -/
@[implemented_by evalFast]
def eval (vs : Fin nvars → R) (p : MvSparsePoly R nvars) : R := evalCore vs p.terms

omit [DecidableEq R] in
theorem evalCore_eq_eval_toPolyCore (vs : Fin nvars → R) :
    ∀ l, evalCore vs l = MvPolynomial.eval vs (toPolyCore l)
  | [] => by simp [evalCore, toPolyCore]
  | (d, c) :: t => by
    have hm : evalMonomial vs d = ∏ i, vs i ^ (MvDegrees.toFinsupp d) i :=
      Finset.prod_congr rfl (fun _ _ => rfl)
    rw [evalCore, toPolyCore, map_add, MvPolynomial.eval_monomial,
      evalCore_eq_eval_toPolyCore vs t, Finsupp.prod_fintype _ _ (fun i => pow_zero (vs i)), hm]

omit [DecidableEq R] in
/-- `eval` agrees with Mathlib's `MvPolynomial.eval` through the bridge `toPoly`. -/
theorem eval_eq_eval_toPoly (vs : Fin nvars → R) (p : MvSparsePoly R nvars) :
    eval vs p = MvPolynomial.eval vs (toPoly p) :=
  evalCore_eq_eval_toPolyCore vs p.terms

@[simp] theorem eval_C (vs : Fin nvars → R) (r : R) : eval vs (C r) = r := by
  rw [eval_eq_eval_toPoly, toPoly_C, MvPolynomial.eval_C]

@[simp] theorem eval_X (vs : Fin nvars → R) (i : Fin nvars) : eval vs (X i) = vs i := by
  rw [eval_eq_eval_toPoly, toPoly_X, MvPolynomial.eval_X]

theorem eval_add (vs : Fin nvars → R) (p q : MvSparsePoly R nvars) :
    eval vs (p + q) = eval vs p + eval vs q := by
  rw [eval_eq_eval_toPoly, toPoly_add, map_add, eval_eq_eval_toPoly, eval_eq_eval_toPoly]

theorem eval_mul (vs : Fin nvars → R) (p q : MvSparsePoly R nvars) :
    eval vs (p * q) = eval vs p * eval vs q := by
  rw [eval_eq_eval_toPoly, toPoly_mul, map_mul, eval_eq_eval_toPoly, eval_eq_eval_toPoly]

-- ==========================================================================
-- BRIDGE TO MATHLIB'S `MonomialOrder`
--
-- Mathlib's `MonomialOrder σ` bundles a synonym type `syn`, an additive equivalence
-- `(σ →₀ ℕ) ≃+ syn`, monotone w.r.t. the divisibility order, into a linearly ordered
-- cancellative, well-founded additive monoid. Our admissible order lives on `MvDegrees nvars`
-- (a `WOrdering`), and `MvDegrees nvars ≃+ (Fin nvars →₀ ℕ)`. Transporting along that equiv
-- packages our order as a genuine `MonomialOrder (Fin nvars)`, so every result we prove
-- computationally can be consumed by the rest of Mathlib's Gröbner / initial-ideal API.
-- ==========================================================================

/-- The inverse of `MvDegrees.toFinsupp`: read a finitely-supported exponent vector back into the
fixed-size array representation. Computable (unlike `toFinsupp`). -/
def MvDegrees.ofFinsupp (f : Fin nvars →₀ ℕ) : MvDegrees nvars where
  degrees := Array.ofFn (fun k : Fin nvars => f k)
  correct := by simp
  totalDegree := (Array.ofFn (fun k : Fin nvars => f k)).foldl (· + ·) 0
  totalDegree_eq := rfl

@[simp] lemma toFinsupp_ofFinsupp (f : Fin nvars →₀ ℕ) :
    MvDegrees.toFinsupp (MvDegrees.ofFinsupp f) = f := by
  ext v
  unfold MvDegrees.toFinsupp MvDegrees.ofFinsupp
  simp

lemma ofFinsupp_toFinsupp (d : MvDegrees nvars) :
    MvDegrees.ofFinsupp (MvDegrees.toFinsupp d) = d :=
  toFinsupp_inj.mp (toFinsupp_ofFinsupp _)

lemma ofFinsupp_add (f g : Fin nvars →₀ ℕ) :
    MvDegrees.ofFinsupp (f + g) = MvDegrees.ofFinsupp f + MvDegrees.ofFinsupp g :=
  toFinsupp_inj.mp <| by rw [toFinsupp_add, toFinsupp_ofFinsupp, toFinsupp_ofFinsupp,
    toFinsupp_ofFinsupp]

/-- Our `MvDegrees` order is a cancellative ordered additive monoid: addition is monotone
(`WOrdering.add_le_add`) and strictly monotone (so order cancels). -/
instance : IsOrderedCancelAddMonoid (MvDegrees nvars) where
  add_le_add_left a b hab c := mvDegrees_add_le_add hab
  le_of_add_le_add_left a b c hbc := by
    by_contra h
    exact absurd hbc (not_le.mpr (mvDegrees_add_lt_add_left (not_le.mp h)))

/-- The admissible order is well-founded (this is exactly `WOrdering.wf`). -/
instance : WellFoundedLT (MvDegrees nvars) := ⟨WOrdering.wf⟩

/-- The additive equivalence `(Fin nvars →₀ ℕ) ≃+ MvDegrees nvars` underlying the bridge. -/
noncomputable def finsuppEquivMvDegrees : (Fin nvars →₀ ℕ) ≃+ MvDegrees nvars where
  toFun := MvDegrees.ofFinsupp
  invFun := MvDegrees.toFinsupp
  left_inv := toFinsupp_ofFinsupp
  right_inv := ofFinsupp_toFinsupp
  map_add' := ofFinsupp_add

@[simp] lemma finsuppEquivMvDegrees_apply (f : Fin nvars →₀ ℕ) :
    finsuppEquivMvDegrees f = MvDegrees.ofFinsupp f := rfl

/-- The bridge is monotone: a divides b (pointwise `≤`) implies `a ⪯ b` in our order. This is the
admissibility condition `0 ≤ x` plus monotonicity of `+`. -/
lemma finsuppEquivMvDegrees_monotone :
    Monotone (finsuppEquivMvDegrees : (Fin nvars →₀ ℕ) → MvDegrees nvars) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := exists_add_of_le hab
  simp only [finsuppEquivMvDegrees_apply, ofFinsupp_add]
  simpa [add_comm] using
    mvDegrees_add_le_add (z := MvDegrees.ofFinsupp a) (mvDegrees_zero_le (MvDegrees.ofFinsupp c))

/-- **The bridge.** Any `WOrdering` (admissible monomial order in our sense) is a Mathlib
`MonomialOrder`. The synonym type is `MvDegrees nvars`, carrying our order; the linear,
cancellative, well-founded structure and the monotone additive equivalence are exactly the
fields established above. -/
noncomputable def WOrdering.toMonomialOrder : MonomialOrder (Fin nvars) where
  syn := MvDegrees nvars
  toSyn := finsuppEquivMvDegrees
  toSyn_monotone := finsuppEquivMvDegrees_monotone

/-- Sanity check: the order Mathlib reads off the bridge is exactly our `WOrdering` order,
transported along `ofFinsupp`. -/
lemma toMonomialOrder_le_iff (a b : Fin nvars →₀ ℕ) :
    WOrdering.toMonomialOrder.toSyn a ≤ WOrdering.toMonomialOrder.toSyn b ↔
    MvDegrees.ofFinsupp a ≤ MvDegrees.ofFinsupp b := Iff.rfl

-- ==========================================================================
-- DICTIONARY: our `multidegree`/`leadCoeff` vs Mathlib's `MonomialOrder.degree`/`leadingCoeff`
--
-- With the bridge in hand we can translate our
-- computable leading-term data into Mathlib's
-- abstract notions, transported across `toPoly`. After this,
-- anything Mathlib proves generically
-- about `MonomialOrder.degree`/`leadingCoeff` (degree of a product,
-- leading-coeff multiplicativity,
-- initial ideals, …) specialises to our computable polynomials for free.
-- ==========================================================================

@[simp] lemma toMonomialOrder_toSyn_apply (c : Fin nvars →₀ ℕ) :
    WOrdering.toMonomialOrder.toSyn c = MvDegrees.ofFinsupp c := rfl

/-- The coefficient of `toPoly a` at the leading exponent vector is the leading coefficient. -/
lemma coeff_toPoly_multidegree (a : MvSparsePoly R nvars) :
    MvPolynomial.coeff (MvDegrees.toFinsupp (multidegree a)) (toPoly a) = leadCoeff a := by
  rcases h : a.terms with _ | ⟨⟨d, v⟩, tl⟩
  · simp [multidegree, leadCoeff, toPoly, toPolyCore, h]
  · have hmd : multidegree a = d := by simp [multidegree, h]
    have hlc : leadCoeff a = v := by simp [leadCoeff, h]
    rw [hmd, hlc, toPoly]
    exact coeff_toPolyCore_mem a.sorted (by rw [h]; simp)

omit [DecidableEq R] in
/-- Every exponent vector occurring in `toPoly a` comes from one of its terms. -/
lemma mem_support_toPolyCore : ∀ {l : List (MvDegrees nvars × R)} {c : Fin nvars →₀ ℕ},
    c ∈ (toPolyCore l).support → ∃ p ∈ l, MvDegrees.toFinsupp p.1 = c := by
  intro l
  induction l with
  | nil => intro c hc; simp [toPolyCore] at hc
  | cons hd tl ih =>
    intro c hc
    obtain ⟨e, w⟩ := hd
    dsimp only [toPolyCore] at hc
    rcases Finset.mem_union.mp (MvPolynomial.support_add hc) with h1 | h2
    · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at h1
      by_cases hc' : MvDegrees.toFinsupp e = c
      · exact ⟨(e, w), List.mem_cons_self, hc'⟩
      · rw [if_neg hc'] at h1; exact absurd rfl h1
    · obtain ⟨p, hp, hpc⟩ := ih h2
      exact ⟨p, List.mem_cons_of_mem _ hp, hpc⟩

omit [DecidableEq R] in
/-- Support bound: every exponent vector of `toPoly a` is `≤` the multidegree. -/
lemma support_toPoly_le_multidegree {a : MvSparsePoly R nvars} {c : Fin nvars →₀ ℕ}
    (hc : c ∈ (toPoly a).support) : MvDegrees.ofFinsupp c ≤ multidegree a := by
  obtain ⟨p, hp, rfl⟩ := mem_support_toPolyCore hc
  rw [ofFinsupp_toFinsupp]
  exact degree_le_multidegree hp

/-- **Degree agrees.** Mathlib's monomial-order degree of `toPoly a` is the image, under
`toFinsupp`, of our computable `multidegree`. -/
lemma toMonomialOrder_degree (a : MvSparsePoly R nvars) :
    WOrdering.toMonomialOrder.degree (toPoly a) = MvDegrees.toFinsupp (multidegree a) := by
  rcases h : a.terms with _ | ⟨⟨d, v⟩, tl⟩
  · have h0 : toPoly a = 0 := by simp [toPoly, h, toPolyCore]
    rw [h0, MonomialOrder.degree_zero]
    simp [multidegree, h, toFinsupp_zero]
  · have hv : v ≠ 0 := a.nonzero (d, v) (by rw [h]; simp)
    have hmem : MvDegrees.toFinsupp (multidegree a) ∈ (toPoly a).support := by
      rw [MvPolynomial.mem_support_iff, coeff_toPoly_multidegree,
        show leadCoeff a = v from by simp [leadCoeff, h]]
      exact hv
    apply WOrdering.toMonomialOrder.toSyn.injective
    refine le_antisymm ?_ (WOrdering.toMonomialOrder.le_degree hmem)
    refine (WOrdering.toMonomialOrder.degree_le_iff).mpr (fun c hc => ?_)
    simp only [toMonomialOrder_toSyn_apply, ofFinsupp_toFinsupp]
    exact support_toPoly_le_multidegree hc

/-- **Leading coefficient agrees.** Mathlib's leading coefficient of `toPoly a` is our
computable `leadCoeff a`. -/
lemma toMonomialOrder_leadingCoeff (a : MvSparsePoly R nvars) :
    WOrdering.toMonomialOrder.leadingCoeff (toPoly a) = leadCoeff a := by
  unfold MonomialOrder.leadingCoeff
  rw [toMonomialOrder_degree, coeff_toPoly_multidegree]

-- Degree monotonicity, harvested from Mathlib through the bridge ───────────
-- `multidegree_add_le` is *derived* from
-- Mathlib's `MonomialOrder.degree_add_le` via the bridge —
-- we don't reprove it. `normalForm_multidegree_le`
-- then shows our computable reduction never
-- raises the multidegree (a step toward proving
-- `normalForm` yields a genuinely reduced remainder).

/-- The multidegree of a sum is `≤` the max of the multidegrees.
  Pulled back from Mathlib's
`MonomialOrder.degree_add_le` along `toMonomialOrder_degree`. -/
lemma multidegree_add_le (a b : MvSparsePoly R nvars) :
    multidegree (a + b) ≤ multidegree a ⊔ multidegree b := by
  have h := WOrdering.toMonomialOrder.degree_add_le (f := toPoly a) (g := toPoly b)
  rw [← toPoly_add, toMonomialOrder_degree, toMonomialOrder_degree, toMonomialOrder_degree,
    toMonomialOrder_toSyn_apply, toMonomialOrder_toSyn_apply, toMonomialOrder_toSyn_apply,
    ofFinsupp_toFinsupp, ofFinsupp_toFinsupp, ofFinsupp_toFinsupp] at h
  exact h

/-- The multidegree of `sparseMonomial i x` is `i` (when `x ≠ 0`). -/
lemma multidegree_sparseMonomial (i : MvDegrees nvars) {x : R} (hx : x ≠ 0) :
    multidegree (sparseMonomial i x) = i := by
  simp [multidegree, sparseMonomial, ofSortedList, List.filter, hx]

/-- **`normalForm` never raises the multidegree.** -/
lemma normalForm_multidegree_le [Div R] (f : MvSparsePoly R nvars)
    (G : List (MvSparsePoly R nvars)) : multidegree (normalForm f G) ≤ multidegree f := by
  fun_induction normalForm f G with
  | case1 f hA =>
    rw [show multidegree (0 : MvSparsePoly R nvars) = 0 from rfl]
    exact mvDegrees_zero_le _
  | case2 f i x as hA f' h ih =>
    refine le_trans ih ?_
    rcases Prod.lex_def.mp (reduceLeadByList_lex hA h) with h1 | ⟨h1, _⟩
    · exact le_of_lt h1
    · exact le_of_eq h1
  | case3 f i x as hA h ih =>
    have hx : x ≠ 0 := f.nonzero (i, x) (by rw [hA]; simp)
    have hmdf : multidegree f = i := by simp [multidegree, hA]
    have htail_le : multidegree (ofSortedList as (sorted_tail hA)) ≤ i := by
      have hlt_as : ∀ p ∈ as, p.1 < i := (List.pairwise_cons.mp (hA ▸ f.sorted)).1
      cases hf : (ofSortedList as (sorted_tail hA)).terms with
      | nil => rw [multidegree, hf]; exact mvDegrees_zero_le i
      | cons p ps =>
        have hp_mem : p ∈ (ofSortedList as (sorted_tail hA)).terms := by
          rw [hf]; exact List.mem_cons_self
        have hmd_tail : multidegree (ofSortedList as (sorted_tail hA)) = p.1 := by
          simp [multidegree, hf]
        rw [hmd_tail]
        exact le_of_lt (hlt_as p (List.mem_of_mem_filter hp_mem))
    calc multidegree (sparseMonomial i x + normalForm (ofSortedList as (sorted_tail hA)) G)
        ≤ multidegree (sparseMonomial i x)
            ⊔ multidegree (normalForm (ofSortedList as (sorted_tail hA)) G) :=
          multidegree_add_le _ _
      _ ≤ i := by rw [multidegree_sparseMonomial i hx]; exact sup_le le_rfl (le_trans ih htail_le)
      _ = multidegree f := hmdf.symm

-- ── `normalForm` produces a *reduced* remainder ─────────────────────────────
-- This is the extra property Mathlib's `MonomialOrder.div_set` carries: no leading monomial of any
-- divisor divides any term of the remainder. Together with `normalForm_span` it makes our
-- computable `normalForm` a genuine normal form (a witness for `div_set`).

/-- `normalForm` of a term-less polynomial is `0`. -/
lemma normalForm_nil [Div R] {f : MvSparsePoly R nvars}
    {G : List (MvSparsePoly R nvars)} (hf : f.terms = []) : normalForm f G = 0 := by
  rw [normalForm]; split <;> simp_all

/-- A term `(d, c)` is **reducible** by `G` if some `g ∈ G` has a leading term that divides `d`
with a matching leading coefficient — exactly the condition under which `reduceLeadByList` fires. -/
def ReducibleBy [Div R] (G : List (MvSparsePoly R nvars)) (d : MvDegrees nvars) (c : R) : Prop :=
  ∃ g ∈ G, ∃ (j : MvDegrees nvars) (y : R) (bs : List (MvDegrees nvars × R)),
    g.terms = (j, y) :: bs ∧ MvDegrees.divides j d = true ∧ y * (c / y) = c

/-- If the leading-term search returns `none`, the term `(i, x)` is irreducible by `G`. -/
lemma reduceLeadByList_none_not_reducible [Div R] {i : MvDegrees nvars} {x : R}
    {f : MvSparsePoly R nvars} : ∀ {G : List (MvSparsePoly R nvars)},
    reduceLeadByList i x f G = none → ¬ ReducibleBy G i x := by
  intro G
  induction G with
  | nil => intro _ hred; obtain ⟨g, hg, -⟩ := hred; exact absurd hg List.not_mem_nil
  | cons g gs ih =>
    intro h hred
    -- From `h`, peel off: `gs` also reduces to `none`, and `g` itself does not match `(i, x)`.
    have key : reduceLeadByList i x f gs = none ∧
        ¬ ∃ (j : MvDegrees nvars) (y : R) (bs : List (MvDegrees nvars × R)),
          g.terms = (j, y) :: bs ∧ MvDegrees.divides j i = true ∧ y * (x / y) = x := by
      cases hgt : g.terms with
      | nil =>
        have heq : reduceLeadByList i x f (g :: gs) = reduceLeadByList i x f gs := by
          conv_lhs => unfold reduceLeadByList
          rw [hgt]
        rw [heq] at h
        refine ⟨h, ?_⟩
        rintro ⟨j, y, bs, hjt, -, -⟩; exact absurd hjt (by simp)
      | cons hd tl =>
        obtain ⟨j0, y0⟩ := hd
        simp only [reduceLeadByList, hgt] at h
        by_cases hd0 : MvDegrees.divides j0 i
        · by_cases hc0 : y0 * (x / y0) = x
          · rw [if_pos hd0, if_pos hc0] at h; exact absurd h (by simp)
          · refine ⟨by rwa [if_pos hd0, if_neg hc0] at h, ?_⟩
            rintro ⟨j, y, bs, hjt, -, hcoeff⟩
            simp only [List.cons.injEq, Prod.mk.injEq] at hjt
            obtain ⟨⟨rfl, rfl⟩, -⟩ := hjt
            exact hc0 hcoeff
        · refine ⟨by rwa [if_neg hd0] at h, ?_⟩
          rintro ⟨j, y, bs, hjt, hdiv, -⟩
          simp only [List.cons.injEq, Prod.mk.injEq] at hjt
          obtain ⟨⟨rfl, rfl⟩, -⟩ := hjt
          exact hd0 hdiv
    obtain ⟨hgs, hg_nomatch⟩ := key
    obtain ⟨g', hg', j, y, bs, hg't, hdiv, hcoeff⟩ := hred
    rcases List.mem_cons.mp hg' with rfl | hg'gs
    · exact hg_nomatch ⟨j, y, bs, hg't, hdiv, hcoeff⟩
    · exact ih hgs ⟨g', hg'gs, j, y, bs, hg't, hdiv, hcoeff⟩

/-- `addCore [(i, x)] l = (i, x) :: l` when every degree in `l` is `< i`. -/
lemma addCore_singleton_cons {i : MvDegrees nvars} {x : R} {l : List (MvDegrees nvars × R)}
    (hl : ∀ t ∈ l, t.1 < i) : addCore [(i, x)] l = (i, x) :: l := by
  cases l with
  | nil => simp [addCore]
  | cons p ps =>
    obtain ⟨j, b⟩ := p
    have hji : j < i := hl (j, b) List.mem_cons_self
    rw [addCore]
    simp only [if_neg (not_lt.mpr hji.le), if_pos hji]
    rw [addCore]

/-- The terms of `sparseMonomial i x + q` are `(i, x) :: q.terms`, when `x ≠ 0` and every degree
in `q` is `< i` (so no merging occurs). -/
lemma add_sparseMonomial_terms [Div R] {i : MvDegrees nvars} {x : R} {q : MvSparsePoly R nvars}
    (hx : x ≠ 0) (hq : ∀ t ∈ q.terms, t.1 < i) :
    (sparseMonomial i x + q).terms = (i, x) :: q.terms := by
  change (addCore (sparseMonomial i x).terms q.terms).filter (·.2 ≠ 0) = _
  have hsm : (sparseMonomial i x).terms = [(i, x)] := by simp [sparseMonomial, ofSortedList, hx]
  rw [hsm, addCore_singleton_cons hq, List.filter_eq_self.mpr]
  intro t ht
  rcases List.mem_cons.mp ht with rfl | htq
  · simpa using hx
  · simpa using q.nonzero t htq

/-- **`normalForm` yields a reduced remainder**: no leading monomial of any `g ∈ G` divides (with
matching leading coefficient) any term of `normalForm f G`. -/
theorem normalForm_reduced [Div R] (f : MvSparsePoly R nvars)
    (G : List (MvSparsePoly R nvars)) :
    ∀ t ∈ (normalForm f G).terms, ¬ ReducibleBy G t.1 t.2 := by
  fun_induction normalForm f G with
  | case1 f hA => intro t ht; exact absurd ht List.not_mem_nil
  | case2 f i x as hA f' h ih => intro t ht; exact ih t ht
  | case3 f i x as hA h ih =>
    intro t ht
    have hx : x ≠ 0 := f.nonzero (i, x) (by rw [hA]; simp)
    have hq_lt : ∀ s ∈ (normalForm (ofSortedList as (sorted_tail hA)) G).terms, s.1 < i := by
      intro s hs
      have htail_terms_lt : ∀ u ∈ (ofSortedList as (sorted_tail hA)).terms, u.1 < i := fun u hu =>
        ((List.pairwise_cons.mp (hA ▸ f.sorted)).1) u (List.mem_of_mem_filter hu)
      have htail_ne : (ofSortedList as (sorted_tail hA)).terms ≠ [] := by
        intro he; rw [normalForm_nil he] at hs; exact absurd hs List.not_mem_nil
      have hmdtail : multidegree (ofSortedList as (sorted_tail hA)) < i := by
        obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil htail_ne
        have hmd : multidegree (ofSortedList as (sorted_tail hA)) = p.1 := by simp [multidegree, hps]
        rw [hmd]; exact htail_terms_lt p (hps ▸ List.mem_cons_self)
      exact lt_of_le_of_lt (le_trans (degree_le_multidegree hs)
        (normalForm_multidegree_le _ G)) hmdtail
    rw [add_sparseMonomial_terms hx hq_lt] at ht
    rcases List.mem_cons.mp ht with rfl | htq
    · exact reduceLeadByList_none_not_reducible h
    · exact ih t htq

-- ==========================================================================
-- BUCHBERGER'S S-POLYNOMIAL CRITERION (computational verifier)
--
-- `sPoly g₁ g₂` is the S-polynomial: with leading monomials `c₁·x^α₁`, `c₂·x^α₂` and
-- `γ = lcm α₁ α₂`, it is `(x^(γ-α₁)/c₁)·g₁ - (x^(γ-α₂)/c₂)·g₂`, engineered so its two leading
-- terms cancel. `isGroebnerBasis G` runs the criterion:
-- every pairwise S-polynomial reduces to `0`
-- modulo `G` (via `normalForm`).
--
-- WHAT IS PROVED:
--   • `sPoly_mem_ideal` — each S-polynomial lies in `⟨G⟩`. Combined with
--     `mem_idealOf_of_normalForm_eq_zero`, the **sound** direction holds: if `normalForm f G = 0`
--     then `f ∈ ⟨G⟩`, for *any* `G`.
--   • `sPoly_toPoly_of_coprime` — Buchberger's First (gcd) Criterion, algebraic core: when the
--     leading monomials are coprime, `S(f,g)` is the explicit cross-combination
--     `(x^β/lc f)·f − (x^α/lc g)·g` (a standard representation). `isGroebnerBasis` uses the
--     `coprimeLead` test to prune such pairs.
--
-- WHAT IS NOT PROVED (and deliberately carries no `sorry`): the soundness of the *criterion*
-- itself — that `isGroebnerBasis G = true` implies `G` is a genuine Gröbner basis, hence that
-- `normalForm` becomes a *complete* membership decision (`f ∈ ⟨G⟩ ↔ normalForm f G = 0`). That is
-- Buchberger's theorem; its formalisation needs the theory of leading-term ideals, Dickson's
-- lemma, and uniqueness of remainders — a major development absent even from current Mathlib. The
-- coprime pruning likewise relies on that theory for its "reduces to 0" conclusion (only the
-- algebraic identity is formalised). So `isGroebnerBasis` is an honest *computational* verifier.
-- ==========================================================================

/-- Pointwise maximum of two exponent vectors — the lcm of the corresponding monomials. -/
def MvDegrees.lcm (a b : MvDegrees nvars) : MvDegrees nvars where
  degrees := Array.zipWith max a.degrees b.degrees
  correct := by simp [a.correct, b.correct]
  totalDegree := (Array.zipWith max a.degrees b.degrees).foldl (· + ·) 0
  totalDegree_eq := rfl

/-- The S-polynomial of `g₁` and `g₂` (over a field, using `[Div R]` for the leading coefficients).
Its two leading terms are constructed to cancel. -/
def sPoly [Div R] (g₁ g₂ : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  sparseMonomial (MvDegrees.lcm (multidegree g₁) (multidegree g₂) - multidegree g₁)
      (1 / leadCoeff g₁) * g₁
    - sparseMonomial (MvDegrees.lcm (multidegree g₁) (multidegree g₂) - multidegree g₂)
      (1 / leadCoeff g₂) * g₂

/-- Each S-polynomial of members of `G` lies in the ideal `⟨G⟩` (it is an explicit combination
`m₁·g₁ - m₂·g₂`). -/
lemma sPoly_mem_ideal [Div R] {G : List (MvSparsePoly R nvars)} {g₁ g₂ : MvSparsePoly R nvars}
    (h₁ : g₁ ∈ G) (h₂ : g₂ ∈ G) : toPoly (sPoly g₁ g₂) ∈ idealOf G := by
  unfold sPoly
  rw [toPoly_sub, toPoly_mul, toPoly_mul]
  exact Submodule.sub_mem _
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g₁, h₁, rfl⟩))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g₂, h₂, rfl⟩))

-- ── Buchberger's First (gcd) Criterion ──────────────────────────────────────
-- When the leading monomials of `f` and `g` are coprime (share no variable), `S(f,g)`
-- automatically reduces to `0`, so the pair may be skipped. We prove the *algebraic core* of the
-- criterion (`sPoly_toPoly_of_coprime`) and use the coprimeness test to prune the verifier.

/-- `a` divides `a + b` (every exponent of `a` is `≤` the corresponding exponent of `a + b`). -/
lemma MvDegrees.divides_add_right (a b : MvDegrees nvars) :
    MvDegrees.divides a (a + b) = true := by
  unfold MvDegrees.divides
  rw [Array.all_eq_true]
  intro k hk
  simp only [show (a + b).degrees = Array.zipWith (· + ·) a.degrees b.degrees from rfl,
    Array.getElem_zipWith, id_eq, decide_eq_true_eq]
  exact Nat.le_add_right _ _

/-- Truncated subtraction cancels addition on the left: `(a + b) - a = b`. -/
lemma MvDegrees.add_sub_cancel_left (a b : MvDegrees nvars) : (a + b) - a = b := by
  apply mvDegrees_add_right_cancel (c := a)
  rw [MvDegrees.sub_add_cancel_of_divides (MvDegrees.divides_add_right a b), add_comm a b]

/-- The leading monomials of `f` and `g` are **coprime**: their lcm equals their product. -/
def MvDegrees.Coprime (a b : MvDegrees nvars) : Prop := MvDegrees.lcm a b = a + b

/-- **Buchberger's First (gcd) Criterion — algebraic core.** When the leading monomials are
coprime (`lcm = α + β`), the S-polynomial is exactly the "cross-multiply" combination
`(x^β / lc f)·f − (x^α / lc g)·g`: each operand is multiplied by the *other's* leading monomial.
This exhibits `S(f,g)` as a combination of `f` and `g` whose two top terms `x^(α+β)` cancel — a
standard representation, the algebraic content behind the criterion's "reduces to 0" conclusion. -/
theorem sPoly_toPoly_of_coprime [Div R] {f g : MvSparsePoly R nvars}
    (hcop : MvDegrees.Coprime (multidegree f) (multidegree g)) :
    toPoly (sPoly f g)
      = MvPolynomial.monomial (MvDegrees.toFinsupp (multidegree g)) (1 / leadCoeff f) * toPoly f
        - MvPolynomial.monomial
         (MvDegrees.toFinsupp (multidegree f)) (1 / leadCoeff g) * toPoly g := by
  unfold MvDegrees.Coprime at hcop
  unfold sPoly
  rw [hcop, MvDegrees.add_sub_cancel_left, add_comm (multidegree f) (multidegree g),
    MvDegrees.add_sub_cancel_left, toPoly_sub, toPoly_mul, toPoly_mul,
    toPoly_sparseMonomial, toPoly_sparseMonomial]

/-- Computable coprimeness test for the leading monomials of `f` and `g`. -/
def coprimeLead (f g : MvSparsePoly R nvars) : Bool :=
  decide (MvDegrees.lcm (multidegree f) (multidegree g) = multidegree f + multidegree g)

/-- All unordered pairs `(gᵢ, gⱼ)`, `i < j`, drawn from a list. -/
def allPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | g :: gs => gs.map (g, ·) ++ allPairs gs

/-- **Buchberger's criterion (computational), with the
 -- First-Criterion optimisation.** `true` iff
 every pair from `G` either has coprime leading terms
-- (skipped — `sPoly_toPoly_of_coprime` is the
proved algebraic justification) or has its S-polynomial reduce
-- to `0` modulo `G`. Meant to be *run*
(its result is a `Bool`); see the section comment on the status
-- of its soundness as a Gröbner test.
The coprime pruning avoids the expensive `normalForm` on
-- pairs the criterion guarantees. -/
def isGroebnerBasis [Div R] (G : List (MvSparsePoly R nvars)) : Bool :=
  (allPairs G).all (fun p =>
    coprimeLead p.1 p.2 || decide (normalForm (sPoly p.1 p.2) G = 0))

-- ==========================================================================
-- FORMAL PARTIAL DERIVATIVE
--
-- `pderiv k p` differentiates `p` with respect to the `k`-th variable, computably. We prove it
-- agrees with Mathlib's `MvPolynomial.pderiv` across `toPoly`, so the computation is certified.
-- (Foundation for square-free factorisation via `gcd(f, ∂f).)
-- ==========================================================================

/-- Value of `toFinsupp d` at coordinate `v` is the `v`-th exponent. -/
lemma toFinsupp_apply (d : MvDegrees nvars) (v : Fin nvars) :
    MvDegrees.toFinsupp d v = d.degrees[(v : ℕ)]'(by rw [d.correct]; exact v.2) := by
  simp only [MvDegrees.toFinsupp, Finsupp.onFinset_apply, Fin.getElem_fin]

/-- `toFinsupp` turns truncated subtraction into `Finsupp` subtraction. -/
lemma toFinsupp_sub (a b : MvDegrees nvars) :
    MvDegrees.toFinsupp (a - b) = MvDegrees.toFinsupp a - MvDegrees.toFinsupp b := by
  ext v
  simp only [Finsupp.tsub_apply, toFinsupp_apply,
    show (a - b).degrees = Array.zipWith (· - ·) a.degrees b.degrees from rfl, Array.getElem_zipWith]

lemma toFinsupp_sub_singleDegree (d : MvDegrees nvars) (k : Fin nvars) :
    MvDegrees.toFinsupp (d - singleDegree k) = MvDegrees.toFinsupp d - Finsupp.single k 1 := by
  rw [toFinsupp_sub, toFinsupp_singleDegree]

/-- **Computable partial derivative** with respect to variable `k`: differentiate each monomial
`c·x^d` to `(c·d_k)·x^(d - e_k)`. Terms with `d_k = 0` get coefficient `0` and are dropped by
`ofList`. -/
def pderiv (k : Fin nvars) (p : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofList (p.terms.map (fun t =>
    (t.1 - singleDegree k,
      t.2 * ((t.1.degrees[(k : ℕ)]'(by rw [t.1.correct]; exact k.2) : ℕ) : R))))

/-- **Correctness of the derivative.** `pderiv` agrees with Mathlib's `MvPolynomial.pderiv`. -/
theorem toPoly_pderiv (k : Fin nvars) (p : MvSparsePoly R nvars) :
    toPoly (pderiv k p) = MvPolynomial.pderiv k (toPoly p) := by
  have key : ∀ l : List (MvDegrees nvars × R),
      toPolyCore (l.map (fun t => (t.1 - singleDegree k,
        t.2 * ((t.1.degrees[(k : ℕ)]'(by rw [t.1.correct]; exact k.2) : ℕ) : R))))
        = MvPolynomial.pderiv k (toPolyCore l) := by
    intro l
    induction l with
    | nil => simp [toPolyCore]
    | cons hd tl ih =>
      obtain ⟨d, c⟩ := hd
      simp only [List.map_cons, toPolyCore, map_add, ih]
      congr 1
      rw [MvPolynomial.pderiv_monomial, toFinsupp_sub_singleDegree, toFinsupp_apply]
  unfold pderiv
  rw [toPoly_ofList]
  exact key p.terms

-- Derivative algebra laws, transferred from Mathlib's `pderiv` through `toPoly_injective`.

@[simp] lemma pderiv_add (k : Fin nvars) (p q : MvSparsePoly R nvars) :
    pderiv k (p + q) = pderiv k p + pderiv k q :=
  toPoly_injective (by simp only [toPoly_pderiv, toPoly_add, map_add])

@[simp] lemma pderiv_C (k : Fin nvars) (r : R) : pderiv k (C r) = 0 :=
  toPoly_injective (by simp only [toPoly_pderiv, toPoly_C, toPoly_zero, MvPolynomial.pderiv_C])

@[simp] lemma pderiv_X_self (k : Fin nvars) : pderiv k (X k : MvSparsePoly R nvars) = 1 :=
  toPoly_injective (by simp only [toPoly_pderiv, toPoly_X, toPoly_one, MvPolynomial.pderiv_X_self])

/-- The Leibniz rule for the computable derivative. -/
lemma pderiv_mul (k : Fin nvars) (p q : MvSparsePoly R nvars) :
    pderiv k (p * q) = pderiv k p * q + p * pderiv k q :=
  toPoly_injective (by simp only [toPoly_pderiv, toPoly_mul, toPoly_add, MvPolynomial.pderiv_mul])

end MvSparsePoly

/-! ### Worked examples (sanity-checked on every build via `#guard`)

These confirm the sparse arithmetic computes the mathematically correct polynomials, and that
the proved theorems (`multidegree_mul`, `leadCoeff_mul`, `IsExactDiv.mul_div_cancel`,
`divRem_spec`) hold on concrete inputs over `ℚ` in two variables `x = X 0`, `y = X 1`. -/
namespace MvSparsePoly.Examples
open MvSparsePoly

-- The arithmetic is well-founded recursion, which does not reduce in the kernel (`by decide`),
-- so the checks below use `#guard`, which evaluates with compiled code. Disable the Mathlib
-- linter that forbids `#`-commands for this examples block.
set_option linter.hashCommand false

/-- Display a polynomial as a list of `(exponent-vector, coefficient)` pairs. -/
private def disp (p : MvSparsePoly ℚ 2) : List (List ℕ × ℚ) :=
  p.terms.map (fun t => (t.1.degrees.toList, t.2))

private abbrev x : MvSparsePoly ℚ 2 := X 0
private abbrev y : MvSparsePoly ℚ 2 := X 1

-- Arithmetic: terms come out sorted in descending lex order with like-terms combined.
#guard disp (x + y)                 = [([1, 0], 1), ([0, 1], 1)]
#guard disp (x * y)                 = [([1, 1], 1)]
#guard disp ((x + y) * (x + y))     = [([2, 0], 1), ([1, 1], 2), ([0, 2], 1)]  -- x² + 2xy + y²
#guard disp ((x + C 1) * (x + C 1)) = [([2, 0], 1), ([1, 0], 2), ([0, 0], 1)]  -- x² + 2x + 1
#guard disp (x * x - y * y)         = [([2, 0], 1), ([0, 2], -1)]              -- x² − y²

-- `multidegree_mul` and `leadCoeff_mul` hold concretely.
#guard multidegree ((x + y) * (x * x + C 2))
        = multidegree (x + y) + multidegree (x * x + C 2)
#guard leadCoeff ((C 3 * x + y) * (C 5 * x + C 7))
        = leadCoeff (C 3 * x + y) * leadCoeff (C 5 * x + C 7)

-- Exact division `(a*b)/b = a` (`IsExactDiv.mul_div_cancel`, since `b ∣ a*b`).
#guard ((x + y) * (x + C 1)) / (x + C 1) = x + y
#guard (x * x - y * y) / (x - y) = x + y          -- (x²−y²)/(x−y) = x+y
#guard (x * x - y * y) / (x + y) = x - y          -- (x²−y²)/(x+y) = x−y

-- Division identity `b*q + r = a` (`divRem_spec`).
#guard (x + C 1) * (divRem (x * x * x + y) (x + C 1)).1 + (divRem (x * x * x + y) (x + C 1)).2
        = x * x * x + y
#guard (divRem ((x + y) * (x + C 1)) (x + C 1)).2 = 0          -- `b ∣ a` ⟹ remainder 0
#guard disp (divRem (x * x + C 1) (x + C 1)).2 = [([0, 0], 2)] -- x²+1 = (x+1)(x−1) + 2

-- Ring laws.
#guard (x + y) * (x - y) = x * x - y * y

-- Evaluation at a point `![v₀, v₁]` (computable; agrees with `MvPolynomial.eval`
-- by `eval_eq_eval_toPoly`).
#guard eval ![3, 5] (x * y + C 1) = 16           -- 3·5 + 1
#guard eval ![3, 5] ((x + y) * (x + y)) = 64      -- (3 + 5)²
#guard eval ![2, 7] (x * x * x - C 2 * y) = -6    -- 2³ − 2·7

-- Partial derivative (`pderiv`; agrees with `MvPolynomial.pderiv` by `toPoly_pderiv`).
#guard disp (pderiv 0 (x * x + y)) = [([1, 0], 2)]              -- ∂/∂x (x² + y) = 2x
#guard disp (pderiv 1 (x * x + y)) = [([0, 0], 1)]              -- ∂/∂y (x² + y) = 1
#guard disp (pderiv 0 (x * x * y + C 3 * x)) = [([1, 1], 2), ([0, 0], 3)]  -- ∂/∂x = 2xy + 3
#guard pderiv 1 (x * x + C 5) = 0                               -- ∂/∂y (x² + 5) = 0

-- The fast `mulFast` (used by `*` at runtime via `@[implemented_by]`) agrees with the reference
-- algorithm `mulRef` (the same body as `mulCore`, but with no `implemented_by`, so it actually
-- runs the generate-all-products-then-sort method). This cross-checks the two algorithms.
private def mulRef (a b : MvSparsePoly ℚ 2) : MvSparsePoly ℚ 2 :=
  ofList do
    let (i, c) ← a.terms
    let (j, d) ← b.terms
    return (i + j, c * d)

#guard ((x + y) * (x + C 1)) = mulRef (x + y) (x + C 1)
#guard ((x * x + C 2 * y + C 3) * (y * y - x + C 5)) =
  mulRef (x * x + C 2 * y + C 3) (y * y - x + C 5)
#guard ((x + y) * (x + y) * (x + y)) = mulRef (mulRef (x + y) (x + y)) (x + y)

-- Multi-divisor normal form (Buchberger's reduction step). `normalForm f G`
-- reduces `f` modulo the
-- divisor list `G`; `normalForm_span` proves `f − normalForm f G ∈ ⟨G⟩`.
-- `x² + 1` reduces by `[x]` to the constant remainder `1`
-- (x² cancels, `1` is irreducible by `x`).
#guard disp (normalForm (x * x + C 1) [x]) = [([0, 0], 1)]
-- `x·y` reduces by `[x]` to `0`  (x divides the leading term x·y).
#guard normalForm (x * y) [x] = 0
-- `x·y + y ∈ ⟨x, y⟩`: it reduces to `0`, certifying ideal membership
-- (`mem_idealOf_of_normalForm_eq_zero` then gives `toPoly (x·y + y) ∈ idealOf [x, y]`).
#guard normalForm (x * y + y) [x, y] = 0
-- Already in normal form w.r.t. `[y]`: no term is divisible by `y`'s leading monomial.
#guard normalForm (x * x + x + C 1) [y] = x * x + x + C 1

-- Buchberger's S-polynomial criterion (the computational verifier `isGroebnerBasis`).
-- `[x, y]` is a Gröbner basis: its only S-polynomial S(x, y) = y·x − x·y is `0`.
#guard sPoly x y = 0
#guard isGroebnerBasis [x, y] = true
-- `[x², x·y + 1]` is NOT a Gröbner basis: S(x², x·y+1) reduces to `−x`, which is irreducible
-- modulo the set (remainder ≠ 0), so the criterion returns `false`.
#guard disp (sPoly (x * x) (x * y + C 1)) = [([1, 0], -1)]              -- S-poly is −x
#guard normalForm (sPoly (x * x) (x * y + C 1)) [x * x, x * y + C 1] ≠ 0
#guard isGroebnerBasis [x * x, x * y + C 1] = false
-- A single generator is vacuously a Gröbner basis (there are no pairs to check).
#guard isGroebnerBasis [x * x + y] = true

-- Buchberger's First (gcd) Criterion: `x` and `y` have coprime
-- leading monomials (no shared
-- variable), so their pair is pruned from the check above; `x²`
-- and `x·y+1` share `x`, so it isn't.
#guard coprimeLead x y = true
#guard coprimeLead (x * x) (x * y + C 1) = false

end MvSparsePoly.Examples
