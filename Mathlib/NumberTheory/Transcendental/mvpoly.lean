-- A computational representation of Polynomials in several (anonymous) variables
-- over a commutative ring R
-- Representation is distributed and sparse, number of variables if fixed as nvars
-- Computational implies that need DecidableEq for R
-- Based on univariates by Mario Carniero at Hausdorff Institute June 2024
-- Representation is as a list of pairs (exponent, coefficient) in ℕ × R
-- Exponents in decreasing order, coefficients non-zero (so zero polynomial is empty list)
-- Note that Lean allows the ring with just 0 (so 1=0)
-- JHD: we may wish to rethink allowing this, as it causes extra checks

import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic
import Mathlib.Deprecated.Sort
--import Mathlib

set_option linter.style.emptyLine false
set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

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
def lex_step (p : ℕ × ℕ) (acc : Bool) : ForInStep Bool :=
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

instance : LE (MvDegrees nvars) where le a b := lexorder_impl a b

-- 3. THE LEAN 4 MAGIC TRICK
-- This tells Lean: "When evaluating math, use `list_lex`.
-- But when actually running the code, run your exact `lexorder_impl` loop!"
@[implemented_by lexorder_impl]
def lexorder (a b : MvDegrees nvars) : Bool :=
  list_lex a.degrees.toList b.degrees.toList




instance : LE (MvDegrees nvars) where le a b := lexorder a b = true

theorem lexorder_total (a b : MvDegrees nvars) : a ≤ b ∨ b ≤ a := by
  change list_lex a.degrees.toList b.degrees.toList = true ∨
         list_lex b.degrees.toList a.degrees.toList = true
  exact list_lex_total a.degrees.toList b.degrees.toList

-- 3. The Equivalence Bridge
lemma lexorder_eq_list_lex (a b : MvDegrees nvars) :
    lexorder a b = list_lex a.degrees.toList b.degrees.toList := by
  unfold lexorder
  have h_len : a.degrees.toList.length = b.degrees.toList.length := by
    aesop
  have ha_arr : a.degrees = a.degrees.toList.toArray := by apply array_eq_of_toList_eq; simp
  have hb_arr : b.degrees = b.degrees.toList.toArray := by apply array_eq_of_toList_eq; simp
  rw [ha_arr, hb_arr]

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


-- Intermediate Lemma: Anti-symmetry for MvDegrees
lemma lexorder_antisymm (a b : MvDegrees nvars) (hab : lexorder a b = true) (hba : lexorder b a = true) : a = b := by
  have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop --[← a.correct, ← b.correct]
  have hlist := list_lex_antisymm h1 hab hba
  apply MvDegrees.ext
  · exact array_eq_of_toList_eq hlist
  · rw [a.totalDegree_eq, b.totalDegree_eq, array_eq_of_toList_eq hlist]

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

@[ext] structure MvSparsePoly (R : Type) [CommRing R] (nvars : ℕ) [WOrdering nvars] : Type where
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

variable {R : Type} [CommRing R] [DecidableEq R] [WOrdering nvars]

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
lemma dedupList_sorted_aux : ∀ (terms : List (MvDegrees nvars × R)),
    terms.Pairwise (·.1 ≥ ·.1) → (dedupList terms).Pairwise (·.1 > ·.1)
  | [] => fun _ => by unfold dedupList; grind
  | [(i, a)] => fun _ => by
    have : dedupList [(i, a)] = [(i, a)] := by unfold dedupList; rfl
    rw [this]
    aesop
  | (i, a) :: (j, b) :: x => fun h => by
    unfold dedupList
    split
    · next heq =>
      have h_next : ((i, a + b) :: x).Pairwise (·.1 ≥ ·.1) := by
        simp only [List.pairwise_cons] at h ⊢
        rcases h with ⟨hi, hj_x⟩
        constructor
        · intro p hp; exact hi p (List.mem_cons_of_mem _ hp)
        · grind
      exact dedupList_sorted_aux ((i, a + b) :: x) h_next

    · next hneq =>
      have h_next : ((j, b) :: x).Pairwise (·.1 ≥ ·.1) := h.of_cons
      let ih := dedupList_sorted_aux ((j, b) :: x) h_next
      simp only [List.pairwise_cons] at h ⊢
      rcases h with ⟨hi_all, hj_x⟩

      -- Extract hi_ge_j: (j, b) is the head of the tail, so i ≥ j
      have hi_ge_j : j ≤ i := hi_all (j, b) (List.mem_cons_self _ _)

      constructor
      · intro p hp
        have hj_bound : ∀ p' ∈ ((j, b) :: x), p'.1 ≤ j := by
          intro p' hp'
          simp only [List.mem_cons] at hp'
          rcases hp' with rfl | hp_x
          · exact le_rfl
          · exact hj_x.1 p' hp_x

        -- Use the bound lemma to get p.1 ≤ j
        let hp_le_j : p.1 ≤ j := dedupList_bound ((j, b) :: x) j hj_bound p hp

        -- We have: p.1 ≤ j, j ≤ i, and i ≠ j
        -- Therefore p.1 < i, which is i > p.1
        have j_lt_i : j < i := lt_of_le_of_ne hi_ge_j (Ne.symm hneq)
        exact lt_of_le_of_lt hp_le_j j_lt_i
      · exact ih
termination_by terms => terms.length

#exit

theorem dedupList_sorted (terms : List (MvDegrees nvars × R))
  (sorted : terms.Pairwise (·.1 ≥ ·.1)) :
  (dedupList terms).Pairwise (·.1 > ·.1) := dedupList_sorted_aux terms sorted


def ofList (terms : List (MvDegrees nvars × R)) : MvSparsePoly R nvars :=
  let terms' := terms.mergeSort (fun a b => lexorder b.1 a.1)

  -- Force Lean to unfold the `≥` into `≤` so it syntactically matches `le_total`
  have hTotal : IsTotal (MvDegrees nvars × R) (·.1 ≥ ·.1) := ⟨fun a b => by
    change b.1 ≤ a.1 ∨ a.1 ≤ b.1
    sorry
  ⟩

  -- Do the same for transitivity to be safe
  have hTrans : IsTrans (MvDegrees nvars × R) (·.1 ≥ ·.1) := ⟨fun a b c hab hbc => by
    change c.1 ≤ a.1
    change b.1 ≤ a.1 at hab
    change c.1 ≤ b.1 at hbc
    sorry
  ⟩

  have hSorted : terms'.Pairwise (·.1 ≥ ·.1) := terms.sorted_mergeSort _ _

  ofSortedList (dedupList terms')
    (dedupList_sorted terms' hSorted)








def X : MvSparsePoly R nvars := ofSortedList [(1, 1)] (List.sorted_singleton _)

instance : Mul (MvSparsePoly R nvars) where
  mul x y :=
    ofList do
      let (i, a) ← x.terms
      let (j, b) ← y.terms
      return (i + j, a * b)

instance : Neg (MvSparsePoly R nvars) where
  neg x := C (-1) * x


instance : CommRing (MvSparsePoly R nvars) where
  add := (·+·)
  add_assoc := sorry
  zero := 0
  zero_add := sorry
  add_zero := sorry
  nsmul := (C (R := R) · * ·)
  add_comm := sorry
  mul := (·*·)
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := 1
  one_mul := sorry
  mul_one := sorry
  neg := (-·)
  zsmul := zsmulRec (C (R := R) · * ·)
  add_left_neg := sorry
  mul_comm := sorry
  natCast n := C n
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  -- refine' {
  --   zero := 0, one := 1, add := (·+·), mul := (·*·)
  --   sub := (·+-·), neg := (-·)
  --   npow := npowRec
  --   nsmul := nsmulRec
  --   zsmul := zsmulRec
  --   .. } <;> sorry
#print AddMonoidWithOne
instance : Algebra R (MvSparsePoly R nvars) := by
  refine' { toFun := C, smul := fun a r => C a * r, ..} <;> sorry

class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

def degree (a : MvSparsePoly R nvars) : ℕ := (a.terms.headD (0, 0)).1

def gcdPrim (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  match a.terms with
  | [] => b
  | (i, x) :: as =>
    match b.terms with
    | [] => a
    | (j, y) :: bs =>
      if i > j then
        gcdPrim (y • a - x • X^(i-j) * b) b
      else
        gcdPrim a (x • b - y • X^(j-i) * a)
termination_by a.degree + b.degree
decreasing_by all_goals sorry

def content [CancelCommMonoidWithZero R] [GCDMonoid R] (a : MvSparsePoly R nvars) : R :=
  a.terms.foldl (init := 0) (gcd · ·.2)

def primitivePart [CancelCommMonoidWithZero R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : MvSparsePoly R nvars) : MvSparsePoly R nvars where
  terms :=
    let b := a.content
    a.terms.map fun (i, a) => (i, a / b)
  sorted := sorry
  nonzero := sorry

nonrec def gcd [CancelCommMonoidWithZero R] [GCDMonoid R]
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
  match a.terms, b.terms with
  | (i, x) :: _, (j, y) :: _ =>
    if i < j then
      (0, a)
    else
      let c := (x / y) • X^(i-j)
      if y * (x / y) = x then
        let (q', r') := divRem (a - c * b) b
        (q' + c, r')
      else
        (0, a)
  | _, _ => (0, a)
termination_by a.degree
decreasing_by all_goals sorry

instance [Div R] : Div (MvSparsePoly R nvars) where
  div a b := (divRem a b).1

instance [Div R] [IsExactDiv R] : IsExactDiv (MvSparsePoly R nvars) where
  mul_div_cancel h := sorry

instance : DecidableEq (MvSparsePoly R nvars) := fun a b =>
  decidable_of_iff' (a.terms = b.terms) (SparsePoly.ext_iff ..)

#eval (X * (C X * X + C (X + 2) : SparsePoly (SparsePoly ℤ))) / X

noncomputable def toPolyEquiv : MvSparsePoly R nvars ≃ₐ[R] Polynomial R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap ..) X
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_mul' := sorry
  commutes' := sorry

@[simp]
theorem ofPoly_X : toPolyEquiv.symm Polynomial.X = (X : MvSparsePoly R nvars) := by
  simp [toPolyEquiv]

@[simp]
theorem toPoly_X : (X : MvSparsePoly R nvars).toPoly = Polynomial.X := by
  rw [← toPolyEquiv.apply_symm_apply Polynomial.X, ofPoly_X]; rfl
