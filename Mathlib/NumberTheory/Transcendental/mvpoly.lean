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
    terms.Pairwise (fun p1 p2 => p2.1 ≤ p1.1) → (dedupList terms).Pairwise (fun p1 p2 => p2.1 < p1.1)
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



theorem dedupList_sorted (terms : List (MvDegrees nvars × R))
  (sorted : terms.Pairwise (·.1 ≥ ·.1)) :
  (dedupList terms).Pairwise (·.1 > ·.1) := dedupList_sorted_aux terms sorted


def ofList (terms : List (MvDegrees nvars × R)) : MvSparsePoly R nvars :=
  -- 1. Use `decide` to turn the abstract `≤` math into the `Bool` that mergeSort needs
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
lemma list_set_one_zero_foldl : ∀ (n : ℕ) (i : ℕ) (h : i < n),
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

instance : Mul (MvSparsePoly R nvars) where
  mul x y :=
    ofList do
      let (i, a) ← x.terms
      let (j, b) ← y.terms
      return (i + j, a * b)

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

-- 3. Bridge: The `ofSortedList` constructor does not change an already valid polynomial.
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
  change (addCore p.terms q.terms).filter (·.2 ≠ 0) = (addCore q.terms p.terms).filter (·.2 ≠ 0)
  rw [addCore_comm]

-- 6. The final Polynomial theorem now natively proves `-p + p = 0`
lemma poly_add_left_neg (p : MvSparsePoly R nvars) : -p + p = 0 := by
  apply MvSparsePoly.ext

  -- Expose the addition definition
  change (addCore ((negCore p.terms).filter (·.2 ≠ 0)) p.terms).filter (·.2 ≠ 0) = []

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
  have h_bind : p.terms.flatMap (fun _ => ([] : List (MvDegrees nvars × R))) = [] := by
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

    -- 3. With both data fields proven equal, unpack the structures and close the goal!
    cases i
    cases j
    simp_all

  · intro h
    rw [h]

lemma toFinsupp_add (i j : MvDegrees nvars) :
    MvDegrees.toFinsupp (i + j) = MvDegrees.toFinsupp i + MvDegrees.toFinsupp j := by
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
  have h_zero_def : (0 : MvDegrees nvars).degrees = (List.replicate nvars 0).toArray := by
    -- Point this exactly at your Zero definition for MvDegrees
    --unfold Zero.zero
    rfl
  simp only [h_zero_def]
  grind


-- Helper 1: toPoly of a constant SparsePoly is the constant MvPolynomial
theorem toPoly_C (r : R) : toPoly (C r : MvSparsePoly R nvars) = MvPolynomial.C r := by
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
    change MvPolynomial.monomial (MvDegrees.toFinsupp 0) r + toPolyCore [] = MvPolynomial.C r
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

theorem coeff_toPolyCore_of_degLt {n : MvDegrees nvars} (xs : List (MvDegrees nvars × R)) (h : degLt n xs) :
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

-- Helper 3: The coefficient of the head of the list at its own exponent `i` is exactly `a`.
theorem coeff_toPolyCore_head {i : MvDegrees nvars} {a : R} (xs : List (MvDegrees nvars × R)) (h : degLt i xs) :
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
lemma degLt_of_sorted_cons {i : MvDegrees nvars} {a : R} {xs : List (MvDegrees nvars × R)}
    (h : ((i, a) :: xs).Pairwise (·.1 > ·.1)) : degLt i xs :=
  fun x hx => (List.pairwise_cons.1 h).1 x hx

-- The Main Boss Fight (Exactly mirroring your univariate logic)
theorem toPolyCore_injective_of_sorted : ∀ (l1 l2 : List (MvDegrees nvars × R)),
    l1.Pairwise (·.1 > ·.1) → l2.Pairwise (·.1 > ·.1) →
    (∀ x ∈ l1, x.2 ≠ 0) → (∀ x ∈ l2, x.2 ≠ 0) →
    toPolyCore l1 = toPolyCore l2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: ys, _, s2, _, nz2, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore []) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((j, b) :: ys)) := by rw [heq]
    change 0 = _ at h_coeff
    rw [coeff_toPolyCore_head ys (degLt_of_sorted_cons s2)] at h_coeff
    have hb_nz := nz2 (j, b) List.mem_cons_self
    exact False.elim (hb_nz h_coeff.symm)
  | (i, a) :: xs, [], s1, _, nz1, _, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore []) := by rw [heq]
    change _ = 0 at h_coeff
    rw [coeff_toPolyCore_head xs (degLt_of_sorted_cons s1)] at h_coeff
    have ha_nz := nz1 (i, a) List.mem_cons_self
    exact False.elim (ha_nz h_coeff)
  | (i, a) :: xs, (j, b) :: ys, s1, s2, nz1, nz2, heq => by
    have h_deg_x : degLt i xs := degLt_of_sorted_cons s1
    have h_deg_y : degLt j ys := degLt_of_sorted_cons s2
    obtain hij | rfl | hji := lt_trichotomy i j
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((j, b) :: ys)) := by rw [heq]
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
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, b) :: ys)) := by rw [heq]
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
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) := by rw [heq]
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
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) a + MvPolynomial.monomial (MvDegrees.toFinsupp i) b) +
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
theorem toPolyCore_perm {l1 l2 : List (MvDegrees nvars × R)} (h : l1.Perm l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => dsimp [toPolyCore]; rw [ih]
  | swap x y l => dsimp [toPolyCore]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- 2. mergeSort is just a permutation
theorem toPolyCore_mergeSort (l : List (MvDegrees nvars × R)) (r : (MvDegrees nvars × R) → (MvDegrees nvars × R) → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l :=
  toPolyCore_perm (l.mergeSort_perm r)

-- 3. Combining like-terms (dedupList) preserves the polynomial via the distributive law
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
theorem toPolyCore_append (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    dsimp [toPolyCore]
    rw [ih, add_assoc]

-- 2. New FlatMap Monomial Helper (Using `change` to outsmart the elaborator)
theorem toPolyCore_monomial_mul_flatMap (l : List (MvDegrees nvars × R)) (i : MvDegrees nvars) (a : R) :
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
  dsimp [HMul.hMul, Mul.mul]
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



#print AddMonoidWithOne

-- instance : Algebra R (MvSparsePoly R nvars) := by
--   refine' { toFun := C, smul := fun a r => C a * r, ..} <;> sorry
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

-- -- 1. Define the custom typeclass mentioned in the paper
-- class Wordering (nvars : ℕ) where
--   lt : MvDegrees nvars → MvDegrees nvars → Prop
--   wf : WellFounded lt


@[ext] class WOrdering (nvars : ℕ) extends LinearOrder (MvDegrees nvars) where
  zero_le {x : MvDegrees nvars} : 0 ≤ x
  add_le_add {x y z : MvDegrees nvars} : x ≤ y → x + z ≤ y + z
  -- FIX: Explicitly state the types so Lean can find the `<` operator!
  wf : WellFounded (fun (a b : MvDegrees nvars) => a < b)

-- The True High-Priority Relation
instance (priority := high) {nvars : ℕ} [w : WOrdering nvars] : WellFoundedRelation (MvDegrees nvars) where
  -- Lean can infer the types here because `rel` expects `MvDegrees nvars → MvDegrees nvars → Prop`
  rel := fun a b => a < b
  wf := w.wf

-- -- 2. Teach Lean that 'Wordering' provides the standard '<' operator
-- instance [w : Wordering nvars] : LT (MvDegrees nvars) where
--   lt := w.lt

-- -- 3. The high-priority WellFoundedRelation that fixes your decreasing_by block
-- instance (priority := high) [w : Wordering nvars] : WellFoundedRelation (MvDegrees nvars) where
--   rel := (· < ·)
--   wf := w.wf


-- -- We use `local instance` and a massive priority to completely overwrite Lean's defaults for this file
-- local instance (priority := high) customPolyWF [w : Wordering nvars] [CommRing R] :
--     WellFoundedRelation (MvSparsePoly R nvars) where
--   rel a b := a.multidegree < b.multidegree
--   wf := InvImage.wf multidegree w.wf

-- 1. The ONLY Custom Relation we need for the Polynomial.
-- FIX: We explicitly add [WOrdering nvars] here so Lean knows to use your '<' operator!
local instance (priority := high) customPolyWF [WOrdering nvars] : WellFoundedRelation (MvSparsePoly R nvars) where

  -- We tie the relation exactly to Lean's built-in Tuple relation so they can never mismatch
  rel := InvImage
           (inferInstance : WellFoundedRelation (MvDegrees nvars × ℕ)).rel
           (fun p => (p.multidegree, p.terms.length))

  -- The proof is now a mathematically perfect match for the relation
  wf := InvImage.wf
          (fun (p : MvSparsePoly R nvars) => (p.multidegree, p.terms.length))
          (inferInstance : WellFoundedRelation (MvDegrees nvars × ℕ)).wf

-- 1. Make absolutely sure Lean has the WellFoundedRelation for MvDegrees.
-- (This prevents Lean from wrapping the tuple components in sizeOf!)
instance (priority := high) mvDegreesWF {nvars : ℕ} [w : WOrdering nvars] : WellFoundedRelation (MvDegrees nvars) where
  rel := (· < ·)
  wf := w.wf

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
lemma lex_drop_of_degLt_with_hA [CommRing R]
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
    · -- FIX: We explicitly pass nvars to the global template so Lean doesn't guess!
      have h_zero_le : (0 : MvDegrees nvars) ≤ i := @WOrdering.zero_le nvars (@instWOrdering nvars) i
      exact False.elim (lt_irrefl _ (lt_of_le_of_lt h_zero_le hgt))
  | cons hd tl =>
    -- Case 2: The remainder list is NOT empty.
    have h_hd_lt : hd.1 < i := h_deg hd List.mem_cons_self
    exact Prod.Lex.left _ _ h_hd_lt

-- The Cancel Lemma
lemma multidegree_sub_cancel [Field R]
  {a b : MvSparsePoly R nvars} {i j : MvDegrees nvars} {x y : R} {as bs}
  (hA : a.terms = (i, x) :: as)
  (hB : b.terms = (j, y) :: bs)
  (hDiv : MvDegrees.divides j i = true) :
  Prod.Lex (fun (u v : MvDegrees nvars) => u < v) (fun (u v : ℕ) => u < v)
    ((a - sparseMonomial (i - j) (x / y) * b).multidegree, (a - sparseMonomial (i - j) (x / y) * b).terms.length)
    (a.multidegree, a.terms.length) := by

  -- 1. Evaluate a.multidegree to i
  have ha_deg : a.multidegree = i := by
    unfold multidegree
    rw [hA]
    rfl
  rw [ha_deg]

  -- 2. Unfold multidegree on the left side to expose the raw List
  unfold multidegree

  -- 3. Apply the Master Bridge Lemma!
  apply lex_drop_of_degLt_with_hA hA

  -- 4. PURE ALGEBRA GOAL REMAINS
  -- Goal: Prove that (a - c*b).terms contains no degrees >= i.
  -- You will prove this later using the 'addCore_cancel_head' lemma we just built!
  sorry

lemma tail_terminates
  {a : MvSparsePoly R nvars} {i : MvDegrees nvars} {x : R} {as}
  (hA : a.terms = (i, x) :: as) :
  Prod.Lex (fun (u v : MvDegrees nvars) => u < v) (fun (u v : ℕ) => u < v)
    ((ofSortedList as sorry).multidegree, (ofSortedList as sorry).terms.length)
    (a.multidegree, a.terms.length) := by

  -- Step 1: Formally prove that the length strictly drops
  have h_len : (ofSortedList as sorry).terms.length < a.terms.length := by
    rw [hA]
    simp only [List.length_cons]
    have h_bound := ofSortedList_length_le as sorry
    grind

  -- Step 2: Split the multidegree comparison into 3 mathematical realities
  rcases lt_trichotomy ((ofSortedList as sorry).multidegree) a.multidegree with h_lt | h_eq | h_gt

  · -- Case 1: The multidegree strictly dropped.
    -- Prod.Lex.left satisfies the goal purely on the first tuple element.
    apply Prod.Lex.left
    exact h_lt

  · -- Case 2: The multidegree stayed exactly the same.
    -- We substitute the equality, and Prod.Lex.right satisfies the goal using the length drop!
    sorry

  · -- Case 3: The multidegree somehow increased.
    -- Mathematically, because the list is sorted, the tail CANNOT have a higher degree.
    -- You will use your `degLt` theorems here to prove this contradicts `hA` and close the branch.
    sorry

-- 4. The Clean Function
-- FIX: Explicitly add [WOrdering nvars] here so Lean doesn't throw it away!
def mvDivRem [Field R] [WOrdering nvars] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars × MvSparsePoly R nvars :=
  match hA : a.terms with
  | [] => (0, 0)
  | (i, x) :: as =>
    match hB : b.terms with
    | [] => (0, a)
    | (j, y) :: bs =>
      if hDiv : MvDegrees.divides j i then
        let c := sparseMonomial (i - j) (x / y)
        if y * (x / y) = x then
          let (q', r') := mvDivRem (a - c * b) b
          (q' + c, r')
        else
          (0, a)
      else
        let (q', r') := mvDivRem (ofSortedList as sorry) b
        (q', sparseMonomial i x + r')
termination_by a
decreasing_by
  · exact multidegree_sub_cancel (a := a) (b := b) (x := x) (y := y) hA hB hDiv
  · exact tail_terminates (a := a) hA

def gcdPrim (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  match a.terms with
  | [] => b
  | (i, x) :: as =>
    match b.terms with
    | [] => a
    | (j, y) :: bs =>
      if i > j then
        -- Cancel the head of 'a' using 'b'
        gcdPrim (y • a - sparseMonomial (i - j) x * b) b
      else
        -- Cancel the head of 'b' using 'a'
        gcdPrim a (x • b - sparseMonomial (j - i) y * a)
termination_by a.degree + b.degree
decreasing_by all_goals sorry


def content [CommMonoidWithZero R] [IsCancelMulZero R] [GCDMonoid R] (a : MvSparsePoly R nvars) : R :=
  a.terms.foldl (init := 0) (gcd · ·.2)

def primitivePart [CommMonoidWithZero R] [IsCancelMulZero R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : MvSparsePoly R nvars) : MvSparsePoly R nvars where
  terms :=
    let b := a.content
    a.terms.map fun (i, a) => (i, a / b)
  sorted := sorry
  nonzero := sorry

nonrec def gcd [CommMonoidWithZero R] [IsCancelMulZero R] [GCDMonoid R]
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
