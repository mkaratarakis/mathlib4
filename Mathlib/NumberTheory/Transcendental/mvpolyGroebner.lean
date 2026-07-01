/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.mvpoly
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Computable multivariate polynomial algebra: division, normal forms, Groebner bases

This file extends `MvSparsePoly` (from `Mathlib.NumberTheory.Transcendental.mvpoly`) with the
commutative-algebra layer that the reflection tactic `mv_decide` does not use: the
multidegree / leading-term API, multivariate division and gcd, multi-divisor normal forms (the
reduction step of Buchberger's algorithm) with a geobucket fast path, the bridge to Mathlib's
`MonomialOrder`, Buchberger's S-polynomial and gcd criteria, and the formal partial derivative.
-/

set_option linter.style.longFile 2100

namespace MvSparsePoly

open MvPolynomial

variable {nvars : ℕ} {R : Type} [CommRing R] [DecidableEq R]

/-- A ring with exact division by divisors. -/
class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

/-- The multidegree (leading exponent vector), used for the algebra. -/
def multidegree (a : MvSparsePoly R nvars) : MvDegrees nvars :=
  (a.terms.headD (0, 0)).1

/-- The total degree of the leading term, used for proofs. -/
def totalDegree (a : MvSparsePoly R nvars) : ℕ :=
  (a.terms.headD (0, 0)).1.totalDegree

/-- The total degree of the leading term. -/
def degree (a : MvSparsePoly R nvars) : ℕ := (a.terms.headD (0, 0)).1.totalDegree

instance : Sub (MvDegrees nvars) where
  sub a b := {
    degrees := Array.zipWith (· - ·) a.degrees b.degrees
    correct := by simp [a.correct, b.correct]
    totalDegree := (Array.zipWith (· - ·) a.degrees b.degrees).foldl (· + ·) 0
    totalDegree_eq := rfl
  }

/-- The single-term polynomial `r · X^d`. -/
def sparseMonomial (d : MvDegrees nvars) (r : R) : MvSparsePoly R nvars :=
  ofSortedList [(d, r)] (by simp)

/-- Whether `a` divides `b` as monomials (component-wise `≤` on exponents). -/
def MvDegrees.divides (a b : MvDegrees nvars) : Bool :=
  Array.zipWith (fun x y => decide (x ≤ y)) a.degrees b.degrees |>.all id

lemma mvDegrees_zero_le (i : MvDegrees nvars) : (0 : MvDegrees nvars) ≤ i := WOrdering.zero_le

lemma mvDegrees_add_le_add {x y z : MvDegrees nvars} (h : x ≤ y) : x + z ≤ y + z :=
  WOrdering.add_le_add h

/-- The well-founded relation on `MvDegrees` used for termination (`a < b` in the monomial
order). High priority so Lean does not fall back to `sizeOf`. -/
instance (priority := high) mvDegreesWF {nvars : ℕ} :
    WellFoundedRelation (MvDegrees nvars) where
  rel := (· < ·)
  wf := WOrdering.wf

/-- The termination relation for `MvSparsePoly`: compare by `(multidegree, #terms)` lexically. -/
local instance (priority := high) customPolyWF :
    WellFoundedRelation (MvSparsePoly R nvars) :=
  invImage (fun (p : MvSparsePoly R nvars) => (p.multidegree, p.terms.length)) inferInstance

/-- Filtering never increases the length of a list. -/
lemma length_filter_le {α} (p : α → Bool) (l : List α) : (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons]
    split
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

/-- The length of `ofSortedList` is at most the length of the raw list. -/
lemma ofSortedList_length_le (l : List (MvDegrees nvars × R)) (h) :
  (ofSortedList l h).terms.length ≤ l.length := by
  exact length_filter_le (fun p => decide (p.2 ≠ 0)) l

/-- Adding a term to its negation cancels both heads. -/
lemma addCore_cancel_head (i : MvDegrees nvars) (x : R) (as bs : List (MvDegrees nvars × R)) :
  addCore ((i, x) :: as) ((i, -x) :: bs) = addCore as bs := by
  conv => lhs; unfold addCore
  have h_not_lt : ¬(i < i) := lt_irrefl i
  have h_zero : x + -x = 0 := add_neg_cancel x
  simp only [h_not_lt, h_zero, ite_false, ite_true]

omit [DecidableEq R] in
/-- Termination bridge: dropping a leading term strictly decreases the `(multidegree, length)`
order. -/
lemma lex_drop_of_degLt_with_hA
  {a : MvSparsePoly R nvars} {i : MvDegrees nvars} {x : R} {as}
  (hA : a.terms = (i, x) :: as)
  {l : List (MvDegrees nvars × R)}
  (h_deg : degLt i l) :
  Prod.Lex (fun (u v : MvDegrees nvars) => u < v) (fun (u v : ℕ) => u < v)
    ((l.headD (0, 0)).1, l.length) (i, a.terms.length) := by
  cases l with
  | nil =>
    rcases lt_trichotomy (0 : MvDegrees nvars) i with hlt | heq | hgt
    · exact Prod.Lex.left _ _ hlt
    · subst heq
      apply Prod.Lex.right
      rw [hA]
      simp only [List.length_cons]
      aesop
    · exact absurd hgt (not_lt.mpr (mvDegrees_zero_le i))
  | cons hd tl =>
    have h_hd_lt : hd.1 < i := h_deg hd List.mem_cons_self
    exact Prod.Lex.left _ _ h_hd_lt

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

lemma toPoly_sparseMonomial (d : MvDegrees nvars) (r : R) :
    toPoly (sparseMonomial d r) = MvPolynomial.monomial (MvDegrees.toFinsupp d) r := by
  change toPolyCore (([(d, r)]).filter (·.2 ≠ 0)) = MvPolynomial.monomial (MvDegrees.toFinsupp d) r
  rw [toPolyCore_filter_nonzero]
  simp only [toPolyCore, add_zero]

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

lemma ofList_degLe {n : MvDegrees nvars} (l : List (MvDegrees nvars × R))
    (h : ∀ p ∈ l, p.1 ≤ n) : ∀ p ∈ (ofList l).terms, p.1 ≤ n := by
  intro p hp
  have hp' : p ∈ dedupList (l.mergeSort (fun a b => decide (b.1 ≤ a.1))) :=
    List.mem_of_mem_filter hp
  refine dedupList_bound (l.mergeSort (fun a b => decide (b.1 ≤ a.1))) n ?_ p hp'
  intro q hq
  exact h q ((l.mergeSort_perm _).mem_iff.mp hq)

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
  intro p hp
  obtain ⟨d, v⟩ := p
  have hv : v ≠ 0 := (a - sparseMonomial (i - j) cf * b).nonzero (d, v) hp
  have hcoeff_v : MvPolynomial.coeff (MvDegrees.toFinsupp d)
      (toPoly (a - sparseMonomial (i - j) cf * b)) = v :=
    coeff_toPolyCore_mem (a - sparseMonomial (i - j) cf * b).sorted hp
  by_contra hge
  push Not at hge
  have hcoeff_0 : MvPolynomial.coeff (MvDegrees.toFinsupp d)
      (toPoly (a - sparseMonomial (i - j) cf * b)) = 0 := by
    rw [toPoly_sub, MvPolynomial.coeff_sub]
    rcases eq_or_lt_of_le hge with rfl | hlt
    · have h1 : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPoly a) = x := by
        change MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore a.terms) = x
        rw [hA]; exact coeff_toPolyCore_head as (degLt_of_sorted_cons (hA ▸ a.sorted))
      have h2 : MvPolynomial.coeff (MvDegrees.toFinsupp i)
          (toPoly (sparseMonomial (i - j) cf * b)) = x :=
        coeff_mul_sparseMonomial_leading hB hDiv h_div
      rw [h1, h2, sub_self]
    · have h1 : MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly a) = 0 := by
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
  have h_len : (ofSortedList as (sorted_tail hA)).terms.length < a.terms.length := by
    rw [hA]
    simp only [List.length_cons]
    have h_bound := ofSortedList_length_le as (sorted_tail hA)
    grind
  have ha_deg : a.multidegree = i := by unfold multidegree; rw [hA]; rfl
  have hlt_as : ∀ p ∈ as, p.1 < i := (List.pairwise_cons.mp (hA ▸ a.sorted)).1
  rcases lt_trichotomy ((ofSortedList as (sorted_tail hA)).multidegree) a.multidegree
    with h_lt | h_eq | h_gt
  · exact Prod.Lex.left _ _ h_lt
  · rw [h_eq]
    exact Prod.Lex.right _ h_len
  · exfalso
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

def mvDivRem [Div R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars × MvSparsePoly R nvars :=
  match hA : a.terms with
  | [] => (0, 0)
  | (i, x) :: as =>
    match _hB : b.terms with
    | [] => (0, a)
    | (j, y) :: _bs =>
      if _hDiv : MvDegrees.divides j i then
        let c := sparseMonomial (i - j) (x / y)
        if _h_div : y * (x / y) = x then
          let (q', r') := mvDivRem (a - c * b) b
          (q' + c, r')
        else
          (0, a)
      else
        let (q', r') := mvDivRem (ofSortedList as (sorted_tail hA)) b
        (q', sparseMonomial i x + r')
termination_by a
decreasing_by
  · exact multidegree_sub_cancel hA _hB _hDiv _h_div
  · exact tail_terminates hA

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

omit [DecidableEq R] in
lemma mv_foldl_gcd_dvd_acc [IsDomain R] [GCDMonoid R]
    (l : List (MvDegrees nvars × R)) (acc : R) :
    l.foldl (fun a x => gcd a x.2) acc ∣ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact (ih (gcd acc hd.2)).trans (gcd_dvd_left _ _)

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

def divRem [Div R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars × MvSparsePoly R nvars :=
  match _hA : a.terms, _hB : b.terms with
  | (i, x) :: _as, (j, y) :: _bs =>
    if _hDiv : MvDegrees.divides j i then
      let c := sparseMonomial (i - j) (x / y)
      if _h_div : y * (x / y) = x then
        let (q', r') := divRem (a - c * b) b
        (q' + c, r')
      else
        (0, a)
    else
      (0, a)
  | _, _ => (0, a)
termination_by a
decreasing_by exact multidegree_sub_cancel _hA _hB _hDiv _h_div

theorem divRem_spec [Div R] (a b : MvSparsePoly R nvars) :
    b * (divRem a b).1 + (divRem a b).2 = a := by
  fun_induction divRem a b with
  | case1 a i x as j y bs ha hb hDiv c h_exact q' r' hqr ih =>
    rw [hqr] at ih
    linear_combination ih
  | _ => simp

/-! ### Multi-divisor normal form (the reduction step of Buchberger's algorithm)

Given a polynomial `f` and a list of divisors `G = [g₁,…,gₖ]`, repeatedly cancel the leading
term of `f` using whichever `gᵢ` has a leading term dividing it; terms that cannot be reduced
are moved to the remainder. The result `normalForm f G` is `f` reduced modulo the ideal `⟨G⟩`.
The key verified fact (`normalForm_span`) is `toPoly f - toPoly (normalForm f G) ∈ ⟨G⟩`, hence
`normalForm f G = 0 → toPoly f ∈ ⟨G⟩` — a computable, *proof-producing* ideal-membership test. -/

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

/-! ### Geobucket reduction (verified-total fast path for `normalForm`)

A geobucket is a list of polynomial "buckets" whose sum is the represented polynomial. Inserting
a small polynomial only touches one bucket (cheap), so the reduction loop avoids re-merging the
whole dividend each step. We prove enough about it to discharge termination of `normalFormFast`,
which then serves as the `@[implemented_by]` runtime for `normalForm`. -/

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
      | cons c cs ihs =>
        simp only [cleanTop, List.map_cons, List.sum_cons]; exact add_le_add (hle c) ihs
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
  have hcoeff_v : MvPolynomial.coeff (MvDegrees.toFinsupp e)
      (toPoly (P - sparseMonomial d cf)) = v :=
    coeff_toPolyCore_mem (P - sparseMonomial d cf).sorted hp
  by_contra hge
  rw [not_lt] at hge
  have hcoeff_0 : MvPolynomial.coeff (MvDegrees.toFinsupp e)
      (toPoly (P - sparseMonomial d cf)) = 0 := by
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
  match _h : gbTop buckets with
  | none => rem
  | some (d, cf) =>
    if _hcf : cf = 0 then
      normalFormFastGo (cleanTop d buckets) rem G
    else
      match _hfind : G.find? (fun g => !g.terms.isEmpty && MvDegrees.divides (multidegree g) d
          && decide ((g.terms.headD (0, 0)).2 * (cf / (g.terms.headD (0, 0)).2) = cf)) with
      | some g =>
        normalFormFastGo (gbInsert buckets
          (-(sparseMonomial (d - multidegree g) (cf / (g.terms.headD (0, 0)).2) * g))) rem G
      | none =>
        normalFormFastGo (gbInsert buckets (-(sparseMonomial d cf)))
          (rem + sparseMonomial d cf) G
termination_by (gbSum buckets, (buckets.map (fun b => b.terms.length)).sum)
decreasing_by
  · have hub : ∀ b ∈ buckets, ∀ t ∈ b.terms, t.1 ≤ d := gbTop_terms_le _h
    have hcoeff : MvPolynomial.coeff (MvDegrees.toFinsupp d) (toPoly (gbSum buckets)) = cf := by
      have hs := gbTop_spec buckets; rw [_h] at hs; exact hs.1
    have hsum_eq : gbSum (cleanTop d buckets) = gbSum buckets := by
      rw [cleanTop_sum d buckets hub, hcoeff, _hcf, sparseMonomial_zero, sub_zero]
    rw [hsum_eq]
    exact Prod.Lex.right _ (cleanTop_terms_lt d buckets (gbTop_mem _h))
  · have hlead : (gbSum buckets).terms = (d, cf) :: (gbSum buckets).terms.tail := gbTop_lead _h _hcf
    have hpred := List.find?_some _hfind
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
  · have hlead : (gbSum buckets).terms = (d, cf) :: (gbSum buckets).terms.tail := gbTop_lead _h _hcf
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
    match _h : reduceLeadByList i x f G with
    | some f' => normalForm f' G
    | none => sparseMonomial i x + normalForm (ofSortedList as (sorted_tail hA)) G
termination_by f
decreasing_by
  · exact reduceLeadByList_lex hA _h
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

def leadCoeff (a : MvSparsePoly R nvars) : R := (a.terms.headD (0, 0)).2


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

omit [DecidableEq R] in
lemma coeff_at_multidegree {a : MvSparsePoly R nvars} (ha : a.terms ≠ []) :
    MvPolynomial.coeff (MvDegrees.toFinsupp (multidegree a)) (toPoly a) = leadCoeff a := by
  obtain ⟨hd, tl, hA⟩ := List.exists_cons_of_ne_nil ha
  have hmd : multidegree a = hd.1 := by unfold multidegree; rw [hA]; rfl
  have hlc : leadCoeff a = hd.2 := by unfold leadCoeff; rw [hA]; rfl
  rw [hmd, hlc]
  exact coeff_toPolyCore_mem a.sorted (hA ▸ List.mem_cons_self)

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

omit [DecidableEq R] in
lemma leadCoeff_ne_zero {a : MvSparsePoly R nvars} (ha : a.terms ≠ []) : leadCoeff a ≠ 0 := by
  obtain ⟨hd, tl, hA⟩ := List.exists_cons_of_ne_nil ha
  have hlc : leadCoeff a = hd.2 := by unfold leadCoeff; rw [hA]; rfl
  rw [hlc]
  exact a.nonzero hd (hA ▸ List.mem_cons_self)

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

lemma dvd_imp_divides [IsDomain R] {a b : MvSparsePoly R nvars} (h : b ∣ a) (ha : a.terms ≠ []) :
    MvDegrees.divides (multidegree b) (multidegree a) = true := by
  obtain ⟨d, hd⟩ := h
  have hb : b.terms ≠ [] := fun hbnil => ha
    (by rw [hd, terms_eq_nil_iff_eq_zero.mp hbnil, zero_mul]; rfl)
  have hdd : d.terms ≠ [] := fun hdnil => ha
    (by rw [hd, terms_eq_nil_iff_eq_zero.mp hdnil, mul_zero]; rfl)
  have hmd : multidegree a = multidegree b + multidegree d := by
    rw [hd]; exact multidegree_mul hb hdd
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

/-! ### Bridge to Mathlib's `MonomialOrder`

Mathlib's `MonomialOrder σ` bundles a synonym type `syn`, an additive equivalence
`(σ →₀ ℕ) ≃+ syn`, monotone w.r.t. the divisibility order, into a linearly ordered
cancellative, well-founded additive monoid. Our admissible order lives on `MvDegrees nvars`
(a `WOrdering`), and `MvDegrees nvars ≃+ (Fin nvars →₀ ℕ)`. Transporting along that equiv
packages our order as a genuine `MonomialOrder (Fin nvars)`, so every result we prove
computationally can be consumed by the rest of Mathlib's Gröbner / initial-ideal API. -/

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

/-! ### Dictionary: our `multidegree`/`leadCoeff` vs Mathlib's `MonomialOrder.degree`/`leadingCoeff`

With the bridge in hand we can translate our computable leading-term data into Mathlib's abstract
notions, transported across `toPoly`. After this, anything Mathlib proves generically about
`MonomialOrder.degree`/`leadingCoeff` (degree of a product, leading-coeff multiplicativity,
initial ideals, …) specialises to our computable polynomials for free. -/

@[simp] lemma toMonomialOrder_toSyn_apply (c : Fin nvars →₀ ℕ) :
    WOrdering.toMonomialOrder.toSyn c = MvDegrees.ofFinsupp c := rfl

omit [DecidableEq R] in
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

omit [DecidableEq R] in
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

omit [DecidableEq R] in
/-- **Leading coefficient agrees.** Mathlib's leading coefficient of `toPoly a` is our
computable `leadCoeff a`. -/
lemma toMonomialOrder_leadingCoeff (a : MvSparsePoly R nvars) :
    WOrdering.toMonomialOrder.leadingCoeff (toPoly a) = leadCoeff a := by
  unfold MonomialOrder.leadingCoeff
  rw [toMonomialOrder_degree, coeff_toPoly_multidegree]


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
        have hmd : multidegree (ofSortedList as (sorted_tail hA)) = p.1 := by
          simp [multidegree, hps]
        rw [hmd]; exact htail_terms_lt p (hps ▸ List.mem_cons_self)
      exact lt_of_le_of_lt (le_trans (degree_le_multidegree hs)
        (normalForm_multidegree_le _ G)) hmdtail
    rw [add_sparseMonomial_terms hx hq_lt] at ht
    rcases List.mem_cons.mp ht with rfl | htq
    · exact reduceLeadByList_none_not_reducible h
    · exact ih t htq

/-! ### Buchberger's S-polynomial criterion (computational verifier)

`sPoly g₁ g₂` is the S-polynomial: with leading monomials `c₁·x^α₁`, `c₂·x^α₂` and
`γ = lcm α₁ α₂`, it is `(x^(γ-α₁)/c₁)·g₁ - (x^(γ-α₂)/c₂)·g₂`, engineered so its two leading
terms cancel. `isGroebnerBasis G` runs the criterion: every pairwise S-polynomial reduces to `0`
modulo `G` (via `normalForm`).

WHAT IS PROVED:
* `sPoly_mem_ideal` — each S-polynomial lies in `⟨G⟩`. Combined with
  `mem_idealOf_of_normalForm_eq_zero`, the **sound** direction holds: if `normalForm f G = 0`
  then `f ∈ ⟨G⟩`, for *any* `G`.
* `sPoly_toPoly_of_coprime` — Buchberger's First (gcd) Criterion, algebraic core: when the
  leading monomials are coprime, `S(f,g)` is the explicit cross-combination
  `(x^β/lc f)·f − (x^α/lc g)·g` (a standard representation). `isGroebnerBasis` uses the
  `coprimeLead` test to prune such pairs.

WHAT IS NOT PROVED (and deliberately carries no `sorry`): the soundness of the *criterion*
itself — that `isGroebnerBasis G = true` implies `G` is a genuine Gröbner basis, hence that
`normalForm` becomes a *complete* membership decision (`f ∈ ⟨G⟩ ↔ normalForm f G = 0`). That is
Buchberger's theorem; its formalisation needs the theory of leading-term ideals, Dickson's
lemma, and uniqueness of remainders — a major development absent even from current Mathlib. The
coprime pruning likewise relies on that theory for its "reduces to 0" conclusion (only the
algebraic identity is formalised). So `isGroebnerBasis` is an honest *computational* verifier. -/

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

/-! #### Buchberger's First (gcd) Criterion

When the leading monomials of `f` and `g` are coprime (share no variable), `S(f,g)`
automatically reduces to `0`, so the pair may be skipped. We prove the *algebraic core* of the
criterion (`sPoly_toPoly_of_coprime`) and use the coprimeness test to prune the verifier. -/

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

/-- **Buchberger's criterion (computational), with the First-Criterion optimisation.** `true` iff
every pair from `G` either has coprime leading terms (skipped — `sPoly_toPoly_of_coprime` is the
proved algebraic justification) or has its S-polynomial reduce to `0` modulo `G`. Meant to be *run*
(its result is a `Bool`); see the section comment on the status of its soundness as a Gröbner test.
The coprime pruning avoids the expensive `normalForm` on pairs the criterion guarantees. -/
def isGroebnerBasis [Div R] (G : List (MvSparsePoly R nvars)) : Bool :=
  (allPairs G).all (fun p =>
    coprimeLead p.1 p.2 || decide (normalForm (sPoly p.1 p.2) G = 0))

/-! ### Formal partial derivative

`pderiv k p` differentiates `p` with respect to the `k`-th variable, computably. We prove it
agrees with Mathlib's `MvPolynomial.pderiv` across `toPoly`, so the computation is certified.
(Foundation for square-free factorisation via `gcd(f, ∂f)`.) -/

/-- Value of `toFinsupp d` at coordinate `v` is the `v`-th exponent. -/
lemma toFinsupp_apply (d : MvDegrees nvars) (v : Fin nvars) :
    MvDegrees.toFinsupp d v = d.degrees[(v : ℕ)]'(by rw [d.correct]; exact v.2) := by
  simp only [MvDegrees.toFinsupp, Finsupp.onFinset_apply, Fin.getElem_fin]

/-- `toFinsupp` turns truncated subtraction into `Finsupp` subtraction. -/
lemma toFinsupp_sub (a b : MvDegrees nvars) :
    MvDegrees.toFinsupp (a - b) = MvDegrees.toFinsupp a - MvDegrees.toFinsupp b := by
  ext v
  simp only [Finsupp.tsub_apply, toFinsupp_apply, Array.getElem_zipWith,
    show (a - b).degrees = Array.zipWith (· - ·) a.degrees b.degrees from rfl]

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

set_option linter.hashCommand false

/-- Display a polynomial as a list of `(exponent-vector, coefficient)` pairs. -/
private def disp (p : MvSparsePoly ℚ 2) : List (List ℕ × ℚ) :=
  p.terms.map (fun t => (t.1.degrees.toList, t.2))

private abbrev x : MvSparsePoly ℚ 2 := X 0
private abbrev y : MvSparsePoly ℚ 2 := X 1

#guard disp (x + y)                 = [([1, 0], 1), ([0, 1], 1)]
#guard disp (x * y)                 = [([1, 1], 1)]
#guard disp ((x + y) * (x + y))     = [([2, 0], 1), ([1, 1], 2), ([0, 2], 1)]
#guard disp ((x + C 1) * (x + C 1)) = [([2, 0], 1), ([1, 0], 2), ([0, 0], 1)]
#guard disp (x * x - y * y)         = [([2, 0], 1), ([0, 2], -1)]

#guard multidegree ((x + y) * (x * x + C 2))
        = multidegree (x + y) + multidegree (x * x + C 2)
#guard leadCoeff ((C 3 * x + y) * (C 5 * x + C 7))
        = leadCoeff (C 3 * x + y) * leadCoeff (C 5 * x + C 7)

#guard ((x + y) * (x + C 1)) / (x + C 1) = x + y
#guard (x * x - y * y) / (x - y) = x + y
#guard (x * x - y * y) / (x + y) = x - y

#guard (x + C 1) * (divRem (x * x * x + y) (x + C 1)).1 + (divRem (x * x * x + y) (x + C 1)).2
        = x * x * x + y
#guard (divRem ((x + y) * (x + C 1)) (x + C 1)).2 = 0
#guard disp (divRem (x * x + C 1) (x + C 1)).2 = [([0, 0], 2)]

#guard (x + y) * (x - y) = x * x - y * y

#guard eval ![3, 5] (x * y + C 1) = 16
#guard eval ![3, 5] ((x + y) * (x + y)) = 64
#guard eval ![2, 7] (x * x * x - C 2 * y) = -6

#guard disp (pderiv 0 (x * x + y)) = [([1, 0], 2)]
#guard disp (pderiv 1 (x * x + y)) = [([0, 0], 1)]
#guard disp (pderiv 0 (x * x * y + C 3 * x)) = [([1, 1], 2), ([0, 0], 3)]
#guard pderiv 1 (x * x + C 5) = 0

private def mulRef (a b : MvSparsePoly ℚ 2) : MvSparsePoly ℚ 2 :=
  ofList do
    let (i, c) ← a.terms
    let (j, d) ← b.terms
    return (i + j, c * d)

#guard ((x + y) * (x + C 1)) = mulRef (x + y) (x + C 1)
#guard ((x * x + C 2 * y + C 3) * (y * y - x + C 5)) =
  mulRef (x * x + C 2 * y + C 3) (y * y - x + C 5)
#guard ((x + y) * (x + y) * (x + y)) = mulRef (mulRef (x + y) (x + y)) (x + y)

#guard disp (normalForm (x * x + C 1) [x]) = [([0, 0], 1)]
#guard normalForm (x * y) [x] = 0
#guard normalForm (x * y + y) [x, y] = 0
#guard normalForm (x * x + x + C 1) [y] = x * x + x + C 1

#guard sPoly x y = 0
#guard isGroebnerBasis [x, y] = true
#guard disp (sPoly (x * x) (x * y + C 1)) = [([1, 0], -1)]
#guard normalForm (sPoly (x * x) (x * y + C 1)) [x * x, x * y + C 1] ≠ 0
#guard isGroebnerBasis [x * x, x * y + C 1] = false
#guard isGroebnerBasis [x * x + y] = true

#guard coprimeLead x y = true
#guard coprimeLead (x * x) (x * y + C 1) = false

end MvSparsePoly.Examples
