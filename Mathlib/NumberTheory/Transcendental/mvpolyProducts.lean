/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.mvpoly

/-!
# Pretty-printed product examples for `MvSparsePoly`

A small companion file that (1) gives `MvSparsePoly` a human-readable `Repr` instance, so `#eval`
prints e.g. `x^2 + 2*x*y + y^2` instead of the raw `[([2,0],1),…]` term list, and (2) saves a few
concrete products as named definitions you can reuse.
-/

namespace MvSparsePoly

/-- Variable name for index `i`: `x, y, z, w`, then `x4, x5, …`. -/
private def varName (i : ℕ) : String := (["x", "y", "z", "w"][i]?).getD ("x" ++ toString i)

/-- Render an exponent vector as `x*y^2*…` (empty string for the constant monomial). -/
private def monoString (degs : List ℕ) : String :=
  String.intercalate "*" (degs.zipIdx.filterMap (fun (e, i) =>
    if e = 0 then none
    else if e = 1 then some (varName i)
    else some s!"{varName i}^{e}"))

/-- Human-readable rendering of a polynomial, e.g. `x^2 + 2*x*y + y^2`. -/
def toStringPoly {R : Type} {nvars : ℕ} [CommRing R] [DecidableEq R] [Repr R]
    (p : MvSparsePoly R nvars) : String :=
  if p.terms.isEmpty then "0"
  else String.intercalate " + " (p.terms.map (fun t =>
    let mono := monoString t.1.degrees.toList
    if mono = "" then reprStr t.2
    else if t.2 = 1 then mono
    else s!"{reprStr t.2}*{mono}"))

/-- `#eval` now prints `MvSparsePoly` as an actual polynomial. -/
instance {R : Type} {nvars : ℕ} [CommRing R] [DecidableEq R] [Repr R] :
    Repr (MvSparsePoly R nvars) where
  reprPrec p _ := toStringPoly p

end MvSparsePoly

namespace MvSparsePoly.ProductExamples

open MvSparsePoly

abbrev x : MvSparsePoly ℚ 2 := X 0
abbrev y : MvSparsePoly ℚ 2 := X 1

/-- Saved products — genuine `MvSparsePoly` values you can reuse. -/
def diffOfSquares := (x + y) * (x - y)
def cubeOfSum := (x + C 1) * (x + C 1) * (x + C 1)
def sumSquared := (x + y) * (x + y)
def sumToFourth := sumSquared * sumSquared
def mixed := (C 2 * x + C 3 * y) * (x * x + y)

-- `#eval` prints them as polynomials (thanks to the `Repr` instance above):
#eval diffOfSquares   -- x^2 + -1*y^2
#eval cubeOfSum       -- x^3 + 3*x^2 + 3*x + 1
#eval sumSquared      -- x^2 + 2*x*y + y^2
#eval sumToFourth     -- x^4 + 4*x^3*y + 6*x^2*y^2 + 4*x*y^3 + y^4
#eval mixed           -- 2*x^3 + 3*x^2*y + 2*x*y + 3*y^2

-- Machine-checked correctness: each product equals an independently-written expansion.
-- (A failing `#guard` is a build error, so if this file compiles the products are correct.)
set_option linter.hashCommand false in
#guard diffOfSquares = x * x - y * y
set_option linter.hashCommand false in
#guard cubeOfSum = x * x * x + C 3 * (x * x) + C 3 * x + C 1
set_option linter.hashCommand false in
#guard sumSquared = x * x + C 2 * (x * y) + y * y
set_option linter.hashCommand false in
#guard sumToFourth = x*x*x*x + C 4*(x*x*x*y) + C 6*(x*x*y*y) + C 4*(x*y*y*y) + y*y*y*y
set_option linter.hashCommand false in
#guard mixed = C 2 * (x*x*x) + C 3 * (x*x*y) + C 2 * (x*y) + C 3 * (y*y)

end MvSparsePoly.ProductExamples
