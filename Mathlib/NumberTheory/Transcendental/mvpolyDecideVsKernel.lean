/-
# Local A/B: `decide` vs `decide +kernel` on our reflected normal-form goals

This is NOT part of the library (no theorems contributed; it only times tactic calls). It isolates the
*one* comparison we can run entirely inside this repo: closing the **same** reflected goal with plain
`decide` versus `decide +kernel`.

Our shipping tactics (`mv_decide`/`poly_decide`) hardcode `decide +kernel`. Here we define twin
tactics `mv_decide_plain`/`poly_decide_plain` that are byte-for-byte identical to the originals except
the final step is plain `decide`. Both reuse the exported reflection machinery (`reifyK`,
`bridgeSimpK`, `eq_of_core`/`ne_of_core`), so the *only* difference measured is the closing idiom:

* `decide`          — elaborator reduces the `Decidable` instance (to build the proof), then the kernel
                      re-checks it. Two reductions.
* `decide +kernel`  — skips the elaborator reduction; the kernel does it once.

`set_option profiler true` reports `tactic execution` (elaborator) + `type checking` (kernel)
separately, so we see exactly where the time goes.

Run: `lake env lean Mathlib/NumberTheory/Transcendental/mvpolyDecideVsKernel.lean`
-/
import Mathlib.NumberTheory.Transcendental.mvpolyReflectKernel
import Mathlib.NumberTheory.Transcendental.polyReflectKernel

open Lean Elab Tactic Meta

/-- Twin of `mv_decide`, identical except it closes with plain `decide` (no `+kernel`). -/
elab "mv_decide_plain" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← g.getType)
  let (isNeg, p, q) ←
    if let some (_, a, b) := tgt.eq? then pure (false, a, b)
    else if let some inner := tgt.not? then
      if let some (_, a, b) := (← whnfR inner).eq? then pure (true, a, b)
      else throwError "mv_decide_plain: goal is not an (in)equality of MvPolynomials"
    else throwError "mv_decide_plain: goal is not an (in)equality of MvPolynomials"
  let (``MvPolynomial, #[σ, R, _]) := (← inferType p).getAppFnArgs
    | throwError "mv_decide_plain: goal type is not MvPolynomial (Fin n) R"
  let n := (← whnfR σ).appArg!
  let l₁ ← MvSparsePoly.Kernel.reifyK R n p
  let l₂ ← MvSparsePoly.Kernel.reifyK R n q
  let mkBridge (l orig : Expr) : MetaM Expr := do
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``MvSparsePoly.toPolyCore #[l]) orig)
    let (res, _) ← simpGoal m.mvarId! (← bridgeSimpK)
    if let some (_, m2) := res then m2.refl
    instantiateMVars m
  let hp ← mkBridge l₁ p
  let hq ← mkBridge l₂ q
  let lem := if isNeg then ``MvSparsePoly.Kernel.ne_of_core else ``MvSparsePoly.Kernel.eq_of_core
  let partialPf ← mkAppM lem #[l₁, l₂, hp, hq]
  let coreTy := (← inferType partialPf).bindingDomain!
  let mCore ← mkFreshExprSyntheticOpaqueMVar coreTy
  g.assign (.app partialPf mCore)
  replaceMainGoal [mCore.mvarId!]
  evalTactic (← `(tactic| decide))

/-- Twin of `poly_decide`, identical except it closes with plain `decide` (no `+kernel`). -/
elab "poly_decide_plain" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← g.getType)
  let (isNeg, p, q) ←
    if let some (_, a, b) := tgt.eq? then pure (false, a, b)
    else if let some inner := tgt.not? then
      if let some (_, a, b) := (← whnfR inner).eq? then pure (true, a, b)
      else throwError "poly_decide_plain: goal is not an (in)equality of Polynomials"
    else throwError "poly_decide_plain: goal is not an (in)equality of Polynomials"
  let (``Polynomial, #[R, _]) := (← inferType p).getAppFnArgs
    | throwError "poly_decide_plain: goal type is not Polynomial R"
  let l₁ ← SparsePoly.Kernel.reifyK R p
  let l₂ ← SparsePoly.Kernel.reifyK R q
  let mkBridge (l orig : Expr) : MetaM Expr := do
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``SparsePoly.toPolyCore #[l]) orig)
    let (res, _) ← simpGoal m.mvarId! (← SparsePoly.Kernel.bridgeSimpK)
    if let some (_, m2) := res then m2.refl
    instantiateMVars m
  let hp ← mkBridge l₁ p
  let hq ← mkBridge l₂ q
  let lem := if isNeg then ``SparsePoly.Kernel.ne_of_core else ``SparsePoly.Kernel.eq_of_core
  let partialPf ← mkAppM lem #[l₁, l₂, hp, hq]
  let coreTy := (← inferType partialPf).bindingDomain!
  let mCore ← mkFreshExprSyntheticOpaqueMVar coreTy
  g.assign (.app partialPf mCore)
  replaceMainGoal [mCore.mvarId!]
  evalTactic (← `(tactic| decide))

namespace DecideVsKernel

open MvPolynomial

/-! ### Bivariate, degree 4 (`ZMod 7`) — `f·g = g·f` -/

set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 2 * (X 0 + X 1 + 2) ^ 2 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 2 * (X 0 + X 1 + 1) ^ 2 := by mv_decide_plain

set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 2 * (X 0 + X 1 + 2) ^ 2 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 2 * (X 0 + X 1 + 1) ^ 2 := by mv_decide

/-! ### Bivariate, degree 6 (`ZMod 7`) -/

set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 3 * (X 0 + X 1 + 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 3 * (X 0 + X 1 + 1) ^ 3 := by mv_decide_plain

set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 3 * (X 0 + X 1 + 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 3 * (X 0 + X 1 + 1) ^ 3 := by mv_decide

/-! ### Univariate, degree 10 (`ZMod 7`) -/

set_option profiler true in
set_option profiler.threshold 1 in
example : ((Polynomial.X + 1) ^ 5 * (Polynomial.X + 2) ^ 5 : Polynomial (ZMod 7))
    = (Polynomial.X + 2) ^ 5 * (Polynomial.X + 1) ^ 5 := by poly_decide_plain

set_option profiler true in
set_option profiler.threshold 1 in
example : ((Polynomial.X + 1) ^ 5 * (Polynomial.X + 2) ^ 5 : Polynomial (ZMod 7))
    = (Polynomial.X + 2) ^ 5 * (Polynomial.X + 1) ^ 5 := by poly_decide

end DecideVsKernel
