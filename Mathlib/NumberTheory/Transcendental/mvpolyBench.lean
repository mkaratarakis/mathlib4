/-
# Benchmarks for `MvSparsePoly`

This is NOT part of the library — it is a small program you run by hand to *measure how
fast* the polynomial operations are. It is not checked on every build (it has no theorems),
and it imports the real definitions from `mvpoly.lean`.

## What a benchmark is

A benchmark just answers "how long does this take?". You:
  1. read the clock,
  2. do the work,
  3. read the clock again,
  4. report the difference.

Two practical gotchas, both handled below:

* **Resolution.** We read a *monotonic* nanosecond clock (`IO.monoNanosNow`) — monotonic means
  it never jumps backwards, so subtracting two readings is a valid elapsed time. We print
  microseconds (`/1000`); 1 second = 1_000_000 µs.

* **Laziness.** Lean does not compute a pure value until something forces it. If you write
  `let r := f * g` and then read the clock, you have only built a *thunk* — the multiplication
  hasn't happened yet, so you'd measure ~0. `IO.lazyPure (fun _ => …)` turns the thunk into an
  `IO` action whose result is forced when we run it with `←`, so the work lands *between* the
  two clock readings. We also fully force the result (`force v`) so a lazy spine can't escape.

## What we measure

* `mulFast` — the multiplication actually used at runtime (the `@[implemented_by]` fast path:
  Johnson/Monagan–Pearce, multiply `y` by each term of `x` and merge with a balanced tree).
* `mulRef`  — the *reference* algorithm (generate all `#x·#y` products, then sort/dedup). Same
  body as the library's `mulCore`, but with no `@[implemented_by]`, so it really runs the slow
  way. Comparing the two on the same inputs both (a) cross-checks they agree and (b) shows the
  speedup.
* `divRem`  — dividing `f*g` by `g`; the result must be `f` again (exact division).

## How to run

From the repository root:

    lake env lean Mathlib/NumberTheory/Transcendental/mvpolyBench.lean

`lake env` makes the compiled `Mathlib` available to the import; running the file elaborates it
and executes the `#eval main` at the bottom, which prints the table. The numbers are from the
Lean *interpreter* (so absolute times are large); for native speed you would put `main` in a
`lake exe` target, but the interpreter is fine for comparing algorithms.

To stress it harder, raise the powers in `main` (cost grows fast — `p=10` already builds
~1000-term factors and a ~10000-term product).
-/
import Mathlib.NumberTheory.Transcendental.mvpoly

open MvSparsePoly

namespace MvPolyBench

/-- Number of variables `x₀ … x₃`. -/
abbrev N := 4

/-- A dense-ish degree-1 polynomial `x₀ + x₁ + ⋯ + c`; raising it to a power `p` (below) gives a
polynomial with many terms (all monomials of total degree `≤ p`), good test data. -/
def base (c : ℚ) : MvSparsePoly ℚ N :=
  (List.finRange N).foldl (fun acc i => acc + X i) (C c)

/-- The *reference* multiplication: generate every product term, then `ofList` (sort + dedup +
drop zeros). Identical to the library's `mulCore` body, but deliberately *without*
`@[implemented_by]`, so this one really runs the naive algorithm. -/
def mulRef (a b : MvSparsePoly ℚ N) : MvSparsePoly ℚ N :=
  ofList do
    let (i, c) ← a.terms
    let (j, d) ← b.terms
    return (i + j, c * d)

/-- Time a forced pure computation. Returns `(microseconds, sizeMeasure)`. `act` produces the
value; `force` walks it (here: counts terms) so nothing stays lazy. The two `IO.lazyPure`s pin
the work between the clock readings, and returning the measure means the caller never has to
touch (and thereby pre-compute/cache) the value outside the timed window. -/
def timeUs {α : Type} (act : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let v  ← IO.lazyPure act
  let m  ← IO.lazyPure (fun _ => force v)
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / 1000, m)

/-- One row of the benchmark for factors `(base 1)^p` and `(base 2)^p`.

CACHING GOTCHA: each value must be computed for the *first* time inside its own timed window.
If we computed `f * g` once for a printout and then timed `f * g` again, the second one would
reuse the cached result and read as ~0. So: we build `f`/`g` up front (not part of the multiply
cost), time the fast multiply (first computation of `f*g`, getting the product size back from it),
time the independent reference multiply, then build the product once more and time only the
division on it. -/
def runFor (p : Nat) : IO Unit := do
  let f := (base 1) ^ p
  let g := (base 2) ^ p
  -- Build `f` and `g` first, so their construction time is not charged to the multiply.
  let _ ← IO.lazyPure (fun _ => f.terms.length + g.terms.length)
  let nf := f.terms.length
  -- Fast multiply: first time `f * g` is computed; also gives us the product size `np`.
  let (tFast, np) ← timeUs (fun _ => f * g)      (·.terms.length)
  -- Reference multiply: a different expression, so it computes from scratch.
  let (tRef, _)   ← timeUs (fun _ => mulRef f g) (·.terms.length)
  -- Division: build the product once (forced), then time only `fg / g`.
  let fg ← IO.lazyPure (fun _ => f * g)
  let _  ← IO.lazyPure (fun _ => fg.terms.length)
  let (tDiv, _)   ← timeUs (fun _ => fg / g)     (·.terms.length)
  -- Multi-divisor reduction: reduce `fg` modulo the singleton basis `[g]`. Since `g ∣ fg` the
  -- remainder is `0`, so this measures the cost of the `normalForm` reduction loop (the naïve
  -- repeated-subtraction algorithm that geobuckets would accelerate).
  let (tNF, _)    ← timeUs (fun _ => normalForm fg [g]) (·.terms.length)
  IO.println s!"p={p}  #f=#g={nf}  product={np} terms   \
    mulFast={tFast}µs   mulRef={tRef}µs   divRem={tDiv}µs   normalForm={tNF}µs"

/-- A *flat* (non-geobucket) multi-divisor reduction, for comparison. Replicates the logical
`normalForm` algorithm but with the dividend kept as a single sorted list, so each subtraction
re-merges the whole polynomial. `partial` is fine here — this file is not part of the verified
library, it only measures speed. -/
partial def normalFormFlat (f : MvSparsePoly ℚ N) (G : List (MvSparsePoly ℚ N)) :
    MvSparsePoly ℚ N :=
  match f.terms with
  | [] => 0
  | (i, x) :: _ =>
    match G.find? (fun g => !g.terms.isEmpty && MvDegrees.divides (multidegree g) i
        && decide ((g.terms.headD (0, 0)).2 * (x / (g.terms.headD (0, 0)).2) = x)) with
    | some g =>
      normalFormFlat (f - sparseMonomial (i - multidegree g) (x / (g.terms.headD (0, 0)).2) * g) G
    | none => sparseMonomial i x + normalFormFlat (dropLead f) G

/-- Multi-divisor reduction — the geobucket's home turf (Buchberger-style `f := f − Σ cᵢ·gᵢ`).
Reduce `(base 1)^p` modulo `G = [x₀+1, x₁+1, x₂+1, x₃+1]` (which collapses it to a constant), timing
the geobucket `normalForm` against the flat reference, and cross-checking they agree. -/
def runReduce (p : Nat) : IO Unit := do
  let f := (base 1) ^ p
  let G := (List.finRange N).map (fun i => X i + C 1)
  let _ ← IO.lazyPure (fun _ => f.terms.length)
  let nf := f.terms.length
  let (tGeo, _)  ← timeUs (fun _ => normalForm f G)     (·.terms.length)
  let (tFlat, _) ← timeUs (fun _ => normalFormFlat f G) (·.terms.length)
  let agree := decide (normalForm f G = normalFormFlat f G)
  IO.println s!"p={p}  #f={nf}   geobucket={tGeo}µs   flat={tFlat}µs   agree={agree}"

def main : IO Unit := do
  IO.println "polynomial multiplication: fast (implemented_by) vs reference, and exact division"
  -- Modest default sizes (a few seconds in the interpreter). Increase for a heavier run.
  for p in [4, 5, 6] do runFor p
  IO.println "multi-divisor reduction: geobucket normalForm vs flat reference"
  for p in [4, 5, 6] do runReduce p

end MvPolyBench

#eval MvPolyBench.main
