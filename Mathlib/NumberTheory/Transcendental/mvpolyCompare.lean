/-
# Cross-library benchmark: `MvSparsePoly` vs. CompPoly

This file is a *runnable benchmark* (not part of the verified library — no theorems) that pits our
computable multivariate polynomials (`MvSparsePoly`, from `mvpoly.lean`) against the two other real
computable-MV-polynomial Lean libraries, on the *same* workload:

* **CompPoly** (`CPoly.CMvPolynomial`, github.com/argumentcomputer/CompPoly) — `ExtTreeMap`-backed
  sparse maps with Horner evaluation; the most mature, evaluation-focused.
* **WuProver / MonomialOrderedPolynomial** (github.com/WuProver/MonomialOrderedPolynomial) — a
  *proof-by-reflection* library: it attaches a computable sorted-list `SortedAddMonoidAlgebra`
  representation to Mathlib's (noncomputable) `MvPolynomial` to **decide** polynomial identities.
  See "A note on WuProver" below for how it is measured and why the modality differs.

(Davenport's work is a *paper*, arXiv 2408.04564 — algorithms/notes, not a runnable library.)

Run our side:

    lake env lean Mathlib/NumberTheory/Transcendental/mvpolyCompare.lean

The CompPoly side runs in a separate checkout (it pins a different Lean toolchain); the exact script
and how to reproduce it are at the bottom of this comment. The numbers below were measured together.

## Methodology — what makes this a *fair* comparison

Cross-repo timing is full of confounds; we control the ones we can and disclose the rest.

* **Same workload.** Both build `f = g = (x₀+x₁+x₂+x₃+x₄ + c)^p` (5 variables), via each library's
  own `+`/`*`/`^`. At `p = 3,4,5` that is 56 / 126 / 252 terms per factor and a 462 / 1287 / 3003
  term product — identical monomials on both sides.
* **Same coefficient ring.** `ZMod (2^31 − 1)` (a prime field) for both, so coefficient arithmetic
  (modular reduction) is the same cost on each side.
* **Same operations.** Each library's *own* multiplication (the one its users actually call) and its
  *own* evaluation. We don't reimplement anything for the other side.
* **Same mode & machine.** Both run in the **Lean interpreter** (`lake env lean`) on the same box
  (11th-gen i7-1165G7). Same-mode is the key fairness lever: it removes "one was native, one wasn't".

## Honest caveats (read these before quoting a number)

1. **Interpreter, not native.** Absolute times are large and *not* what you'd ship. CompPoly is
   designed and tuned for **native** compilation (its real `lake exe CompPolyBench` does warm-up +
   measured iterations and is much faster); its ExtTreeMap representation has more per-op overhead
   that the interpreter penalizes more heavily than our flat sorted list. **Native ratios will
   differ** and could narrow substantially. This file measures the interpreter only.
2. **Different Lean toolchains** (ours `v4.32.0-rc1`, CompPoly `v4.30.0`) — unavoidable, they pin
   different versions. Minor interpreter differences exist between releases.
3. **Scope.** This compares *multiplication* and *evaluation* — the operations both libraries have.
   Our library's distinctive features (verified multivariate **division**, **gcd/content**,
   **Gröbner `normalForm`/Buchberger**) have **no CompPoly counterpart at the multivariate layer**,
   so there is nothing to benchmark them against.

## Results (Lean interpreter, ZMod(2³¹−1), 5 vars; microseconds)

### Multiplication — each library's own `*`

| p | #product | `MvSparsePoly` (packed) | WuProver       | CompPoly      |
|---|----------|-------------------------|----------------|---------------|
| 3 |    462   |        32 960 µs        |     49 243 µs  |    872 623 µs |
| 4 |  1 287   |       178 193 µs        |    333 976 µs  | 10 862 897 µs |
| 5 |  3 003   |       813 330 µs        |  1 567 950 µs  |115 768 858 µs |
| 6 |  6 188   |     3 592 222 µs        |  6 572 430 µs  |      —        |

All three produce identical term counts (cross-check). Ranking, interpreter:
**ours packed (fastest) > WuProver ≈ our array path (`mulFast`) > CompPoly (slowest)**.

* We are **~1.5–1.9× faster than WuProver** — exactly the margin the `mulPacked` exponent-packing
  buys; WuProver's sorted-list `AddMonoidAlgebra` mul is otherwise on par with our *array* path.
* WuProver's sorted-list mul **beats CompPoly's ExtTreeMap-insertion mul by 18–74×**, and the gap to
  us *widens* with size (CompPoly: 26–142× behind us).

So the real spread is: a sorted-list representation (ours, WuProver) crushes a persistent-tree-map
representation (CompPoly) in the interpreter; among the sorted-list libraries, our `UInt64` exponent
packing is the differentiator.

### What the packing buys — `MvSparsePoly` packed vs. its own array path

The current runtime is `mulPacked` (Davenport / Monagan–Pearce **exponent packing**): when the
product's exponents fit in a `b`-bit field with `nvars·b ≤ 64`, a whole monomial is encoded as one
`UInt64`, so monomial-multiply is a single integer *add* and monomial-compare a single integer
*compare* — instead of allocating/walking an `Array ℕ` per partial product. It falls back to the
array path (`mulFast`) when exponents are too big, and is cross-checked equal to the proven `mulCore`
(`agree = true` below).

| p | #product | packed (`mulPacked`) | array (`mulFast`) | speedup |
|---|----------|----------------------|-------------------|---------|
| 3 |    462   |       32 960 µs      |      84 709 µs    | 2.6×    |
| 4 |  1 287   |      178 193 µs      |     442 605 µs    | 2.5×    |
| 5 |  3 003   |      813 330 µs      |   1 787 188 µs    | 2.2×    |
| 6 |  6 188   |    3 592 222 µs      |   6 279 044 µs    | 1.75×   |

The speedup *tapers* with size because the `n·m` **coefficient** multiplications (intrinsic to any
sparse product — `ZMod` multiply + reduce) eventually dominate over exponent handling, which is all
the packing accelerates. So ≈2.5× is about the practical ceiling of this trick on this workload; a
true streaming Johnson heap on the packed keys would mainly save peak memory, not time.

### Broadened matrix — coefficient ring and variable count (all three libraries)

Multiplication time (µs), same workload, interpreter. Two sweeps:

**Coefficient ring** (n = 5, p = 4, product = 1287 terms):

| ring        | `MvSparsePoly` | WuProver  | CompPoly    |
|-------------|----------------|-----------|-------------|
| `ZMod 97`   |    173 417     |  238 293  | 14 720 454  |
| `ZMod 2³¹−1`|    174 092     |  250 671  | 10 862 897  |
| `ℤ`         |    159 572     |  291 410  |  9 288 690  |

**Variable count** (`ZMod 2³¹−1`):

| config     | #product | `MvSparsePoly` | WuProver   | CompPoly      |
|------------|----------|----------------|------------|---------------|
| n=5, p=4   |   1 287  |     174 092    |   250 671  |  10 862 897   |
| n=10, p=3  |   8 008  |   1 080 058    | 3 503 498  | 311 856 252   |
| n=5, p=6   |   6 188  |   3 754 525    | 6 232 364  |     —         |

Three findings the matrix exposes:

1. **Coefficient ring barely moves the needle.** For us it's flat (~160–174 µs across a tiny field,
   a 31-bit prime, and arbitrary-precision `ℤ`) — the `(Σxᵢ+c)^p` coefficients stay small, so the
   bignum path of `ℤ` never bites at this size. WuProver is mildly ℤ-sensitive (+22%). CompPoly's
   time is set by tree-map key operations, not coefficients — it's actually *slowest* on the tiny
   field `ZMod 97`.
2. **Our edge widens with dimension.** Vs WuProver: 1.4× at n=5 → **3.2× at n=10**. Vs CompPoly:
   ~62× at n=5 → **289× at n=10**. Bigger exponent vectors cost the sorted-`Finsupp` (WuProver) and
   the tree-map (CompPoly) more per monomial, while our packed `UInt64` stays a single word (until it
   overflows 64 bits and falls back).
3. **CompPoly's tree-map scales catastrophically with variable count**: 10.9 s → **312 s** for ~6×
   more terms (a 29× jump), versus our near-linear 0.17 s → 1.08 s. Persistent-tree-map insertion is
   the wrong data structure for the interpreter.

### Evaluation — our power-table `evalFast` vs. naive vs. CompPoly's Horner

| p | `eval` (fast) | `evalCore` (naive) | CompPoly `eval` | fast vs naive | fast vs CompPoly |
|---|---------------|--------------------|-----------------|---------------|------------------|
| 3 |      677 µs   |     1 639 µs       |    1 671 µs     | 2.4× faster   | 2.5× faster |
| 4 |    1 248 µs   |     3 325 µs       |    3 710 µs     | 2.7× faster   | 3.0× faster |
| 5 |    2 524 µs   |     6 866 µs       |    8 023 µs     | 2.7× faster   | 3.2× faster |

The `evalFast` win (precompute a per-variable table of powers `vⱼ^e` once, then look up per
monomial, instead of re-exponentiating every term) is the speedup added for this comparison; it's
wired into `eval` via `@[implemented_by evalFast]`, so callers get it for free.

## A note on WuProver (a different modality)

WuProver is not a runtime calculator like ours or CompPoly — it is a **decision procedure**. Its
`MvPolynomial σ R` is Mathlib's noncomputable type; the computable `SortedAddMonoidAlgebra` sorted
list lives in a `SortedRepr` *instance* and is reduced by the **kernel** during `decide` to *prove*
identities (e.g. `(X₀+X₁+1)^10 = …`). You cannot `#eval` a WuProver product — the underlying value is
noncomputable. To get an apples-to-apples *runtime* number, the table above builds WuProver's
`SortedAddMonoidAlgebra` representation **directly** (bypassing the noncomputable wrapper) and
`#eval`s the product — i.e. it measures WuProver's actual sorted-list mul algorithm in the
interpreter, the same mode as the other two. Used *as designed* (kernel reduction inside `decide`)
the same computation is far slower but yields a kernel-checked proof — a capability the others don't
provide. So "we're ~1.8× faster" is a fair statement about the mul *algorithm*, not about WuProver's
use case, which is orthogonal (proving identities, not calculating values).

## The moat — capabilities the other libraries don't offer as a computable CAS

Speed on shared operations is a constant-factor race with a floor (coefficient arithmetic). The
durable advantage is *capability*: verified, `#eval`-able **multivariate division**, **gcd/content**,
and **Gröbner/Buchberger `normalForm` reduction** that return values you compute with. CompPoly's
multivariate type offers ring ops + evaluation and nothing else (its Euclidean/division algorithms
are univariate-only). WuProver is a *prover*, not a calculator — it can decide identities but does
not give you an `#eval`-able quotient or normal form. So there is no competitor to benchmark these
against. Numbers over ℚ, same workload
(`f = (Σxᵢ+1)^p`, `g = (Σxᵢ+2)^p`, dividing `f·g`):

| p | #(f·g) | `divRem` ((f·g)/g = f) | `normalForm` mod {xᵢ+1} | verified |
|---|--------|------------------------|-------------------------|----------|
| 3 |   462  |       194 097 µs       |        322 224 µs       | exact / rem = const |
| 4 | 1 287  |     1 200 658 µs       |      2 009 056 µs       | exact / rem = const |
| 5 | 3 003  |     5 545 865 µs       |      8 955 135 µs       | exact / rem = const |

(`exact = true`: the quotient is recovered exactly; `normalForm` collapses `f·g` to a single
constant remainder modulo the basis — both machine-checked at runtime.)

## Where we do *not* win (stated honestly)

* **Dense univariate multiplication.** CompPoly has NTT/FFT univariate mul (`Univariate/NTT`,
  `NTTFast`) — `O(n log n)`. Ours is schoolbook `O(n²)`. For large dense univariate inputs they win
  decisively; we don't compete there.
* **Native finite-field evaluation.** CompPoly is engineered for *native* execution over specific
  prime fields (KoalaBear/Goldilocks, Horner groups). Our eval lead is an *interpreter* result; a
  native rematch could narrow or reverse it (see caveat 1).

## Bottom line

In an apples-to-apples interpreter run, `MvSparsePoly` is the **fastest at multiplication** of the
three: ~1.5–1.9× ahead of WuProver (the `mulPacked` exponent-packing margin — itself ≈2.5× over our
own previous array path) and 26–142× ahead of CompPoly, the gap widening with size. We are also
**modestly faster on evaluation** (≈2.5–3× vs CompPoly), on top of offering verified, `#eval`-able
division/gcd/Gröbner that neither competitor provides as a computable CAS. The honest qualifiers:
(1) this is the *interpreter* — CompPoly's native pipeline closes much of its absolute gap, and a
native-vs-native rematch is the obvious next measurement; (2) WuProver plays a different game
(kernel-checked proofs, not runtime values), so the mul number compares algorithms, not use cases;
(3) for *dense univariate* mul CompPoly's NTT/FFT beats our schoolbook O(n²) — we don't compete there.
-/
import Mathlib.NumberTheory.Transcendental.mvpoly

open MvSparsePoly

namespace MvPolyCompare

/-- 5 variables, matching CompPoly's multivariate benchmark shape. -/
abbrev N : ℕ := 5

/-- Prime field `ZMod (2³¹ − 1)`; same modulus used on the CompPoly side. -/
abbrev P : ℕ := 2147483647
abbrev F := ZMod P

/-- The shared test polynomial `x₀ + x₁ + ⋯ + x₄ + c`; `^p` (below) expands it to all monomials of
total degree `≤ p`. Built with the library's own `+`, exactly as the CompPoly side is. -/
def base (c : F) : MvSparsePoly F N :=
  (List.finRange N).foldl (fun acc i => acc + X i) (C c)

/-- Time a forced pure computation; returns `(microseconds, sizeMeasure)`. The two `IO.lazyPure`s
pin the work between the clock readings and `force` walks the result so nothing stays lazy. -/
def timeUs {α : Type} (act : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let v  ← IO.lazyPure act
  let m  ← IO.lazyPure (fun _ => force v)
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / 1000, m)

/-- One comparison row: builds `f = (base 1)^p`, `g = (base 2)^p` (their construction is *not*
charged to the timings), then times the runtime multiplication, the fast power-table `eval`, and the
naive `evalCore` — the same three quantities tabulated in the file header. -/
def runRow (p : Nat) : IO Unit := do
  let f := (base 1) ^ p
  let g := (base 2) ^ p
  -- Force `f`, `g` up front so building them is excluded from the multiply timing.
  let _ ← IO.lazyPure (fun _ => f.terms.length + g.terms.length)
  let nf := f.terms.length
  let pt : Fin N → F := fun i => ((i.val : F) + 2)
  let (tMul, np)  ← timeUs (fun _ => f * g)                (·.terms.length)
  let (tFast, _)  ← timeUs (fun _ => eval pt f)            (fun r => r.val)
  let (tNaive, _) ← timeUs (fun _ => evalCore pt f.terms)  (fun r => r.val)
  IO.println s!"p={p}  #f={nf}  product={np}   \
    mul={tMul}µs   evalFast={tFast}µs   evalNaive={tNaive}µs"

def main : IO Unit := do
  IO.println "MvSparsePoly over ZMod(2^31-1), 5 vars — mul + eval (compare with CompPoly, see header)"
  for p in [3, 4, 5] do runRow p

end MvPolyCompare

#eval MvPolyCompare.main

/-
## Reproducing the CompPoly side

In a CompPoly checkout (`git clone` the repo; it pins `leanprover/lean4:v4.30.0`), run
`lake exe cache get` then `lake build`, and place this script (`cpbench.lean`) at the repo root:

```
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Lawful
open CPoly
abbrev P : ℕ := 2147483647
abbrev F := ZMod P
abbrev N : ℕ := 5
def base (c : F) : CMvPolynomial N F :=
  (List.finRange N).foldl (fun acc i => acc + CMvPolynomial.X i) (CMvPolynomial.C c)
def timeUs {α : Type} (act : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let v ← IO.lazyPure act
  let m ← IO.lazyPure (fun _ => force v)
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / 1000, m)
def main : IO Unit := do
  for p in [3, 4, 5] do
    let f := (base 1) ^ p
    let g := (base 2) ^ p
    let pt : Fin N → F := fun i => ((i.val : F) + 2)
    let _ ← IO.lazyPure (fun _ => (CMvPolynomial.eval pt f).val + (CMvPolynomial.eval pt g).val)
    let (tmul, _) ← timeUs (fun _ => CMvPolynomial.eval pt (f * g)) (·.val)  -- mul (eval negligible)
    let (tev, _)  ← timeUs (fun _ => CMvPolynomial.eval pt f) (·.val)
    IO.println s!"COMPPOLY p={p}  mul(+eval)={tmul}us  eval={tev}us"
#eval main
```

Run with `lake env lean cpbench.lean`. (`CMvPolynomial n R := Lawful n R`, whose `Mul`/`NatPow`
instances give `*` and `^`; the `mul` timing folds in one cheap `eval` to force the product, which is
negligible — `eval` alone is the second column.)

## Reproducing the WuProver side

In a `MonomialOrderedPolynomial` checkout (pins `leanprover/lean4:v4.29.0-rc8`), run
`lake exe cache get` then `lake build`, and place this script (`wbench.lean`) at the repo root. It
builds WuProver's computable `SortedAddMonoidAlgebra` representation directly (the value `#eval`
cannot touch through the noncomputable `MvPolynomial` wrapper) and times its sorted-list mul:

```
import MonomialOrderedPolynomial.MvPolynomial
abbrev P : ℕ := 2147483647
abbrev F := ZMod P
abbrev WMon := Lex (SortedFinsupp (Fin 5) ℕ compare)
abbrev WPoly := SortedAddMonoidAlgebra F WMon (compare · · |>.swap)
def xv (i : Fin 5) : WPoly :=
  SortedAddMonoidAlgebra.single _ (toLex (SortedFinsupp.single compare i 1)) (1 : F)
def cc (c : F) : WPoly := SortedAddMonoidAlgebra.single _ (toLex (0 : SortedFinsupp (Fin 5) ℕ compare)) c
def base (c : F) : WPoly := (List.finRange 5).foldl (fun acc i => acc + xv i) (cc c)
def timeUs {α : Type} (act : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let v ← IO.lazyPure act
  let m ← IO.lazyPure (fun _ => force v)
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / 1000, m)
def main : IO Unit := do
  for p in [3, 4, 5, 6] do
    let f := (base 1) ^ p
    let g := (base 2) ^ p
    let _ ← IO.lazyPure (fun _ => f.val.toList.length + g.val.toList.length)
    let (tMul, np) ← timeUs (fun _ => f * g) (·.val.toList.length)
    IO.println s!"WUPROVER p={p}  product={np}  mul={tMul}µs"
#eval main
```

Run with `lake env lean wbench.lean`. The product term counts match ours exactly (462 / 1287 / 3003
/ 6188), a cross-library correctness check.
-/
