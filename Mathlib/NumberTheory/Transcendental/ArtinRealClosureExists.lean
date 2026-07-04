/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Transfer
import Mathlib.NumberTheory.Transcendental.ArtinRealClosureUnique
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Order.Field.Subfield

/-!
# Uniqueness of real closures: existence of the order-embedding

`ArtinRealClosureUnique.lean` reduced the uniqueness of real closures to the *existence* of an
`F`-algebra homomorphism between them. This file proves that existence, following the classical
Bochnak–Coste–Roy argument (Thm. 1.3.2 there, going back to Artin–Schreier):

* Zorn's lemma runs over `IntermediateField.Lifts F R R'` whose embeddings are **monotone**
  (`R`, `R'` real closed, `R` algebraic over `F`).
* At a maximal lift `(E, f)` with `E ≠ ⊤`, pick `α ∉ E` with minimal polynomial `p` over `E`.
  The Sturm-theoretic root-count transfer `Sturm.card_roots_map_congr` (which only needs the
  *ordered* base `E` and the monotonicity of `f`) shows `p` has as many roots in `R'` as in `R`,
  so `α` — the `k`-th root of `p` in `R` — has a *matched root* `β`: the `k`-th root of `p^f`
  in `R'` (`matchedRoot`).
* **Sign transport** (`eval_map_matchedRoot_pos`): if `q(α) > 0` then `(q^f)(β) > 0`. This is
  the heart: adjoin to `E` (inside `R`) all roots of `p`, square roots of all their differences,
  and a square root of `q(α)`; the resulting finite extension `M` admits *some* `E`-embedding
  `h` into `R'` (primitive element + root-count transfer). The adjoined square roots of
  differences force `h` to enumerate the roots of `p^f` in increasing order — pinning
  `h(α) = β` — and the square root of `q(α)` forces `(q^f)(β) = h(q(α))` to be positive.
  The embedding `h` is a *throwaway*: it transports these finitely many facts and is discarded.
* Consequently the lift extending `f` by `α ↦ β` is monotone, contradicting maximality; so the
  maximal lift is defined on all of `R` (`nonempty_algHom_of_orderCompat`).

Combining with the rigidity half (`algEquivOfRealClosures`) yields the **uniqueness of real
closures** (`realClosureAlgEquiv`): two real closed algebraic extensions of `F` inducing the same
order on `F` are `F`-isomorphic (and the isomorphism is automatically an order isomorphism, by
`Sturm.strictMono_map`).
-/

open Polynomial IntermediateField

namespace Hilbert17Blueprint

section RealClosureExists

variable {F R R' : Type*} [Field F]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
  [Algebra F R] [Algebra F R']

/-- An intermediate field of an ordered field is an ordered field. -/
local instance {K L : Type*} [Field K] [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [Algebra K L] (E : IntermediateField K L) : IsStrictOrderedRing E :=
  E.toSubfield.toIsStrictOrderedRing

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Every element of `R` is integral over every intermediate field. -/
theorem isIntegral_intermediateField [Algebra.IsAlgebraic F R] (E : IntermediateField F R)
    (x : R) : IsIntegral (↥E) x :=
  ((Algebra.IsAlgebraic.tower_top (K := F) (↥E)).isIntegral).1 x

/-- A square root of a nonnegative element of the real closed field `R` (junk value `0` on
negatives). -/
noncomputable def sqrtOf (x : R) : R :=
  if h : 0 ≤ x then (IsSquare.of_nonneg h).choose else 0

theorem sqrtOf_mul_self {x : R} (hx : 0 ≤ x) : sqrtOf x * sqrtOf x = x := by
  rw [sqrtOf, dif_pos hx]
  exact (IsSquare.of_nonneg hx).choose_spec.symm

theorem sqrtOf_ne_zero {x : R} (hx : 0 < x) : sqrtOf x ≠ 0 := by
  intro h0
  have := sqrtOf_mul_self hx.le
  rw [h0, mul_zero] at this
  exact hx.ne this

section Matching

variable {E : IntermediateField F R}

/-- **Root-count transfer over an intermediate field**: a polynomial over `E ⊆ R` has the same
number of roots in `R` as in `R'`, along any monotone `F`-algebra map `E → R'`. This is
`Sturm.card_roots_map_congr` for the ordered base field `E`. -/
theorem card_roots_map_lift_congr (f : ↥E →ₐ[F] R') (hf : Monotone f) (p : (↥E)[X]) :
    (p.map (algebraMap (↥E) R)).roots.toFinset.card
      = (p.map (f : ↥E →+* R')).roots.toFinset.card :=
  Sturm.card_roots_map_congr (φ := algebraMap (↥E) R) (φ' := (f : ↥E →+* R'))
    (fun _ _ h => h) (hf.strictMono_of_injective f.injective) p

variable (E) in
/-- The roots in `R` of the minimal polynomial of `α` over the intermediate field `E`. -/
noncomputable def rootsIn (α : R) : Finset R :=
  ((minpoly (↥E) α).map (algebraMap (↥E) R)).roots.toFinset

/-- The roots in `R'` of the image under `f` of the minimal polynomial of `α` over `E`. -/
noncomputable def rootsIn' (f : ↥E →ₐ[F] R') (α : R) : Finset R' :=
  ((minpoly (↥E) α).map (f : ↥E →+* R')).roots.toFinset

theorem card_rootsIn' (f : ↥E →ₐ[F] R') (hf : Monotone f) (α : R) :
    (rootsIn' f α).card = (rootsIn E α).card :=
  (card_roots_map_lift_congr f hf (minpoly (↥E) α)).symm

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem mem_rootsIn_self {α : R} (hint : IsIntegral (↥E) α) : α ∈ rootsIn E α := by
  rw [rootsIn, Multiset.mem_toFinset, Polynomial.mem_roots']
  refine ⟨(Polynomial.map_ne_zero_iff (algebraMap (↥E) R).injective).mpr
    (minpoly.ne_zero hint), ?_⟩
  rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
  exact minpoly.aeval (↥E) α

/-- The root of `(minpoly E α)^f` in `R'` matched to `α`: if `α` is the `k`-th root of its
minimal polynomial in `R`, this is the `k`-th root of the image polynomial in `R'`. -/
noncomputable def matchedRoot (f : ↥E →ₐ[F] R') (hf : Monotone f) {α : R}
    (hint : IsIntegral (↥E) α) : R' :=
  (rootsIn' f α).orderEmbOfFin (card_rootsIn' f hf α)
    (((rootsIn E α).orderIsoOfFin rfl).symm ⟨α, mem_rootsIn_self hint⟩)

theorem matchedRoot_mem (f : ↥E →ₐ[F] R') (hf : Monotone f) {α : R}
    (hint : IsIntegral (↥E) α) : matchedRoot f hf hint ∈ rootsIn' f α :=
  Finset.orderEmbOfFin_mem _ _ _

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Evaluating a polynomial over `E` at an element of an intermediate extension `M ⊆ R`,
seen in `R`. -/
theorem val_aeval (M : IntermediateField (↥E) R) (m : ↥M) (p : (↥E)[X]) :
    (Polynomial.aeval m p : R) = (p.map (algebraMap (↥E) R)).eval (m : R) := by
  have h1 : Polynomial.aeval (M.val m) p = M.val (Polynomial.aeval m p) :=
    Polynomial.aeval_algHom_apply M.val m p
  rw [show ((Polynomial.aeval m p : ↥M) : R) = M.val (Polynomial.aeval m p) from rfl, ← h1,
    Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rfl

/-- **Extension of a monotone lift to a finite-dimensional subextension** (as a ring
homomorphism). Uses the primitive element theorem and the root-count transfer; the resulting
embedding is *not* claimed to be monotone. -/
theorem exists_ringHom_extension [Algebra.IsAlgebraic F R] (f : ↥E →ₐ[F] R') (hf : Monotone f)
    (M : IntermediateField (↥E) R) [FiniteDimensional (↥E) ↥M] :
    ∃ h : ↥M →+* R', ∀ x : ↥E, h (algebraMap (↥E) ↥M x) = f x := by
  letI : Algebra (↥E) R' := (f : ↥E →+* R').toAlgebra
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (↥E) ↥M
  have hθint : IsIntegral (↥E) θ := IsIntegral.of_finite (↥E) θ
  -- the minimal polynomial of `θ` has a root in `R`, namely `θ` itself
  have hmin : minpoly (↥E) (M.val θ) = minpoly (↥E) θ :=
    minpoly.algHom_eq M.val (fun _ _ h => Subtype.ext_iff.mpr h) θ
  have hne : (minpoly (↥E) θ).map (algebraMap (↥E) R) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (↥E) R).injective).mpr (minpoly.ne_zero hθint)
  have hcard : 0 < ((minpoly (↥E) θ).map (algebraMap (↥E) R)).roots.toFinset.card := by
    rw [Finset.card_pos]
    refine ⟨M.val θ, Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hne, ?_⟩)⟩
    rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, ← hmin]
    exact minpoly.aeval (↥E) (M.val θ)
  -- transfer: it has a root `β` in `R'`
  rw [card_roots_map_lift_congr f hf] at hcard
  obtain ⟨β, hβ⟩ := Finset.card_pos.mp hcard
  have hβroot : β ∈ (minpoly (↥E) θ).aroots R' := by
    rw [Polynomial.aroots_def]
    exact Multiset.mem_toFinset.mp hβ
  -- assemble the `E`-algebra homomorphism `M → R'`
  let g : (↥E)⟮θ⟯ →ₐ[↥E] R' :=
    (IntermediateField.algHomAdjoinIntegralEquiv (↥E) hθint).symm ⟨β, hβroot⟩
  let e : ↥M ≃ₐ[↥E] ↥(↥E)⟮θ⟯ :=
    ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv).symm
  refine ⟨(g.comp e.toAlgHom : ↥M →ₐ[↥E] R').toRingHom, fun x => ?_⟩
  have := (g.comp e.toAlgHom).commutes x
  simp only [RingHom.algebraMap_toAlgebra] at this
  exact this

/-- **Sign transport to the matched root** — the heart of the uniqueness of real closures.
If `q(α) > 0` in `R`, then `q^f(β) > 0` in `R'`, where `β` is the matched root of `α`.

Proof: inside `R`, adjoin to `E` all roots of `p = minpoly E α`, square roots of all their
pairwise differences, and a square root of `q(α)`. This finite extension `M` admits an
`E`-embedding `h` into `R'` (`exists_ringHom_extension`). Since differences of roots are squares
in `M`, `h` enumerates the roots of `p^f` in increasing order, hence sends the `k`-th root `α`
to the `k`-th root `β`; since `q(α)` is a square in `M`, `h(q(α)) = q^f(β)` is a nonzero
square. -/
theorem eval_map_matchedRoot_pos [Algebra.IsAlgebraic F R] (f : ↥E →ₐ[F] R') (hf : Monotone f)
    {α : R} (hint : IsIntegral (↥E) α) {q : (↥E)[X]}
    (hq : 0 < (q.map (algebraMap (↥E) R)).eval α) :
    0 < (q.map (f : ↥E →+* R')).eval (matchedRoot f hf hint) := by
  classical
  set T : Finset R := rootsIn E α with hT
  set T' : Finset R' := rootsIn' f α with hT'
  set ξ : R := (q.map (algebraMap (↥E) R)).eval α with hξ
  -- the finite set to adjoin: roots, square roots of differences, square root of `ξ`
  set S : Finset R := (T ∪ Finset.image₂ (fun a b => sqrtOf (b - a)) T T) ∪ {sqrtOf ξ} with hS
  set M : IntermediateField (↥E) R := IntermediateField.adjoin (↥E) (S : Set R) with hM
  haveI : FiniteDimensional (↥E) ↥M :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => isIntegral_intermediateField E x)
  obtain ⟨h, hcompat⟩ := exists_ringHom_extension f hf M
  -- memberships in `M`
  have hTmem : ∀ a ∈ T, a ∈ M := fun a ha =>
    IntermediateField.subset_adjoin _ _ (by simp [hS, ha])
  have hDmem : ∀ a ∈ T, ∀ b ∈ T, sqrtOf (b - a) ∈ M := fun a ha b hb =>
    IntermediateField.subset_adjoin _ _
      (by simp only [hS, Finset.coe_union, Set.mem_union]
          exact Or.inl (Or.inr (Finset.mem_coe.mpr
            (Finset.mem_image₂.mpr ⟨a, ha, b, hb, rfl⟩))))
  have hξsqrtmem : sqrtOf ξ ∈ M :=
    IntermediateField.subset_adjoin _ _ (by simp [hS])
  -- pushing evaluations through `h`
  have hmapf : (f : ↥E →+* R') = h.comp (algebraMap (↥E) ↥M) :=
    RingHom.ext fun x => (hcompat x).symm
  have keyEval : ∀ (p : (↥E)[X]) (m : ↥M),
      (p.map (f : ↥E →+* R')).eval (h m) = h (Polynomial.aeval m p) := by
    intro p m
    rw [hmapf, ← Polynomial.map_map, Sturm.eval_map_apply h _ m]
    congr 1
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  -- `h` sends roots of `p` in `R` (inside `M`) to roots of `p^f` in `R'`
  have hroot' : ∀ a (ha : a ∈ T), h ⟨a, hTmem a ha⟩ ∈ T' := by
    intro a ha
    have haR : ((minpoly (↥E) α).map (algebraMap (↥E) R)).eval a = 0 := by
      have ha' : a ∈ rootsIn E α := by rw [← hT]; exact ha
      rw [rootsIn, Multiset.mem_toFinset, Polynomial.mem_roots'] at ha'
      exact ha'.2
    have haM : Polynomial.aeval (⟨a, hTmem a ha⟩ : ↥M) (minpoly (↥E) α) = 0 := by
      have := val_aeval M ⟨a, hTmem a ha⟩ (minpoly (↥E) α)
      exact Subtype.ext (by rw [this]; exact haR)
    have hne' : (minpoly (↥E) α).map (f : ↥E →+* R') ≠ 0 :=
      (Polynomial.map_ne_zero_iff (f : ↥E →+* R').injective).mpr
        (minpoly.ne_zero hint)
    rw [hT', rootsIn', Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hne', ?_⟩
    rw [Polynomial.IsRoot, keyEval, haM, map_zero]
  -- the adjoined square roots force `h` to be increasing on the roots
  have hInc : ∀ a (ha : a ∈ T), ∀ b (hb : b ∈ T), a < b →
      h ⟨a, hTmem a ha⟩ < h ⟨b, hTmem b hb⟩ := by
    intro a ha b hb hab
    have hsq : sqrtOf (b - a) * sqrtOf (b - a) = b - a :=
      sqrtOf_mul_self (by linarith)
    have hne0 : sqrtOf (b - a) ≠ 0 := sqrtOf_ne_zero (by linarith)
    have hsub : (⟨b, hTmem b hb⟩ - ⟨a, hTmem a ha⟩ : ↥M)
        = ⟨sqrtOf (b - a), hDmem a ha b hb⟩ * ⟨sqrtOf (b - a), hDmem a ha b hb⟩ :=
      Subtype.ext (by push_cast; rw [hsq])
    have hpos : 0 < h ⟨b, hTmem b hb⟩ - h ⟨a, hTmem a ha⟩ := by
      rw [← map_sub, hsub, map_mul]
      exact mul_self_pos.mpr fun h0 => hne0 (Subtype.ext_iff.mp (h.injective
        (h0.trans (map_zero h).symm)) : _)
    linarith
  -- pinning: `h` realizes the order-preserving enumeration of `T'`
  have hcard' : T'.card = T.card := card_rootsIn' f hf α
  set A := T.orderIsoOfFin rfl with hA
  have hpin : (fun i => h ⟨(A i : R), hTmem _ (A i).2⟩) = ⇑(T'.orderEmbOfFin hcard') := by
    apply Finset.orderEmbOfFin_unique
    · intro i; exact hroot' _ (A i).2
    · intro i j hij
      exact hInc _ (A i).2 _ (A j).2 (Subtype.coe_lt_coe.mpr (A.strictMono hij))
  -- hence `h(α) = matchedRoot`
  have hαT : α ∈ T := by rw [hT]; exact mem_rootsIn_self hint
  set k : Fin T.card := A.symm ⟨α, hαT⟩ with hk
  have hAk : ((A k : ↥T) : R) = α := by rw [hk, A.apply_symm_apply]
  have hhα : h ⟨α, hTmem α hαT⟩ = matchedRoot f hf hint := by
    have := congrFun hpin k
    rw [show (⟨(A k : R), hTmem _ (A k).2⟩ : ↥M) = ⟨α, hTmem α hαT⟩ from
      Subtype.ext hAk] at this
    rw [this]
    rfl
  -- sign transport through the adjoined square root of `ξ`
  have hαM : α ∈ M := hTmem α hαT
  have hδsq : sqrtOf ξ * sqrtOf ξ = ξ := sqrtOf_mul_self hq.le
  have hδne : sqrtOf ξ ≠ 0 := sqrtOf_ne_zero hq
  have hqval : Polynomial.aeval (⟨α, hαM⟩ : ↥M) q
      = ⟨sqrtOf ξ, hξsqrtmem⟩ * ⟨sqrtOf ξ, hξsqrtmem⟩ := by
    refine Subtype.ext ?_
    rw [val_aeval M ⟨α, hαM⟩ q]
    push_cast
    rw [hδsq]
  have : 0 < h (Polynomial.aeval (⟨α, hαM⟩ : ↥M) q) := by
    rw [hqval, map_mul]
    exact mul_self_pos.mpr fun h0 => hδne (Subtype.ext_iff.mp (h.injective
      (h0.trans (map_zero h).symm)) : _)
  rw [← keyEval q ⟨α, hαM⟩, hhα] at this
  exact this

end Matching

section ZornStep

variable [Algebra.IsAlgebraic F R]

/-- **The extension step**: a monotone lift that is not everywhere defined extends strictly,
staying monotone. The new value at `α` is `matchedRoot`, and monotonicity is
`eval_map_matchedRoot_pos`. -/
theorem exists_monotone_lift_gt (L : Lifts F R R') (hmono : Monotone L.emb)
    (hne : L.carrier ≠ ⊤) :
    ∃ L' : Lifts F R R', L < L' ∧ Monotone L'.emb := by
  obtain ⟨α, -, hαE⟩ := SetLike.exists_of_lt (hne.lt_top : L.carrier < ⊤)
  set E := L.carrier with hE
  set f := L.emb with hf
  have hint : IsIntegral (↥E) α := isIntegral_intermediateField E α
  letI : Algebra (↥E) R' := (f : ↥E →+* R').toAlgebra
  haveI : IsScalarTower F (↥E) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hβmem : matchedRoot f hmono hint ∈ (minpoly (↥E) α).aroots R' := by
    rw [Polynomial.aroots_def]
    exact Multiset.mem_toFinset.mp (matchedRoot_mem f hmono hint)
  set σ : ↥(↥E)⟮α⟯ →ₐ[↥E] R' :=
    (IntermediateField.algHomAdjoinIntegralEquiv (↥E) hint).symm
      ⟨matchedRoot f hmono hint, hβmem⟩ with hσ
  have hσgen : σ (IntermediateField.AdjoinSimple.gen (↥E) α) = matchedRoot f hmono hint :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen (↥E) hint _
  -- strict monotonicity of the extension
  have hσmono : StrictMono σ := by
    intro x y hxy
    have hpos : (0 : ↥(↥E)⟮α⟯) < y - x := sub_pos.mpr hxy
    obtain ⟨q, hq⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval' (y - x)
    rw [IntermediateField.adjoin.powerBasis_gen] at hq
    have hposR : (0 : R) < ((y - x : ↥(↥E)⟮α⟯) : R) := hpos
    have hval : (((y - x) : ↥(↥E)⟮α⟯) : R) = (q.map (algebraMap (↥E) R)).eval α := by
      rw [hq, val_aeval ((↥E)⟮α⟯) _ q]
      congr 1
    have h3 : 0 < (q.map (f : ↥E →+* R')).eval (matchedRoot f hmono hint) :=
      eval_map_matchedRoot_pos f hmono hint (by rw [← hval]; exact hposR)
    have hσval : σ (y - x) = (q.map (f : ↥E →+* R')).eval (matchedRoot f hmono hint) := by
      rw [hq, ← Polynomial.aeval_algHom_apply σ _ q, hσgen,
        Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      rfl
    have := hσval ▸ h3
    rw [map_sub] at this
    linarith
  -- package the new lift
  refine ⟨⟨((↥E)⟮α⟯).restrictScalars F, σ.restrictScalars F⟩, Lifts.lt_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · show E < ((↥E)⟮α⟯).restrictScalars F
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, left_lt_sup,
      IntermediateField.adjoin_simple_le_iff]
    exact hαE
  · exact AlgHom.coe_ringHom_injective σ.comp_algebraMap
  · exact fun x y hxy => (hσmono.monotone hxy : _)

/-- **Existence of an `F`-algebra homomorphism between real closed algebraic extensions.**
`R` is real closed and algebraic over `F`; `R'` is real closed; the two embeddings of `F`
induce the same order relation on `F`. Then there is an `F`-algebra homomorphism `R → R'`
(automatically an order embedding, by `Sturm.strictMono_map`). -/
theorem nonempty_algHom_of_orderCompat
    (hcompat : ∀ u v : F, algebraMap F R u ≤ algebraMap F R v →
      algebraMap F R' u ≤ algebraMap F R' v) :
    Nonempty (R →ₐ[F] R') := by
  classical
  -- the poset of monotone lifts
  set S : Set (Lifts F R R') := {L | Monotone L.emb} with hSdef
  -- the bottom lift is monotone
  have hbot : (⊥ : Lifts F R R') ∈ S := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := (IntermediateField.botEquiv F R).symm.surjective x
    obtain ⟨v, rfl⟩ := (IntermediateField.botEquiv F R).symm.surjective y
    have ex : ∀ w : F, (⊥ : Lifts F R R').emb ((IntermediateField.botEquiv F R).symm w)
        = algebraMap F R' w := by
      intro w
      show ((Algebra.ofId F R').comp (IntermediateField.botEquiv F R).toAlgHom) _ = _
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      rfl
    have cu : ∀ w : F, (((IntermediateField.botEquiv F R).symm w : ↥(⊥ : IntermediateField F R))
        : R) = algebraMap F R w := by
      intro w
      rw [IntermediateField.botEquiv_symm]
      rfl
    rw [ex u, ex v]
    refine hcompat u v ?_
    rw [← cu u, ← cu v]
    exact hxy
  -- chains of monotone lifts have monotone upper bounds
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, hbot, by simp⟩
    haveI : Nonempty c := hne.to_subtype
    refine ⟨Lifts.union c hc, ?_, fun z hz => Lifts.le_union c hc hz⟩
    intro x y hxy
    -- both coordinates live in a single member of the chain
    have hdir : Directed (· ≤ ·) (fun i : c => i.1.carrier) :=
      (hc.directedOn.directed_val).mono_comp _ fun _ _ h => h.1
    have hcoe : (↑((Lifts.union c hc).carrier) : Set R)
        = ⋃ i : c, ↑(i.1.carrier) := by
      rw [Lifts.carrier_union]
      exact IntermediateField.coe_iSup_of_directed hdir
    have hx : (x : R) ∈ ⋃ i : c, (↑(i.1.carrier) : Set R) := hcoe ▸ x.2
    have hy : (y : R) ∈ ⋃ i : c, (↑(i.1.carrier) : Set R) := hcoe ▸ y.2
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    obtain ⟨m, him, hjm⟩ := hdir i j
    have hxm : (x : R) ∈ m.1.carrier := him hxi
    have hym : (y : R) ∈ m.1.carrier := hjm hyj
    have hkey : ∀ (z : ↥(Lifts.union c hc).carrier) (hz : (z : R) ∈ m.1.carrier),
        (Lifts.union c hc).emb z = m.1.emb ⟨z, hz⟩ := by
      intro z hz
      have := (Lifts.le_union c hc m.2).2 ⟨(z : R), hz⟩
      rw [← this]
      exact congrArg _ (Subtype.ext rfl)
    rw [hkey x hxm, hkey y hym]
    exact hcS m.2 (show (⟨(x : R), hxm⟩ : ↥m.1.carrier) ≤ ⟨(y : R), hym⟩ from hxy)
  obtain ⟨M, hM⟩ := zorn_le₀ S hchain
  -- the maximal monotone lift is defined on all of `R`
  by_cases htop : M.carrier = ⊤
  · exact ⟨M.emb.comp (((IntermediateField.equivOfEq htop).trans
      IntermediateField.topEquiv).symm : R ≃ₐ[F] ↥M.carrier)⟩
  · obtain ⟨L', hlt, hmono'⟩ := exists_monotone_lift_gt M hM.1 htop
    exact absurd (hM.2 hmono' hlt.le) hlt.not_ge

/-- **Uniqueness of real closures**: two real closed algebraic extensions of `F` that induce the
same order relation on `F` are `F`-isomorphic. The isomorphism is automatically an order
isomorphism: ring homomorphisms out of real closed fields are strictly monotone
(`Sturm.strictMono_map`). -/
noncomputable def realClosureAlgEquiv [Algebra.IsAlgebraic F R']
    (hcompat : ∀ u v : F, algebraMap F R u ≤ algebraMap F R v →
      algebraMap F R' u ≤ algebraMap F R' v) :
    R ≃ₐ[F] R' :=
  algEquivOfRealClosures (Classical.choice (nonempty_algHom_of_orderCompat hcompat))

end ZornStep

end RealClosureExists

section RelativeClosure

/-! ### The relative algebraic closure in a real closed field is real closed

Together with `realClosureAlgEquiv`, this gives existence *and* uniqueness of the real closure
of a subfield of a real closed field, inside that field — the form needed to compare two models
of RCF over a common substructure. Note that `IsRealClosed` is an order-free predicate, so no
order hypotheses appear. -/

variable {K L : Type*} [Field K] [Field L] [IsRealClosed L] [Algebra K L]

/-- Sums of squares map to sums of squares under any ring homomorphism. -/
theorem isSumSq_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {s : A}
    (hs : IsSumSq s) : IsSumSq (f s) := by
  induction hs with
  | zero => rw [map_zero]; exact IsSumSq.zero
  | sq_add a hs ih => rw [map_add, map_mul]; exact IsSumSq.sq_add _ ih

open Field in
/-- **The relative algebraic closure of `K` in a real closed field `L` is real closed.**
Squares, square roots and roots of odd-degree polynomials taken in `L` are algebraic over the
closure, hence over `K`, hence already in the closure. -/
theorem isRealClosed_algebraicClosure : IsRealClosed ↥(algebraicClosure K L) := by
  haveI : Algebra.IsIntegral K ↥(algebraicClosure K L) :=
    ⟨fun x => (isIntegral_algebraMap_iff
      (algebraMap ↥(algebraicClosure K L) L).injective).mp
        (mem_algebraicClosure_iff'.mp x.2)⟩
  -- elements of `L` integral over the closure lie in the closure
  have hmem : ∀ z : L, IsIntegral ↥(algebraicClosure K L) z → z ∈ algebraicClosure K L :=
    fun z hz => mem_algebraicClosure_iff'.mpr (isIntegral_trans z hz)
  -- square roots taken in `L` lie in the closure
  have hsqrt : ∀ (x : ↥(algebraicClosure K L)) (s : L), (x : L) = s * s →
      s ∈ algebraicClosure K L := by
    intro x s hxs
    refine hmem s ⟨Polynomial.X ^ 2 - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C x two_ne_zero, ?_⟩
    have hx' : (algebraMap ↥(algebraicClosure K L) L) x = s * s := hxs
    simp [Polynomial.eval₂_sub, sq, hx']
  refine { one_add_ne_zero := ?_, isSquare_or_isSquare_neg := ?_,
           exists_isRoot_of_odd_natDegree := ?_ }
  · -- semireality restricts along the inclusion
    intro s hs h0
    have hs' : IsSumSq ((s : L)) :=
      isSumSq_map ((algebraicClosure K L).val : ↥(algebraicClosure K L) →+* L) hs
    refine IsSemireal.one_add_ne_zero hs' ?_
    have h0' := congrArg ((algebraicClosure K L).val) h0
    simpa using h0'
  · -- `x` or `-x` is a square, with the square root caught by algebraicity
    intro x
    rcases IsRealClosed.isSquare_or_isSquare_neg ((x : L)) with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨⟨s, hsqrt x s hs⟩, Subtype.ext (by push_cast; exact hs)⟩
    · refine Or.inr ⟨⟨s, hsqrt (-x) s (by push_cast; exact hs)⟩,
        Subtype.ext (by push_cast; exact hs)⟩
  · -- roots of odd-degree polynomials, likewise
    intro f hf
    have hf0 : f ≠ 0 := fun h => by simp [h, Nat.odd_iff] at hf
    have hmap : Odd ((f.map (algebraMap ↥(algebraicClosure K L) L)).natDegree) := by
      rwa [Polynomial.natDegree_map]
    obtain ⟨z, hz⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hmap
    have hzmem : z ∈ algebraicClosure K L := hmem z (IsAlgebraic.isIntegral
      ⟨f, hf0, by rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]⟩)
    refine ⟨⟨z, hzmem⟩, Subtype.ext ?_⟩
    have hcomm := Sturm.eval_map_apply
      ((algebraMap ↥(algebraicClosure K L) L)) f (⟨z, hzmem⟩ : ↥(algebraicClosure K L))
    have hzz : (algebraMap ↥(algebraicClosure K L) L)
        (⟨z, hzmem⟩ : ↥(algebraicClosure K L)) = z := rfl
    rw [hzz] at hcomm
    show (algebraMap ↥(algebraicClosure K L) L) (Polynomial.eval (⟨z, hzmem⟩ :
        ↥(algebraicClosure K L)) f)
      = (algebraMap ↥(algebraicClosure K L) L) 0
    rw [← hcomm, map_zero]
    exact hz

end RelativeClosure

end Hilbert17Blueprint
