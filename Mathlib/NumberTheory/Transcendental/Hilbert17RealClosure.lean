/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17Spectral

/-!
# Real closure of an ordered field, I: a maximal formally real extension is real closed

Part of the real-closed-field input to Hilbert's 17th problem for matrices
(see `Mathlib.NumberTheory.Transcendental.Hilbert17`).

A maximal formally real intermediate field of an algebraic closure (`exists_maximal_isSemireal`, a
Zorn argument) is real closed (`isRealClosed_of_maximal`), giving a real closed field extension of
any formally real field (`exists_isRealClosed_extension`). The order refinement turning this into a
genuine real closure is in `Hilbert17RealClosureOrder`.
-/

namespace Hilbert17Blueprint

open Polynomial Matrix

universe u

/-! ### (E) Existence of a real closure of an ordered field -/

/-- A **real closure** of an ordered field `F`: a real closed field with an order-preserving
ring embedding `F ↪ R`. Bundled as a structure because the target carries its own
field/order/real-closed instances. -/
structure RealClosure (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- The underlying real closed field. -/
  carrier : Type u
  [field : Field carrier]
  [linearOrder : LinearOrder carrier]
  [isStrictOrderedRing : IsStrictOrderedRing carrier]
  [isRealClosed : IsRealClosed carrier]
  /-- The embedding of `F`. -/
  emb : F →+* carrier
  /-- The embedding is order-preserving. -/
  monotone_emb : Monotone emb

open Module in
/-- **Artin's lemma** (cornerstone of E, **proved**): adjoining a square root of a sum of squares to
a formally real field keeps it formally real. This is the key inductive step of E3 (it forbids a
proper formally real quadratic extension once every positive element is a square). -/
theorem isSemireal_adjoinRoot_sqrt {F : Type*} [Field F] [IsSemireal F] {a : F} (ha : IsSumSq a)
    (hirr : Irreducible (X ^ 2 - C a)) :
    IsSemireal (AdjoinRoot (X ^ 2 - C a)) := by
  haveI : Fact (Irreducible (X ^ 2 - C a)) := ⟨hirr⟩
  set K := AdjoinRoot (X ^ 2 - C a) with hK
  have hne : (X ^ 2 - C a) ≠ 0 := hirr.ne_zero
  set pb := AdjoinRoot.powerBasis hne with hpb
  have hdim : pb.dim = 2 := by rw [hpb, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  set b : Module.Basis (Fin 2) F K := pb.basis.reindex (finCongr hdim) with hb
  have hgen : pb.gen = AdjoinRoot.root (X ^ 2 - C a) := by simp [hpb, AdjoinRoot.powerBasis_gen]
  have hval0 : (((finCongr hdim).symm 0 : Fin pb.dim) : ℕ) = 0 := by simp
  have hval1 : (((finCongr hdim).symm 1 : Fin pb.dim) : ℕ) = 1 := by simp
  have hb0 : b 0 = 1 := by
    rw [hb, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, hval0, pow_zero]
  have hb1 : b 1 = AdjoinRoot.root (X ^ 2 - C a) := by
    rw [hb, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, hval1, pow_one, hgen]
  set re : K →ₗ[F] F := b.coord 0 with hre
  have hre1 : re 1 = 1 := by rw [hre, ← hb0, Module.Basis.coord_apply, b.repr_self_apply]; simp
  have hre_root : re (AdjoinRoot.root (X ^ 2 - C a)) = 0 := by
    rw [hre, ← hb1, Module.Basis.coord_apply, b.repr_self_apply]; simp
  have hre_smul1 (x : F) : re (algebraMap F K x) = x := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hre1, smul_eq_mul, mul_one]
  have hroot2 : (AdjoinRoot.root (X ^ 2 - C a)) ^ 2 = algebraMap F K a := by
    have h : aeval (AdjoinRoot.root (X ^ 2 - C a)) (X ^ 2 - C a) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
    exact h
  have hdecomp (z : K) : z = algebraMap F K (re z) + algebraMap F K (b.coord 1 z)
      * AdjoinRoot.root (X ^ 2 - C a) := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two, hb0, hb1]
    rw [hre, Module.Basis.coord_apply, Module.Basis.coord_apply, Algebra.smul_def, Algebra.smul_def,
      mul_one]
  have hre_sq (z : K) : re (z ^ 2) = (re z) ^ 2 + a * (b.coord 1 z) ^ 2 := by
    set c := re z with hc
    set d := b.coord 1 z with hd
    have hz2 : z ^ 2 = algebraMap F K (c ^ 2 + a * d ^ 2)
        + algebraMap F K (2 * c * d) * AdjoinRoot.root (X ^ 2 - C a) := by
      rw [hdecomp z, ← hc, ← hd]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap F K d) ^ 2 * hroot2
    rw [hz2, map_add, hre_smul1,
      show algebraMap F K (2 * c * d) * AdjoinRoot.root (X ^ 2 - C a)
        = (2 * c * d) • AdjoinRoot.root (X ^ 2 - C a) from (Algebra.smul_def _ _).symm,
      map_smul, hre_root, smul_zero, add_zero]
  have hre_sq_sos (z : K) : IsSumSq (re (z ^ 2)) := by
    rw [hre_sq z]
    refine IsSumSq.add ?_ (ha.mul ?_)
    · rw [pow_two]; exact IsSumSq.mul_self _
    · rw [pow_two]; exact IsSumSq.mul_self _
  have hre_sos : ∀ s : K, IsSumSq s → IsSumSq (re s) := by
    intro s hs
    induction hs with
    | zero => simpa using IsSumSq.zero
    | sq_add x hs ih =>
        rw [map_add]
        refine IsSumSq.add ?_ ih
        rw [show x * x = x ^ 2 by ring]; exact hre_sq_sos x
  rw [isSemireal_iff_not_isSumSq_neg_one]
  intro h
  have hcontra : IsSumSq (re (-1 : K)) := hre_sos _ h
  rw [show (-1 : K) = algebraMap F K (-1) by simp, hre_smul1] at hcontra
  exact (isSemireal_iff_not_isSumSq_neg_one.mp ‹IsSemireal F›) hcontra

/-- **Odd-degree theorem, analytic crux** (proved). Over a formally real field, the leading
coefficient of a sum of squares of polynomials is itself a sum of squares (so it is nonzero unless
the polynomial is `0`), and the degree is even — there is no top-degree cancellation, by formal
reality. This is the engine of the Artin–Schreier odd-degree theorem (brick 2 of E): it forces the
cofactor `h` in `∑gᵢ² + 1 = p·h` to have odd degree, driving the induction. -/
theorem isSumSq_leadingCoeff_natDegree_even {F : Type*} [Field F] [IsSemireal F]
    {s : F[X]} (hs : IsSumSq s) : IsSumSq s.leadingCoeff ∧ Even s.natDegree := by
  induction hs with
  | zero => exact ⟨by simp [leadingCoeff], by simp⟩
  | sq_add g ht ih =>
      rename_i tt
      obtain ⟨iht, iht2⟩ := ih
      by_cases hg : g = 0
      · simpa [hg] using ⟨iht, iht2⟩
      by_cases htt : tt = 0
      · subst htt
        refine ⟨?_, ?_⟩
        · rw [add_zero, leadingCoeff_mul]; exact IsSumSq.mul_self _
        · rw [add_zero, natDegree_mul hg hg]; exact ⟨g.natDegree, by ring⟩
      have hlcgg : (g * g).leadingCoeff = g.leadingCoeff * g.leadingCoeff := leadingCoeff_mul g g
      have hgg_sos : IsSumSq (g * g).leadingCoeff := by rw [hlcgg]; exact IsSumSq.mul_self _
      have hggdeg : (g * g).natDegree = 2 * g.natDegree := by rw [natDegree_mul hg hg]; ring
      rcases lt_trichotomy (g * g).degree tt.degree with hlt | heq | hgt
      · refine ⟨?_, ?_⟩
        · rw [leadingCoeff_add_of_degree_lt hlt]; exact iht
        · rw [natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt hlt)]; exact iht2
      · have hsum_ne : (g * g).leadingCoeff + tt.leadingCoeff ≠ 0 := fun hsum =>
          (mul_ne_zero (leadingCoeff_ne_zero.2 hg) (leadingCoeff_ne_zero.2 hg))
            (hlcgg ▸ isSumSq_eq_zero_of_add hgg_sos iht hsum)
        refine ⟨?_, ?_⟩
        · rw [leadingCoeff_add_of_degree_eq heq hsum_ne]; exact hgg_sos.add iht
        · have hdeq : (g * g + tt).degree = (g * g).degree := by
            rw [degree_add_eq_of_leadingCoeff_add_ne_zero hsum_ne, ← heq, max_self]
          rw [natDegree_eq_of_degree_eq hdeq, hggdeg]; exact ⟨g.natDegree, by ring⟩
      · refine ⟨?_, ?_⟩
        · rw [leadingCoeff_add_of_degree_lt' hgt]; exact hgg_sos
        · rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hgt), hggdeg]
          exact ⟨g.natDegree, by ring⟩

/-- **Odd-degree brick 3a** (proved): a sum of squares lifts back along a surjective ring hom. Used
to turn `−1 = ∑βⱼ²` in the quotient `F[X]/(p)` into a polynomial sum-of-squares relation. -/
theorem exists_isSumSq_preimage {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ) {b : B} (hb : IsSumSq b) :
    ∃ a : A, IsSumSq a ∧ φ a = b := by
  induction hb with
  | zero => exact ⟨0, IsSumSq.zero, map_zero φ⟩
  | sq_add y _ ih =>
      obtain ⟨a', ha'sos, ha'eq⟩ := ih
      obtain ⟨x, hx⟩ := hφ y
      exact ⟨x * x + a', (IsSumSq.mul_self x).add ha'sos, by rw [map_add, map_mul, hx, ha'eq]⟩

/-- **Odd-degree brick 3b** (proved): a polynomial of odd degree over a field has an odd-degree
irreducible factor (some irreducible factor must carry the odd parity of the total degree). Used to
recurse in the Artin–Schreier odd-degree induction. -/
theorem exists_odd_monic_irreducible_factor {F : Type*} [Field F] :
    ∀ (n : ℕ) (h : F[X]), h.natDegree = n → Odd n →
      ∃ q : F[X], q.Monic ∧ Irreducible q ∧ Odd q.natDegree ∧ q ∣ h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn hodd
    rw [Nat.odd_iff] at hodd
    have hne : h ≠ 0 := by rintro rfl; rw [natDegree_zero] at hn; omega
    have hnu : ¬ IsUnit h := fun hu => by rw [natDegree_eq_zero_of_isUnit hu] at hn; omega
    obtain ⟨q₀, hq₀mon, hq₀irr, hq₀dvd⟩ := exists_monic_irreducible_factor h hnu
    rcases Nat.even_or_odd q₀.natDegree with hev | hod
    · rw [Nat.even_iff] at hev
      obtain ⟨c, hc⟩ := hq₀dvd
      have hc0 : c ≠ 0 := fun h0 => hne (by rw [hc, h0, mul_zero])
      rw [hc, natDegree_mul hq₀irr.ne_zero hc0] at hn
      have hq₀pos : 0 < q₀.natDegree := hq₀irr.natDegree_pos
      have hcodd : Odd c.natDegree := by rw [Nat.odd_iff]; omega
      obtain ⟨q, hqm, hqirr, hqodd, hqdvd⟩ := ih c.natDegree (by omega) c rfl hcodd
      exact ⟨q, hqm, hqirr, hqodd, hqdvd.trans (hc.symm ▸ dvd_mul_left c q₀)⟩
    · exact ⟨q₀, hq₀mon, hq₀irr, hod, hq₀dvd⟩

/-- Ring homomorphisms preserve sums of squares. -/
theorem isSumSq_ringHom_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {a : A}
    (ha : IsSumSq a) : IsSumSq (φ a) := by
  induction ha with
  | zero => simpa using IsSumSq.zero
  | sq_add y _ ih => rw [map_add, map_mul]; exact (IsSumSq.mul_self _).add ih

/-- A sum of squares in `F[X]/(p)` (`p` monic, positive degree) lifts to a sum of squares in `F[X]`
of degree `< 2·deg p`, by reducing each base mod `p`. -/
theorem exists_isSumSq_preimage_reduced {F : Type*} [Field F] {p : F[X]} (hp : p.Monic)
    (hp1 : 0 < p.natDegree) {b : AdjoinRoot p} (hb : IsSumSq b) :
    ∃ σ : F[X], IsSumSq σ ∧ AdjoinRoot.mk p σ = b ∧ σ.natDegree < 2 * p.natDegree := by
  have hpne1 : p ≠ 1 := fun h => by rw [h, natDegree_one] at hp1; omega
  induction hb with
  | zero => exact ⟨0, IsSumSq.zero, map_zero _, by simpa using hp1⟩
  | sq_add y _ ih =>
      obtain ⟨σ', hσ'sos, hσ'eq, hσ'deg⟩ := ih
      obtain ⟨x, hx⟩ := AdjoinRoot.mk_surjective y
      have hmkr : AdjoinRoot.mk p (x %ₘ p) = y := by
        rw [show AdjoinRoot.mk p (x %ₘ p) = AdjoinRoot.mk p x from AdjoinRoot.mk_eq_mk.2
          ⟨-(x /ₘ p), by rw [modByMonic_eq_sub_mul_div x p]; ring⟩, hx]
      have hrdeg : (x %ₘ p).natDegree < p.natDegree := natDegree_modByMonic_lt x hp hpne1
      refine ⟨(x %ₘ p) * (x %ₘ p) + σ', (IsSumSq.mul_self (x %ₘ p)).add hσ'sos, ?_, ?_⟩
      · rw [map_add, map_mul, hmkr, hσ'eq]
      · have h1 : ((x %ₘ p) * (x %ₘ p)).natDegree < 2 * p.natDegree :=
          lt_of_le_of_lt natDegree_mul_le (by omega)
        exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt h1 hσ'deg)

/-- **Odd-degree theorem (Artin–Schreier), brick 2 of E — fully proved.** A monic irreducible
polynomial of odd degree over a formally real field generates a formally real extension. Strong
induction on the degree: from `−1 = ∑βⱼ²` in `F[X]/(p)`, lift to a *reduced* relation
`∑gᵢ²+1 = p·h` (`isSumSq_preimage_reduced`); `isSumSq_leadingCoeff_natDegree_even` forces `deg h`
odd; `exists_odd_monic_irreducible_factor` pulls a monic odd irreducible factor `q` of `h` of
smaller degree; the induction makes `F[X]/(q)` formally real; but `q ∣ σ+1` gives `−1 = ∑gᵢ²` in
`F[X]/(q)` — contradiction. -/
theorem isSemireal_adjoinRoot_odd {F : Type*} [Field F] [IsSemireal F] :
    ∀ (n : ℕ) (p : F[X]), p.Monic → p.natDegree = n → Odd n → Irreducible p →
      IsSemireal (AdjoinRoot p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hpm hn hodd hpirr
    have hn1 : 0 < p.natDegree := by rw [hn]; rcases hodd with ⟨m, _⟩; omega
    rw [isSemireal_iff_not_isSumSq_neg_one]
    intro hsos
    obtain ⟨σ, hσsos, hσeq, hσdeg⟩ := exists_isSumSq_preimage_reduced hpm hn1 hsos
    obtain ⟨hσlc, hσeven⟩ := isSumSq_leadingCoeff_natDegree_even hσsos
    have hpdvd : p ∣ σ + 1 := by
      rw [← AdjoinRoot.mk_eq_zero, map_add, hσeq, map_one]; ring
    obtain ⟨h, hh⟩ := hpdvd
    have hhne : h ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hh
      have hσ1 : σ = -1 := eq_neg_of_add_eq_zero_left hh
      exact IsSemireal.not_isSumSq_neg_one F (by simpa [hσ1] using hσlc)
    have hdeg_eq : σ.natDegree = n + h.natDegree := by
      conv_lhs => rw [← natDegree_add_C (p := σ) (a := 1), C_1, hh]
      rw [natDegree_mul hpirr.ne_zero hhne, hn]
    have hhdeg_lt : h.natDegree < n := by omega
    have hhodd : Odd h.natDegree := by
      rcases hσeven with ⟨k, hk⟩; rcases hodd with ⟨m, hm⟩; rw [Nat.odd_iff]; omega
    obtain ⟨q, hqm, hqirr, hqodd, hqdvd⟩ :=
      exists_odd_monic_irreducible_factor h.natDegree h rfl hhodd
    have hqdeglt : q.natDegree < n := lt_of_le_of_lt (natDegree_le_of_dvd hqdvd hhne) hhdeg_lt
    have hqsemi : IsSemireal (AdjoinRoot q) := ih q.natDegree hqdeglt q hqm rfl hqodd hqirr
    have hqdvdσ : q ∣ σ + 1 := hqdvd.trans (hh.symm ▸ dvd_mul_left h p)
    have hmkq : AdjoinRoot.mk q σ = -1 := by
      have h0 : AdjoinRoot.mk q (σ + 1) = 0 := AdjoinRoot.mk_eq_zero.2 hqdvdσ
      rw [map_add, map_one] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hcon : IsSumSq (-1 : AdjoinRoot q) := hmkq ▸ isSumSq_ringHom_map (AdjoinRoot.mk q) hσsos
    exact (isSemireal_iff_not_isSumSq_neg_one.mp hqsemi) hcon

/-! #### E3: a maximal formally real algebraic extension is real closed -/

section RealClosedOfMaximal
variable {R : Type*} [Field R] [IsSemireal R]
  (hmax : ∀ q : R[X], q.Monic → Irreducible q → 2 ≤ q.natDegree → ¬ IsSemireal (AdjoinRoot q))
include hmax

/-- **E3, odd-root condition** (proved). With no proper formally real simple algebraic extension,
every odd-degree polynomial has a root — its odd monic irreducible factor must be linear, else the
odd-degree theorem makes a proper formally real extension. -/
theorem exists_isRoot_of_odd_of_maximal {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  obtain ⟨q, hqm, hqirr, hqodd, hqdvd⟩ := exists_odd_monic_irreducible_factor f.natDegree f rfl hf
  have hq1 : q.natDegree = 1 := by
    by_contra hne
    have hq2 : 2 ≤ q.natDegree := by rcases hqodd with ⟨m, hm⟩; omega
    exact hmax q hqm hqirr hq2 (isSemireal_adjoinRoot_odd q.natDegree q hqm rfl hqodd hqirr)
  obtain ⟨c, hc⟩ := exists_root_of_degree_eq_one (p := q)
    (by rw [degree_eq_natDegree hqm.ne_zero, hq1]; rfl)
  exact ⟨c, hc.dvd hqdvd⟩

/-- **E3, sums of squares are squares** (proved). Else adjoining `√s` gives a proper formally real
extension, by Artin's lemma. -/
theorem isSquare_of_isSumSq_of_maximal {s : R} (hs : IsSumSq s) : IsSquare s := by
  by_contra hns
  have hirr : Irreducible (X ^ 2 - C s) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [natDegree_X_pow_sub_C]; decide
    · intro c hc
      rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
      exact hns ⟨c, by rw [← hc]; ring⟩
  exact hmax (X ^ 2 - C s) (monic_X_pow_sub_C s two_ne_zero) hirr
    (le_of_eq natDegree_X_pow_sub_C.symm) (isSemireal_adjoinRoot_sqrt hs hirr)

open Module in
/-- **E3, square condition** (proved). `x` or `-x` is a square: if `x` is not a square then
`R(√x)` is not formally real (maximality), so `-1 = A + x·B` for sums of squares `A`, `B` (extracted
via the "real part" functional); then `-x = (1+A)/B`, a quotient of squares, hence a square. -/
theorem isSquare_or_isSquare_neg_of_maximal (x : R) : IsSquare x ∨ IsSquare (-x) := by
  by_cases hx : IsSquare x
  · exact Or.inl hx
  refine Or.inr ?_
  have hirr : Irreducible (X ^ 2 - C x) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [natDegree_X_pow_sub_C]; decide
    · intro c hc
      rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
      exact hx ⟨c, by rw [← hc]; ring⟩
  haveI : Fact (Irreducible (X ^ 2 - C x)) := ⟨hirr⟩
  set K := AdjoinRoot (X ^ 2 - C x) with hK
  have hne : (X ^ 2 - C x) ≠ 0 := hirr.ne_zero
  set pb := AdjoinRoot.powerBasis hne with hpb
  have hdim : pb.dim = 2 := by rw [hpb, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  set b : Module.Basis (Fin 2) R K := pb.basis.reindex (finCongr hdim) with hb
  have hgen : pb.gen = AdjoinRoot.root (X ^ 2 - C x) := by simp [hpb, AdjoinRoot.powerBasis_gen]
  have hb0 : b 0 = 1 := by
    rw [hb, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
      show (((finCongr hdim).symm 0 : Fin pb.dim) : ℕ) = 0 by simp, pow_zero]
  have hb1 : b 1 = AdjoinRoot.root (X ^ 2 - C x) := by
    rw [hb, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
      show (((finCongr hdim).symm 1 : Fin pb.dim) : ℕ) = 1 by simp, pow_one, hgen]
  set re : K →ₗ[R] R := b.coord 0 with hre
  have hre1 : re 1 = 1 := by rw [hre, ← hb0, Module.Basis.coord_apply, b.repr_self_apply]; simp
  have hre_root : re (AdjoinRoot.root (X ^ 2 - C x)) = 0 := by
    rw [hre, ← hb1, Module.Basis.coord_apply, b.repr_self_apply]; simp
  have hre_smul1 (r : R) : re (algebraMap R K r) = r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hre1, smul_eq_mul, mul_one]
  have hroot2 : (AdjoinRoot.root (X ^ 2 - C x)) ^ 2 = algebraMap R K x := by
    have h : aeval (AdjoinRoot.root (X ^ 2 - C x)) (X ^ 2 - C x) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h; exact h
  have hdecomp (z : K) : z = algebraMap R K (re z) + algebraMap R K (b.coord 1 z)
      * AdjoinRoot.root (X ^ 2 - C x) := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two, hb0, hb1]
    rw [hre, Module.Basis.coord_apply, Module.Basis.coord_apply, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  have hre_sq (z : K) : re (z ^ 2) = (re z) ^ 2 + x * (b.coord 1 z) ^ 2 := by
    set c := re z with hc
    set d := b.coord 1 z with hd
    have hz2 : z ^ 2 = algebraMap R K (c ^ 2 + x * d ^ 2)
        + algebraMap R K (2 * c * d) * AdjoinRoot.root (X ^ 2 - C x) := by
      rw [hdecomp z, ← hc, ← hd]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap R K d) ^ 2 * hroot2
    rw [hz2, map_add, hre_smul1,
      show algebraMap R K (2 * c * d) * AdjoinRoot.root (X ^ 2 - C x)
        = (2 * c * d) • AdjoinRoot.root (X ^ 2 - C x) from (Algebra.smul_def _ _).symm,
      map_smul, hre_root, smul_zero, add_zero]
  have hre_decomp : ∀ s : K, IsSumSq s → ∃ A B : R, IsSumSq A ∧ IsSumSq B ∧ re s = A + x * B := by
    intro s hs
    induction hs with
    | zero => exact ⟨0, 0, IsSumSq.zero, IsSumSq.zero, by simp⟩
    | sq_add y _ ih =>
        obtain ⟨A', B', hA', hB', hre't⟩ := ih
        refine ⟨(re y) ^ 2 + A', (b.coord 1 y) ^ 2 + B', ?_, ?_, ?_⟩
        · rw [pow_two]; exact (IsSumSq.mul_self _).add hA'
        · rw [pow_two]; exact (IsSumSq.mul_self _).add hB'
        · rw [map_add, show y * y = y ^ 2 by ring, hre_sq y, hre't]; ring
  have hnsemi : ¬ IsSemireal K := hmax (X ^ 2 - C x) (monic_X_pow_sub_C x two_ne_zero) hirr
    (le_of_eq natDegree_X_pow_sub_C.symm)
  rw [isSemireal_iff_not_isSumSq_neg_one, not_not] at hnsemi
  obtain ⟨A, B, hA, hB, hABeq⟩ := hre_decomp _ hnsemi
  have hre_neg1 : re (-1 : K) = -1 := by
    rw [show (-1 : K) = algebraMap R K (-1) by simp, hre_smul1]
  rw [hre_neg1] at hABeq
  have hBne : B ≠ 0 := by
    rintro rfl
    rw [mul_zero, add_zero] at hABeq
    exact IsSemireal.not_isSumSq_neg_one R (hABeq ▸ hA)
  obtain ⟨u, hu⟩ := isSquare_of_isSumSq_of_maximal hmax (by simpa using IsSumSq.sq_add (1 : R) hA)
  obtain ⟨v, hv⟩ := isSquare_of_isSumSq_of_maximal hmax hB
  have hv0 : v ≠ 0 := fun h => hBne (by rw [hv, h, mul_zero])
  refine ⟨u / v, ?_⟩
  rw [div_mul_div_comm, ← hu, ← hv, eq_div_iff hBne]
  linear_combination hABeq

/-- **E3 assembly** (proved). A formally real field with no proper formally real simple algebraic
extension is real closed. -/
theorem isRealClosed_of_maximal : IsRealClosed R where
  isSquare_or_isSquare_neg := isSquare_or_isSquare_neg_of_maximal hmax
  exists_isRoot_of_odd_natDegree := fun hf => exists_isRoot_of_odd_of_maximal hmax hf

end RealClosedOfMaximal

/-! #### E2: a maximal formally real algebraic extension exists (Zorn) -/

section MaximalSemireal
open IntermediateField
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- A sum of squares in a directed supremum of intermediate fields descends to one member. -/
theorem isSumSq_iSup_descend {ι : Type*} [Nonempty ι] {E : ι → IntermediateField F Ω}
    (dir : Directed (· ≤ ·) E) {s : ↥(⨆ i, E i)} (hs : IsSumSq s) :
    ∃ i, ∃ t : ↥(E i), IsSumSq t ∧ inclusion (le_iSup E i) t = s := by
  induction hs with
  | zero => exact ⟨Classical.arbitrary ι, 0, IsSumSq.zero, map_zero _⟩
  | @sq_add y s' _ ih =>
      obtain ⟨k, t', ht'sos, ht'eq⟩ := ih
      obtain ⟨j, hyj⟩ : ∃ j, (y : Ω) ∈ E j := by
        have hy := y.2
        rwa [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed dir, Set.mem_iUnion] at hy
      obtain ⟨m, hjm, hkm⟩ := dir j k
      refine ⟨m, inclusion hjm ⟨(y : Ω), hyj⟩ * inclusion hjm ⟨(y : Ω), hyj⟩
        + inclusion hkm t', (IsSumSq.mul_self _).add
          (isSumSq_ringHom_map (inclusion hkm : ↥(E k) →+* ↥(E m)) ht'sos), ?_⟩
      apply Subtype.ext
      have hy' : ((inclusion (le_iSup E m) (inclusion hjm ⟨(y : Ω), hyj⟩) : ↥(⨆ i, E i)) : Ω)
          = (y : Ω) := by rw [inclusion_inclusion]; rfl
      have ht'' : ((inclusion (le_iSup E m) (inclusion hkm t') : ↥(⨆ i, E i)) : Ω) = (s' : Ω) := by
        rw [inclusion_inclusion]
        have := congrArg (Subtype.val) ht'eq
        rwa [coe_inclusion] at this
      push_cast [map_add, map_mul]
      rw [hy', ht'']

/-- **E2 chain condition.** A directed family of formally-real intermediate fields has a
formally-real supremum. -/
theorem isSemireal_iSup_of_directed {ι : Type*} [Nonempty ι] {E : ι → IntermediateField F Ω}
    (dir : Directed (· ≤ ·) E) (hE : ∀ i, IsSemireal ↥(E i)) : IsSemireal ↥(⨆ i, E i) := by
  rw [isSemireal_iff_not_isSumSq_neg_one]
  intro hsos
  obtain ⟨i, t, htsos, hteq⟩ := isSumSq_iSup_descend dir hsos
  have ht1 : t = -1 := inclusion_injective (le_iSup E i) (by rw [hteq, map_neg, map_one])
  rw [ht1] at htsos
  haveI := hE i
  exact IsSemireal.not_isSumSq_neg_one ↥(E i) htsos

/-- **E2: existence of a maximal formally-real intermediate field** (Zorn). -/
theorem exists_maximal_isSemireal [IsSemireal F] :
    ∃ R : IntermediateField F Ω, IsSemireal ↥R ∧
      ∀ E : IntermediateField F Ω, R ≤ E → IsSemireal ↥E → E = R := by
  have hbot : IsSemireal ↥(⊥ : IntermediateField F Ω) := by
    rw [isSemireal_iff_not_isSumSq_neg_one]
    intro h
    refine IsSemireal.not_isSumSq_neg_one F ?_
    have := isSumSq_ringHom_map (IntermediateField.botEquiv F Ω).toRingHom h
    rwa [map_neg, map_one] at this
  obtain ⟨R, hR⟩ := zorn_le₀ {E : IntermediateField F Ω | IsSemireal ↥E}
    (fun c hcS hchain => by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, hbot, by simp⟩
      · refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
        rw [Set.mem_setOf_eq, sSup_eq_iSup']
        haveI : Nonempty ↥c := hne.to_subtype
        exact isSemireal_iSup_of_directed
          (fun a b => (hchain.total a.2 b.2).elim
            (fun h => ⟨b, h, le_rfl⟩) (fun h => ⟨a, le_rfl, h⟩))
          (fun i => hcS i.2))
  exact ⟨R, hR.1, fun E hRE hE => le_antisymm (hR.2 hE hRE) hRE⟩

/-- **Connection lemma (E2 ⟹ the `hmax` of E3).** A *maximal* formally-real intermediate field `R`
of an algebraically closed extension `Ω ⊇ F` has no proper formally-real simple algebraic
extension: every monic irreducible `q` over `R` of degree `≥ 2` makes `AdjoinRoot q` non-formally-
real. Indeed a root `α ∈ Ω` of `q` would give a formally-real `R(α) ≅ AdjoinRoot q`; maximality
forces `R(α) = R`, so `α ∈ R` and `deg q = 1`, a contradiction. -/
theorem hmax_of_maximal [IsAlgClosed Ω] {R : IntermediateField F Ω}
    (hRmax : ∀ E : IntermediateField F Ω, R ≤ E → IsSemireal ↥E → E = R)
    (q : (↥R)[X]) (hqm : q.Monic) (hqirr : Irreducible q) (hq2 : 2 ≤ q.natDegree) :
    ¬ IsSemireal (AdjoinRoot q) := by
  intro hsemi
  haveI : Fact (Irreducible q) := ⟨hqirr⟩
  have hdeg0 : q.degree ≠ 0 := by
    rw [degree_eq_natDegree hqm.ne_zero]; exact_mod_cast (by omega : q.natDegree ≠ 0)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (k := Ω) q hdeg0
  have hint : IsIntegral (↥R) α := ⟨q, hqm, hα⟩
  have hminpoly : minpoly (↥R) α = q := (minpoly.eq_of_irreducible_of_monic hqirr hα hqm).symm
  set Rα : IntermediateField (↥R) Ω := IntermediateField.adjoin (↥R) {α} with hRα
  have hsemi' : IsSemireal ↥Rα := by
    rw [isSemireal_iff_not_isSumSq_neg_one]
    intro h
    refine (isSemireal_iff_not_isSumSq_neg_one.mp hsemi) ?_
    have e : AdjoinRoot q ≃ₐ[↥R] ↥Rα := hminpoly ▸ adjoinRootEquivAdjoin (↥R) hint
    have := isSumSq_ringHom_map e.symm.toRingHom h
    rwa [map_neg, map_one] at this
  set E : IntermediateField F Ω := Rα.restrictScalars F with hE
  have hRE : R ≤ E := fun x hx => by
    rw [hE, mem_restrictScalars]
    simpa using IntermediateField.algebraMap_mem Rα (⟨x, hx⟩ : ↥R)
  have hER : E = R := hRmax E hRE hsemi'
  have hαE : α ∈ E := by
    rw [hE, mem_restrictScalars]; exact IntermediateField.mem_adjoin_simple_self (↥R) α
  rw [hER] at hαE
  have hle : (minpoly (↥R) α).natDegree ≤ 1 := by
    have hdvd : minpoly (↥R) α ∣ (X - C (⟨α, hαE⟩ : ↥R)) :=
      minpoly.dvd (↥R) α (by rw [map_sub, aeval_X, aeval_C, sub_eq_zero]; rfl)
    have := natDegree_le_of_dvd hdvd (X_sub_C_ne_zero _)
    rwa [natDegree_X_sub_C] at this
  rw [hminpoly] at hle
  omega

end MaximalSemireal

/-- **Real closed extension exists** (E1+E2+E3 combined). Every formally real field `F` has a real
closed algebraic extension: the maximal formally-real intermediate field `R` of `AlgebraicClosure F`
(`exists_maximal_isSemireal`) is real closed (`isRealClosed_of_maximal`, whose `hmax` hypothesis is
supplied by `hmax_of_maximal`). This is the field-theoretic core of real-closure existence; the
remaining gap to `exists_realClosure` is purely the *order* refinement (E4). -/
theorem exists_isRealClosed_extension (F : Type*) [Field F] [IsSemireal F] :
    ∃ R : IntermediateField F (AlgebraicClosure F), IsRealClosed ↥R := by
  obtain ⟨R, hRsemi, hRmax⟩ := exists_maximal_isSemireal (F := F) (Ω := AlgebraicClosure F)
  haveI := hRsemi
  exact ⟨R, isRealClosed_of_maximal (hmax_of_maximal hRmax)⟩

end Hilbert17Blueprint
