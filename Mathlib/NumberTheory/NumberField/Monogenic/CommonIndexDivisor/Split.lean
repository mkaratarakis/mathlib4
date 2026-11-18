/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.CommonIndexDivisor

/-!
# The index of a number field at a prime that splits completely

If `p` splits completely in the number field `K`, that is `p 𝓞 K` is a product of `n = [K : ℚ]`
distinct primes, then `ν_p(i(K)) = ν_p(0! · 1! ⋯ (n - 1)!)`.  For every `θ ∈ 𝓞 K` the element
`θ (θ - 1) ⋯ (θ - k + 1)` is divisible by `p ^ ν_p(k!)` in `𝓞 K`, which forces this power of `p`
into `[𝓞 K : ℤ[θ]]`; an element congruent to `i` modulo a high power of the `i`-th prime above `p`
attains the bound.

Several lemmas only use that the primes above `p` are unramified and are stated in that generality;
they are used again in `Mathlib.NumberTheory.NumberField.Monogenic.CommonIndexDivisor.Unramified`.

## Main results

* `NumberField.index_eq_natAbs_det`: `[𝓞 K : ℤ[θ]]` is the absolute value of the determinant of
  `1, θ, …, θ ^ (n - 1)` in a basis of `𝓞 K`.
* `NumberField.pow_dvd_index_of_splitsCompletely`: the lower bound for every generator.
* `NumberField.exists_index_eq_pow_mul_of_splitsCompletely`: the bound is attained.
* `NumberField.factorization_fieldIndex_of_splitsCompletely`: `ν_p(i(K)) = ν_p(0! 1! ⋯ (n - 1)!)`.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section Split

variable {p : ℕ} [hp : Fact p.Prime]

omit [NumberField K] in
/-- The index of `ℤ[θ]` is the absolute value of the determinant of `1, θ, …, θ ^ (n - 1)` in any
basis of `𝓞 K`. -/
theorem index_eq_natAbs_det {θ : 𝓞 K} [NumberField K] (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (b : Module.Basis (Fin (Module.finrank ℚ K)) ℤ (𝓞 K)) :
    RingOfIntegers.index θ = (b.det fun k : Fin (Module.finrank ℚ K) ↦ θ ^ (k : ℕ)).natAbs := by
  set pb := Algebra.adjoin.powerBasis' θ.isIntegral
  have hdim : pb.dim = Module.finrank ℚ K := by
    rw [Algebra.adjoin.powerBasis'_dim, natDegree_minpoly_eq_finrank hθ]
  let bN : Module.Basis (Fin (Module.finrank ℚ K)) ℤ
      (Subalgebra.toSubmodule (Algebra.adjoin ℤ {θ})) :=
    (pb.basis.reindex (finCongr hdim)).map (Subalgebra.toSubmoduleEquiv _).symm
  have hbN : ((↑) ∘ bN : Fin (Module.finrank ℚ K) → 𝓞 K) =
      fun k : Fin (Module.finrank ℚ K) ↦ θ ^ (k : ℕ) := by
    funext k
    simp only [bN, Function.comp_apply, Module.Basis.map_apply, Module.Basis.reindex_apply]
    rw [PowerBasis.basis_eq_pow, Algebra.adjoin.powerBasis'_gen]
    rfl
  change Submodule.cardQuot (Subalgebra.toSubmodule (Algebra.adjoin ℤ {θ})) = _
  rw [Submodule.cardQuot_apply, ← Submodule.natAbs_det_basis_change b _ bN, hbN]

omit [NumberField K] in
/-- Replacing `θ ^ k` by `θ (θ - 1) ⋯ (θ - k + 1)` does not change the determinant: the change of
basis is unitriangular. -/
theorem det_pow_eq_det_descPochhammer {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (θ : 𝓞 K) :
    b.det (fun k : Fin n ↦ θ ^ (k : ℕ)) =
      b.det (fun k : Fin n ↦ aeval θ (descPochhammer ℤ (k : ℕ))) := by
  set U : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j k ↦ (descPochhammer ℤ (k : ℕ)).coeff j
  have hU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun k _ ↦ ?_
      have := (monic_descPochhammer ℤ (k : ℕ)).coeff_natDegree
      rwa [descPochhammer_natDegree] at this
    · intro i j hij
      exact coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact hij)
  have hmat : b.toMatrix (fun k : Fin n ↦ aeval θ (descPochhammer ℤ (k : ℕ))) =
      b.toMatrix (fun k : Fin n ↦ θ ^ (k : ℕ)) * U := by
    ext i k
    rw [Module.Basis.toMatrix_apply, Matrix.mul_apply,
      aeval_eq_sum_range' (n := n) (by rw [descPochhammer_natDegree]; exact k.2),
      ← Fin.sum_univ_eq_sum_range (fun j ↦ (descPochhammer ℤ (k : ℕ)).coeff j • θ ^ j), map_sum,
      Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.toMatrix_apply, mul_comm]
    rfl
  rw [Module.Basis.det_apply, Module.Basis.det_apply, hmat, Matrix.det_mul, hU, mul_one]

omit [NumberField K] in
/-- If `1, θ, …, θ ^ (n - 1)` have nonzero determinant in a basis of `𝓞 K`, then `θ`
generates `K`. -/
theorem adjoin_eq_top_of_det_ne_zero [NumberField K]
    (b : Module.Basis (Fin (Module.finrank ℚ K)) ℤ (𝓞 K)) {θ : 𝓞 K}
    (h : b.det (fun k : Fin (Module.finrank ℚ K) ↦ θ ^ (k : ℕ)) ≠ 0) :
    Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
  refine adjoin_eq_top_of_finrank_le_natDegree (not_lt.mp fun hlt ↦ h ?_)
  apply AlternatingMap.map_linearDependent
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun k ↦ (minpoly ℤ θ).coeff k, ?_, ⟨⟨_, hlt⟩, ?_⟩⟩
  · rw [Fin.sum_univ_eq_sum_range (fun k ↦ (minpoly ℤ θ).coeff k • θ ^ k),
      ← aeval_eq_sum_range' hlt, minpoly.aeval]
  · change (minpoly ℤ θ).coeff (minpoly ℤ θ).natDegree ≠ 0
    rw [(minpoly.monic θ.isIntegral).coeff_natDegree]
    exact one_ne_zero

omit hp in
theorem nonempty_basis_fin : Nonempty (Module.Basis (Fin (Module.finrank ℚ K)) ℤ (𝓞 K)) :=
  ⟨(RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]))⟩

omit [NumberField K] hp in
/-- If `θ (θ - 1) ⋯ (θ - k + 1) = p ^ ν_p(k!) β_k` for `k < n`, the determinant of
`1, θ, …, θ ^ (n - 1)` is `p ^ ν_p(0! ⋯ (n - 1)!)` times that of the `β_k`. -/
theorem det_pow_eq_pow_mul_det {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (θ : 𝓞 K)
    (β : Fin n → 𝓞 K)
    (hβ : ∀ k : Fin n, β k * (p : 𝓞 K) ^ (Nat.factorial (k : ℕ)).factorization p =
      aeval θ (descPochhammer ℤ (k : ℕ))) :
    b.det (fun k : Fin n ↦ θ ^ (k : ℕ)) =
      ((p ^ ∑ k ∈ Finset.range n, (Nat.factorial k).factorization p : ℕ) : ℤ) * b.det β := by
  rw [det_pow_eq_det_descPochhammer]
  have : (fun k : Fin n ↦ aeval θ (descPochhammer ℤ (k : ℕ))) =
      fun k : Fin n ↦ ((p : ℤ) ^ (Nat.factorial (k : ℕ)).factorization p) • β k := by
    funext k
    rw [← hβ k, zsmul_eq_mul]
    push_cast
    ring
  rw [this, AlternatingMap.map_smul_univ, smul_eq_mul, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun k ↦ (Nat.factorial k).factorization p)]
  push_cast
  rfl

variable (p) in
/-- `p` splits completely in `K`: there are `[K : ℚ]` primes of `𝓞 K` above `p`. -/
abbrev SplitsCompletely : Prop :=
  (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K

/-- If `p` splits completely, every prime above `p` is unramified of residue degree one. -/
theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one (hsplit : SplitsCompletely (K := K) p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
  classical
  have hsum := sum_ramificationIdx_mul_inertiaDeg (K := K) p
  rw [← hsplit, Set.ncard_eq_toFinset_card', Finset.card_eq_sum_ones] at hsum
  have hle : ∀ Q ∈ (primesOver (span {(p : ℤ)}) (𝓞 K)).toFinset,
      1 ≤ Q.ramificationIdx ℤ * Q.inertiaDeg ℤ := fun Q hQ ↦ by
    have hQ' := Set.mem_toFinset.mp hQ
    haveI : Q.IsPrime := hQ'.1
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) Q).ne'
      (Ideal.inertiaDeg_pos (R := ℤ) Q).ne')
  exact mul_eq_one.mp ((Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm P
    (Set.mem_toFinset.mpr hP)).symm

/-- If `p` splits completely, every prime above `p` is unramified. -/
theorem unramified_of_splitsCompletely (hsplit : SplitsCompletely (K := K) p) :
    ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1 := fun _ hP ↦
  (ramificationIdx_eq_one_and_inertiaDeg_eq_one hsplit hP).1

/-- If every prime above `p` is unramified, `p 𝓞 K` is the product of the primes above `p`. -/
theorem span_natCast_eq_prod_of_unramified
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1) :
    Ideal.span {(p : 𝓞 K)} = ∏ P ∈ (primesOver (span {(p : ℤ)}) (𝓞 K)).toFinset, P := by
  haveI := Int.ideal_span_isMaximal_of_prime p
  have h := Ideal.map_algebraMap_eq_finsetProd_pow (S := ℤ) (R := 𝓞 K)
    (span_natCast_ne_bot_of_prime hp.out)
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at h
  rw [h]
  exact Finset.prod_congr rfl fun P hP ↦ by
    rw [he P (Set.mem_toFinset.mp hP), pow_one]

/-- If every prime above `p` is unramified, an element lying in `P ^ m` for every prime `P` above
`p` is divisible by `p ^ m`. -/
theorem mem_span_pow_of_forall_mem_pow
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1) {x : 𝓞 K} {m : ℕ}
    (hx : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), x ∈ P ^ m) :
    x ∈ Ideal.span {(p : 𝓞 K) ^ m} := by
  set S := primesOver (span {(p : ℤ)}) (𝓞 K)
  have hcop : (S.toFinset : Set (Ideal (𝓞 K))).Pairwise
      (Function.onFun IsCoprime fun P ↦ P ^ m) := by
    intro P hP Q hQ hPQ
    rw [Set.coe_toFinset] at hP hQ
    haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
    haveI : Q.IsMaximal := Ideal.primesOver.isMaximal ⟨Q, hQ⟩
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance hPQ)).pow
  rw [← Ideal.span_singleton_pow, span_natCast_eq_prod_of_unramified he,
    ← Finset.prod_pow,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
  simp only [Submodule.mem_iInf, Set.mem_toFinset]
  exact hx

/-- If every prime above `p` is unramified, `p ∉ P ^ 2` for every prime `P` above `p`. -/
theorem natCast_notMem_sq_of_unramified
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) : (p : 𝓞 K) ∉ P ^ 2 := by
  classical
  intro h
  set S := primesOver (span {(p : ℤ)}) (𝓞 K)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (span_natCast_ne_bot_of_prime hp.out) hP
  haveI : P.IsPrime := hP.1
  have hle : (∏ Q ∈ S.toFinset, Q) ≤ P ^ 2 := by
    rw [← span_natCast_eq_prod_of_unramified he, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← Finset.mul_prod_erase _ _ (Set.mem_toFinset.mpr hP), pow_two, ← Ideal.dvd_iff_le] at hle
  have hdvd : P ∣ ∏ Q ∈ S.toFinset.erase P, Q :=
    (mul_dvd_mul_iff_left (by simpa using hP0)).mp hle
  obtain ⟨Q, hQ, hPQ⟩ := ((Ideal.prime_of_isPrime hP0 inferInstance).dvd_finsetProd_iff _).mp hdvd
  have hQ' := Set.mem_toFinset.mp (Finset.mem_of_mem_erase hQ)
  haveI : Q.IsMaximal := Ideal.primesOver.isMaximal ⟨Q, hQ'⟩
  exact Finset.ne_of_mem_erase hQ (Ideal.IsMaximal.eq_of_le inferInstance
    (Ideal.IsPrime.ne_top inferInstance) (Ideal.dvd_iff_le.mp hPQ))

/-- If every prime above `p` is unramified and `P` lies above `p`, a natural number lies in `P ^ m`
only if it is divisible by `p ^ m`. -/
theorem dvd_of_natCast_mem_pow
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) {c m : ℕ} (hc : (c : 𝓞 K) ∈ P ^ m) :
    p ^ m ∣ c := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact dvd_zero _
  obtain ⟨r, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.out.ne_one
  haveI : P.IsPrime := hP.1
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (span_natCast_ne_bot_of_prime hp.out) hP
  have huP : (u : 𝓞 K) ∉ P := fun h ↦ hu (by
    haveI : P.LiesOver (span {(p : ℤ)}) := hP.2
    have : (u : ℤ) ∈ P.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact h
    rw [← Ideal.over_def P (span {(p : ℤ)}), Ideal.mem_span_singleton] at this
    exact Int.natCast_dvd_natCast.mp this)
  rw [Nat.cast_mul, Nat.cast_pow, mul_comm] at hc
  rcases Ideal.IsPrime.mul_mem_pow P hc with h | h
  · exact absurd h huP
  · refine Dvd.dvd.mul_right (pow_dvd_pow p ?_) u
    by_contra hlt
    push Not at hlt
    exact pow_notMem_pow_succ hP0 (natCast_mem_of_mem_primesOver hP)
      (natCast_notMem_sq_of_unramified he hP) r (Ideal.pow_le_pow_right hlt h)

/-- If `p` splits completely and `P` lies above `p`, every element of `𝓞 K` is congruent to a
natural number modulo `P ^ m`. -/
theorem exists_natCast_sub_mem_pow (hsplit : SplitsCompletely (K := K) p) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) (x : 𝓞 K) (m : ℕ) :
    ∃ c : ℕ, x - c ∈ P ^ m := by
  haveI : CharP (𝓞 K ⧸ P ^ m) (p ^ m) := ⟨fun c ↦ by
    rw [← map_natCast (Ideal.Quotient.mk (P ^ m)), Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨dvd_of_natCast_mem_pow (unramified_of_splitsCompletely hsplit) hP, fun ⟨t, ht⟩ ↦ ?_⟩
    rw [ht, Nat.cast_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (natCast_mem_of_mem_primesOver hP) m)⟩
  have hcard : Nat.card (𝓞 K ⧸ P ^ m) = p ^ m := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, natCard_quotient_of_mem_primesOver hP,
      (ramificationIdx_eq_one_and_inertiaDeg_eq_one hsplit hP).2, pow_one]
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Finite (𝓞 K ⧸ P ^ m) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have hbij := (ZMod.castHom_injective (𝓞 K ⧸ P ^ m)).bijective_of_nat_card_le (by
    rw [hcard, Nat.card_zmod])
  obtain ⟨c, hc⟩ := hbij.2 (Ideal.Quotient.mk _ x)
  refine ⟨c.val, ?_⟩
  rw [← Ideal.Quotient.eq, map_natCast, ← hc, ZMod.castHom_apply, ZMod.natCast_val]

/-- If `p` splits completely, then for every `θ ∈ 𝓞 K` the element `θ (θ - 1) ⋯ (θ - k + 1)` is
divisible by `p ^ ν_p(k!)` in `𝓞 K`. -/
theorem aeval_descPochhammer_mem_span (hsplit : SplitsCompletely (K := K) p) (θ : 𝓞 K) (k : ℕ) :
    aeval θ (descPochhammer ℤ k) ∈ Ideal.span {(p : 𝓞 K) ^ (Nat.factorial k).factorization p} := by
  refine mem_span_pow_of_forall_mem_pow (unramified_of_splitsCompletely hsplit) fun P hP ↦ ?_
  obtain ⟨c, hc⟩ := exists_natCast_sub_mem_pow hsplit hP θ ((Nat.factorial k).factorization p)
  have h1 : aeval θ (descPochhammer ℤ k) - aeval (c : 𝓞 K) (descPochhammer ℤ k) ∈
      P ^ (Nat.factorial k).factorization p := by
    obtain ⟨d, hd⟩ := sub_dvd_eval_sub θ (c : 𝓞 K) ((descPochhammer ℤ k).map (algebraMap ℤ (𝓞 K)))
    rw [eval_map, eval_map, ← aeval_def, ← aeval_def] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ hc
  have h2 : aeval (c : 𝓞 K) (descPochhammer ℤ k) = ((c.descFactorial k : ℕ) : 𝓞 K) := by
    rw [aeval_def, ← eval_map, descPochhammer_map, descPochhammer_eval_eq_descFactorial]
  have h3 : ((c.descFactorial k : ℕ) : 𝓞 K) ∈ P ^ (Nat.factorial k).factorization p := by
    obtain ⟨t, ht⟩ :=
      (Nat.ordProj_dvd (Nat.factorial k) p).trans (Nat.factorial_dvd_descFactorial c k)
    rw [ht, Nat.cast_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (natCast_mem_of_mem_primesOver hP) _)
  have := add_mem h1 (h2 ▸ h3)
  rwa [sub_add_cancel] at this

/-- **The lower bound.**  If `p` splits completely in `K`, then `p ^ ν_p(0! 1! ⋯ (n - 1)!)` divides
the index of every generator of `K`, `n = [K : ℚ]`. -/
theorem pow_dvd_index_of_splitsCompletely (hsplit : SplitsCompletely (K := K) p) {θ : 𝓞 K}
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ^ ∑ k ∈ Finset.range (Module.finrank ℚ K), (Nat.factorial k).factorization p ∣
      RingOfIntegers.index θ := by
  obtain ⟨b⟩ := nonempty_basis_fin (K := K)
  have hβ := fun k : Fin (Module.finrank ℚ K) ↦
    Ideal.mem_span_singleton'.mp (aeval_descPochhammer_mem_span hsplit θ k)
  choose β hβ using hβ
  rw [index_eq_natAbs_det hθ b, det_pow_eq_pow_mul_det b θ β hβ, Int.natAbs_mul,
    Int.natAbs_natCast]
  exact Dvd.intro _ rfl

/-- **The bound is attained.**  If `p` splits completely in `K`, some generator `θ` of `K` has
index `p ^ ν_p(0! 1! ⋯ (n - 1)!) · m` with `p ∤ m`. -/
theorem exists_index_eq_pow_mul_of_splitsCompletely (hsplit : SplitsCompletely (K := K) p) :
    ∃ θ : 𝓞 K, Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧ ∃ m : ℕ, ¬ p ∣ m ∧
      RingOfIntegers.index θ =
        p ^ (∑ k ∈ Finset.range (Module.finrank ℚ K), (Nat.factorial k).factorization p) * m := by
  classical
  set n := Module.finrank ℚ K
  set S := primesOver (span {(p : ℤ)}) (𝓞 K)
  set a : ℕ → ℕ := fun k ↦ (Nat.factorial k).factorization p
  set A := ∑ k ∈ Finset.range n, a k
  set u : ℕ → ℕ := fun k ↦ Nat.factorial k / p ^ a k
  have hku : ∀ k, Nat.factorial k = p ^ a k * u k := fun k ↦
    (Nat.ordProj_mul_ordCompl_eq_self (Nat.factorial k) p).symm
  have hu : ∀ k, ¬ p ∣ u k := fun k ↦ Nat.not_dvd_ordCompl hp.out (Nat.factorial_ne_zero k)
  have haA : ∀ k : Fin n, a k + 1 ≤ A + 1 := fun k ↦ Nat.succ_le_succ
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr k.2))
  -- enumerate the `n` primes above `p`
  have hcard : Fintype.card S = n := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hsplit
  set e : Fin n ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  have hP0 : ∀ i, (e i : Ideal (𝓞 K)) ≠ ⊥ := fun i ↦
    Ideal.ne_bot_of_mem_primesOver (span_natCast_ne_bot_of_prime hp.out) (e i).2
  -- `θ ≡ i` modulo a high power of the `i`-th prime
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun i ↦ (e i : Ideal (𝓞 K))) (fun _ ↦ A + 1)
    (fun i _ ↦ Ideal.prime_of_isPrime (hP0 i) (e i).2.1)
    (fun i _ j _ hij h ↦ hij (e.injective (Subtype.ext h)))
    (fun i ↦ (((i : Fin n) : ℕ) : 𝓞 K))
  have hθ' : ∀ i : Fin n, θ - ((i : ℕ) : 𝓞 K) ∈ (e i : Ideal (𝓞 K)) ^ (A + 1) := fun i ↦
    hθ i (Finset.mem_univ i)
  have hβ := fun k : Fin n ↦ Ideal.mem_span_singleton'.mp (aeval_descPochhammer_mem_span hsplit θ k)
  choose β hβ using hβ
  -- modulo the `i`-th prime, `β k ≡ u k * binom(i, k)`
  have hr : ∀ i k : Fin n,
      β k - ((u k * (i : ℕ).choose k : ℕ) : 𝓞 K) ∈ (e i : Ideal (𝓞 K)) := by
    intro i k
    set P := (e i : Ideal (𝓞 K))
    haveI : P.IsPrime := (e i).2.1
    have h1 : aeval θ (descPochhammer ℤ (k : ℕ)) -
        aeval ((i : ℕ) : 𝓞 K) (descPochhammer ℤ (k : ℕ)) ∈ P ^ (A + 1) := by
      obtain ⟨d, hd⟩ := sub_dvd_eval_sub θ ((i : ℕ) : 𝓞 K)
        ((descPochhammer ℤ (k : ℕ)).map (algebraMap ℤ (𝓞 K)))
      rw [eval_map, eval_map, ← aeval_def, ← aeval_def] at hd
      rw [hd]
      exact Ideal.mul_mem_right _ _ (hθ' i)
    rw [aeval_def (R := ℤ) ((i : ℕ) : 𝓞 K), ← eval_map, descPochhammer_map,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, hku,
      ← hβ k] at h1
    have h2 : (β k - ((u k * (i : ℕ).choose k : ℕ) : 𝓞 K)) * (p : 𝓞 K) ^ a k ∈ P ^ (A + 1) := by
      convert h1 using 1
      push_cast
      ring
    rcases Ideal.IsPrime.mul_mem_pow P h2 with h | h
    · exact h
    · exact absurd (Ideal.pow_le_pow_right (haA k) h) (pow_notMem_pow_succ (hP0 i)
        (natCast_mem_of_mem_primesOver (e i).2)
        (natCast_notMem_sq_of_unramified (unramified_of_splitsCompletely hsplit) (e i).2) (a k))
  -- the `β k` span `𝓞 K` modulo `p`
  have hspan : ∀ x : 𝓞 K, ∃ c : Fin n → ℤ, x - ∑ k, c k • β k ∈ Ideal.span {(p : 𝓞 K)} := by
    intro x
    have hxi := fun i : Fin n ↦ exists_natCast_sub_mem_pow hsplit (e i).2 x 1
    choose xs hxs using hxi
    set B : Matrix (Fin n) (Fin n) (ZMod p) :=
      Matrix.of fun i k ↦ ((u k * (i : ℕ).choose k : ℕ) : ZMod p)
    have hBdet : IsUnit B.det := by
      rw [isUnit_iff_ne_zero, Matrix.det_of_lowerTriangular B ?_]
      · rw [Finset.prod_ne_zero_iff]
        intro i _
        simp only [B, Matrix.of_apply, Nat.choose_self, mul_one]
        exact (ZMod.natCast_eq_zero_iff _ _).not.mpr (hu i)
      · intro i k hik
        simp [B, Nat.choose_eq_zero_of_lt (show (i : ℕ) < k from hik)]
    set cbar := B⁻¹.mulVec (fun i ↦ (xs i : ZMod p))
    have hB : B.mulVec cbar = fun i ↦ (xs i : ZMod p) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBdet, Matrix.one_mulVec]
    refine ⟨fun k ↦ ((cbar k).val : ℤ), ?_⟩
    rw [← pow_one (p : 𝓞 K)]
    refine mem_span_pow_of_forall_mem_pow (unramified_of_splitsCompletely hsplit) fun P hP ↦ ?_
    obtain ⟨i, hi⟩ := e.surjective ⟨P, hP⟩
    rw [pow_one, show P = (e i : Ideal (𝓞 K)) by rw [hi]]
    set N := ∑ k : Fin n, u k * (i : ℕ).choose k * (cbar k).val
    have hcong : (N : ZMod p) = (xs i : ZMod p) := by
      have := congr_fun hB i
      simp only [Matrix.mulVec, dotProduct, B, Matrix.of_apply] at this
      rw [← this]
      push_cast [N]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [ZMod.natCast_zmod_val]
    have hmem1 : ((N : ℕ) : 𝓞 K) - (xs i : 𝓞 K) ∈ (e i : Ideal (𝓞 K)) := by
      obtain ⟨t, ht⟩ := Nat.modEq_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcong)
      have : ((N : ℕ) : 𝓞 K) - (xs i : 𝓞 K) = (p : 𝓞 K) * (-(t : 𝓞 K)) := by
        have := congr_arg (Int.cast : ℤ → 𝓞 K) ht
        push_cast at this
        linear_combination -this
      rw [this]
      exact Ideal.mul_mem_right _ _ (natCast_mem_of_mem_primesOver (e i).2)
    have heq : x - ∑ k, ((cbar k).val : ℤ) • β k = (x - xs i) - (((N : ℕ) : 𝓞 K) - xs i) +
        ∑ k, ((cbar k).val : 𝓞 K) * (((u k * (i : ℕ).choose k : ℕ) : 𝓞 K) - β k) := by
      have hN : ((N : ℕ) : 𝓞 K) =
          ∑ k, ((cbar k).val : 𝓞 K) * ((u k * (i : ℕ).choose k : ℕ) : 𝓞 K) := by
        push_cast [N]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
      simp only [zsmul_eq_mul, Int.cast_natCast, mul_sub, Finset.sum_sub_distrib, hN]
      ring
    rw [heq]
    refine add_mem (sub_mem (by simpa using hxs i) hmem1) (Ideal.sum_mem _ fun k _ ↦ ?_)
    refine Ideal.mul_mem_left _ _ ?_
    rw [← neg_sub]
    exact neg_mem (hr i k)
  -- hence `p` does not divide the determinant of the `β k`
  obtain ⟨b⟩ := nonempty_basis_fin (K := K)
  have hdet : ¬ (p : ℤ) ∣ b.det β := by
    have hb := fun i : Fin n ↦ hspan (b i)
    choose C hC using hb
    have hγ := fun i ↦ Ideal.mem_span_singleton'.mp (hC i)
    choose γ hγ using hγ
    have hbi : ∀ i, b i = ∑ k, C i k • β k + (p : ℤ) • γ i := fun i ↦ by
      rw [zsmul_eq_mul, Int.cast_natCast, mul_comm, hγ i]
      abel
    have hentry : ∀ j i : Fin n, (if j = i then 1 else 0 : ℤ) =
        ∑ k, b.repr (β k) j * C i k + p * b.repr (γ i) j := by
      intro j i
      have h := congr_arg (fun y ↦ b.repr y j) (hbi i)
      simp only [Module.Basis.repr_self, map_add, map_sum, map_zsmul, Finsupp.add_apply,
        Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_apply] at h
      have h' : (if j = i then (1 : ℤ) else 0) = if i = j then 1 else 0 := by
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij, Ne.symm hij]
      rw [h', h]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
    set φ := Int.castRingHom (ZMod p)
    have hM : φ.mapMatrix (b.toMatrix β) * Matrix.of (fun k i ↦ (C i k : ZMod p)) = 1 := by
      ext j i
      have h := congr_arg (Int.cast : ℤ → ZMod p) (hentry j i)
      push_cast [ZMod.natCast_self] at h
      simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
        Module.Basis.toMatrix_apply, Matrix.one_apply, φ, eq_intCast]
      rw [h, zero_mul, add_zero]
    have h1 := congr_arg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h1
    intro hd
    rw [Module.Basis.det_apply, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
    rw [show φ (b.toMatrix β).det = 0 from hd, zero_mul] at h1
    exact zero_ne_one h1
  -- conclusion
  have hdetθ := det_pow_eq_pow_mul_det b θ β hβ
  have hprim : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    refine adjoin_eq_top_of_det_ne_zero b ?_
    rw [hdetθ]
    exact mul_ne_zero (by exact_mod_cast pow_ne_zero _ hp.out.ne_zero) fun h ↦ hdet (h ▸ dvd_zero _)
  refine ⟨θ, hprim, (b.det β).natAbs, fun h ↦ hdet (Int.natCast_dvd.mpr h), ?_⟩
  rw [index_eq_natAbs_det hprim b, hdetθ, Int.natAbs_mul, Int.natAbs_natCast]

/-- **The index at a completely split prime.**  If `p` splits completely in `K` (there are
`n = [K : ℚ]` primes above `p`), then `ν_p(i(K)) = ν_p(0! 1! ⋯ (n - 1)!)`. -/
theorem factorization_fieldIndex_of_splitsCompletely (hsplit : SplitsCompletely (K := K) p) :
    (fieldIndex K).factorization p =
      ∑ k ∈ Finset.range (Module.finrank ℚ K), (Nat.factorial k).factorization p := by
  set A := ∑ k ∈ Finset.range (Module.finrank ℚ K), (Nat.factorial k).factorization p
  have hne := fieldIndex_ne_zero (K := K)
  obtain ⟨θ, hθ, m, hm, hidx⟩ := exists_index_eq_pow_mul_of_splitsCompletely hsplit
  have hm0 : m ≠ 0 := fun h ↦ hm (h ▸ dvd_zero p)
  refine le_antisymm ?_ ?_
  · have hdvd : fieldIndex K ∣ RingOfIntegers.index θ :=
      (dvd_fieldIndex_iff K (fieldIndex K)).mp dvd_rfl θ hθ
    have hidx0 : RingOfIntegers.index θ ≠ 0 := by
      rw [hidx]; exact mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hm0
    have := (Nat.factorization_le_iff_dvd hne hidx0).mpr hdvd p
    rwa [hidx, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero] at this
  · have hdvd : p ^ A ∣ fieldIndex K :=
      (dvd_fieldIndex_iff K _).mpr fun θ hθ ↦ pow_dvd_index_of_splitsCompletely hsplit hθ
    exact (hp.out.pow_dvd_iff_le_factorization hne).mp hdvd

end Split

end NumberField
