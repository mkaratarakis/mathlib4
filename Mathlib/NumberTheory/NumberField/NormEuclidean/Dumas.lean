/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The Eisenstein–Dumas condition forces total ramification

Let `p` be a prime, let `n ≥ 1` and let `m ≥ 1` be coprime to `n`.  A monic integer polynomial
`X ^ n + ∑ i < n, a i X ^ i` satisfies the *Eisenstein–Dumas condition at `p` of slope `m / n`*
when the `p`-adic valuation of `a i` is at least `m (n - i) / n` for every `i < n`, with equality
`m` for `i = 0`; equivalently, the Newton polygon of the polynomial at `p` is the single segment
joining `(0, m)` to `(n, 0)`.  Taking `m = 1` recovers Eisenstein's condition.

Rather than fixing a normalisation, the hypotheses below carry a sequence of exponents
`c : ℕ → ℕ` with `m * (n - i) ≤ n * c i` and `p ^ c i ∣ a i`, together with `p ^ (m+1) ∤ a 0`.

The main computation, `NumberField.EisensteinDumas.mul_multiplicity_eq`, is that for a root `θ`
of such a polynomial lying in a number field `K` and a maximal ideal `𝔭` of `𝓞 K` above `p`,

`n * v_𝔭(θ) = m * v_𝔭(p)`,

which forces `n ∣ v_𝔭(p)` because `m` and `n` are coprime.  Since the ramification index is at
most the degree, this yields at once that the polynomial is irreducible (its root generates a
field of degree exactly `n`) and that `p` is totally ramified there, `𝔭 ^ n = (p)`.

## Main results

* `NumberField.EisensteinDumas.mul_multiplicity_eq`: the valuation identity `n v(θ) = m v(p)`.
* `NumberField.EisensteinDumas.dvd_multiplicity`: `n ∣ v_𝔭(p)`, hence `n ≤ v_𝔭(p)`.
* `NumberField.EisensteinDumas.finrank_eq`: the root generates a field of degree `n`, i.e. the
  Eisenstein–Dumas irreducibility criterion.
* `NumberField.EisensteinDumas.pow_eq_span`: `𝔭 ^ n = (p)`, total ramification.
-/

public section

open NumberField Finset

namespace NumberField.EisensteinDumas

variable {K : Type*} [Field K] [NumberField K]

section Setup

variable {p n : ℕ} {𝔭 : Ideal (𝓞 K)}

/-- Membership in a power of `𝔭` is divisibility of the principal ideal. -/
theorem pow_dvd_span_iff (x : 𝓞 K) (k : ℕ) : 𝔭 ^ k ∣ Ideal.span {x} ↔ x ∈ 𝔭 ^ k := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

omit [NumberField K] in
/-- A rational integer lying in a maximal ideal above `p` is divisible by `p`. -/
theorem intCast_mem_iff (hp : p.Prime) (h𝔭 : 𝔭.IsPrime)
    (hmem : (p : 𝓞 K) ∈ 𝔭) {t : ℤ} (ht : (t : 𝓞 K) ∈ 𝔭) : (p : ℤ) ∣ t := by
  have hcomap : (Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔭).IsPrime := Ideal.IsPrime.comap _
  have hpmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔭 := by
    simpa [Ideal.mem_comap] using hmem
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp) |>.isMaximal (by
        simpa [Ideal.span_singleton_eq_bot] using (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0))
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔭 :=
    (Ideal.span_singleton_le_iff_mem _).2 hpmem
  have htop : Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔭 ≠ ⊤ := hcomap.ne_top
  have : Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔭 = Ideal.span {(p : ℤ)} := (hmax.eq_of_le htop hle).symm
  have : t ∈ Ideal.span {(p : ℤ)} := by
    rw [← this, Ideal.mem_comap]
    simpa using ht
  exact Ideal.mem_span_singleton.1 this

end Setup

variable {θ : 𝓞 K} {p n m : ℕ} {a : ℕ → ℤ} {c : ℕ → ℕ} {𝔭 : Ideal (𝓞 K)}

section Main

variable (hp : p.Prime) (hn : 0 < n) (hm : 0 < m)
  (hroot : θ ^ n + ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
  (hc : ∀ i < n, m * (n - i) ≤ n * c i) (hdvd : ∀ i < n, (p : ℤ) ^ c i ∣ a i)
  (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
  (h𝔭 : 𝔭.IsMaximal) (hmem : (p : 𝓞 K) ∈ 𝔭)

include hp hn hm hroot hc hdvd hnd h𝔭 hmem

/-- **The Newton polygon computation.**  If `θ` is a root of a polynomial satisfying the
Eisenstein–Dumas condition at `p` with slope `m / n`, and `𝔭` is a maximal ideal of `𝓞 K` above
`p`, then `n * v_𝔭(θ) = m * v_𝔭(p)`. -/
theorem mul_multiplicity_eq :
    n * multiplicity 𝔭 (Ideal.span {θ}) = m * multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) := by
  classical
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a 0 ≠ 0 := by rintro h; exact hnd (by simp [h])
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    refine ha0 ?_
    have hz : ((a 0 : ℤ) : 𝓞 K) = 0 := by
      have h1 : ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * (0 : 𝓞 K) ^ i = ((a 0 : ℤ) : 𝓞 K) := by
        rw [Finset.sum_eq_single 0] <;> simp_all [Finset.mem_range, hn]
      rw [h1] at hroot
      simpa [zero_pow hn.ne'] using hroot
    exact_mod_cast (map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int).1 (by simpa using hz)
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  have hPp : Prime 𝔭 := Ideal.prime_of_isPrime h𝔭0 h𝔭.isPrime
  have hspanθ : Ideal.span {θ} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hθ0
  have hspanp : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    simp only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fun h => hp.ne_zero (by exact_mod_cast h)
  have hfinθ : FiniteMultiplicity 𝔭 (Ideal.span {θ}) := FiniteMultiplicity.of_prime_left hPp hspanθ
  have hfinp : FiniteMultiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) :=
    FiniteMultiplicity.of_prime_left hPp hspanp
  set w := multiplicity 𝔭 (Ideal.span {θ}) with hw
  set e := multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) with he
  have hθmem : θ ∈ 𝔭 ^ w := (pow_dvd_span_iff θ w).1 (pow_multiplicity_dvd _ _)
  have hpmem : (p : 𝓞 K) ∈ 𝔭 ^ e := (pow_dvd_span_iff _ e).1 (pow_multiplicity_dvd _ _)
  have hθnot : θ ∉ 𝔭 ^ (w + 1) := fun h =>
    hfinθ.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self w) ((pow_dvd_span_iff θ _).2 h)
  have hpnot : (p : 𝓞 K) ∉ 𝔭 ^ (e + 1) := fun h =>
    hfinp.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self e) ((pow_dvd_span_iff _ _).2 h)
  have he1 : 1 ≤ e := hfinp.le_multiplicity_of_pow_dvd
    ((pow_dvd_span_iff _ 1).2 (by simpa using hmem))
  -- every coefficient has positive valuation
  have hcpos : ∀ i, i < n → 1 ≤ c i := by
    intro i hi
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · have h2 := hc i hi
      rw [h, Nat.mul_zero] at h2
      have : 1 ≤ n - i := by omega
      exact absurd h2 (by nlinarith)
    · exact h
  have hcoeff : ∀ i, i < n → ((a i : ℤ) : 𝓞 K) ∈ 𝔭 ^ (e * c i) := by
    intro i hi
    obtain ⟨y, hy⟩ := hdvd i hi
    have hrw : ((a i : ℤ) : 𝓞 K) = ((p : 𝓞 K)) ^ c i * ((y : ℤ) : 𝓞 K) := by
      rw [hy]; push_cast; ring
    rw [hrw, pow_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpmem _)
  have hterm : ∀ i, i < n → ((a i : ℤ) : 𝓞 K) * θ ^ i ∈ 𝔭 ^ (e * c i + i * w) := by
    intro i hi
    rw [pow_add]
    refine Ideal.mul_mem_mul (hcoeff i hi) ?_
    rw [mul_comm, pow_mul]
    exact Ideal.pow_mem_pow hθmem _
  -- `θ` lies in `𝔭`
  have hθ1 : θ ∈ 𝔭 := by
    refine h𝔭.isPrime.mem_of_pow_mem n ?_
    have hrw : θ ^ n = -∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i := by
      linear_combination hroot
    rw [hrw]
    refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.1 hi
    refine Ideal.mul_mem_right _ _ ?_
    have hle : 𝔭 ^ (e * c i) ≤ 𝔭 ^ 1 := Ideal.pow_le_pow_right (by
      have := hcpos i hi'; nlinarith)
    simpa using hle (hcoeff i hi')
  have hw1 : 1 ≤ w := hfinθ.le_multiplicity_of_pow_dvd
    ((pow_dvd_span_iff θ 1).2 (by simpa using hθ1))
  -- the valuation of the constant coefficient is exactly `m * e`
  have hc0 : c 0 = m := by
    have hge : m ≤ c 0 := by have := hc 0 hn; simp only [Nat.sub_zero] at this; nlinarith
    by_contra hne
    exact hnd (dvd_trans (pow_dvd_pow _ (by omega)) (hdvd 0 hn))
  obtain ⟨u, hu⟩ := hdvd 0 hn
  have hunot : ¬ (p : ℤ) ∣ u := by
    rintro ⟨v, rfl⟩
    exact hnd ⟨v, by rw [hu, hc0]; ring⟩
  have hune : ((u : ℤ) : 𝓞 K) ∉ 𝔭 := fun h =>
    hunot (intCast_mem_iff hp h𝔭.isPrime hmem h)
  have hspan0 : Ideal.span {((a 0 : ℤ) : 𝓞 K)}
      = (Ideal.span {(p : 𝓞 K)}) ^ m * Ideal.span {((u : ℤ) : 𝓞 K)} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
    congr 1
    rw [hu, hc0]; push_cast; ring
  have hfin0 : FiniteMultiplicity 𝔭 (Ideal.span {((a 0 : ℤ) : 𝓞 K)}) := by
    refine FiniteMultiplicity.of_prime_left hPp ?_
    simp only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fun h => ha0 (by exact_mod_cast (map_eq_zero_iff _
      (algebraMap ℤ (𝓞 K)).injective_int).1 (by simpa using h))
  have huzero : multiplicity 𝔭 (Ideal.span {((u : ℤ) : 𝓞 K)}) = 0 := by
    refine multiplicity_eq_zero.2 fun hdd => hune ?_
    have h1 : 𝔭 ^ 1 ∣ Ideal.span {((u : ℤ) : 𝓞 K)} := by rwa [pow_one]
    simpa using (pow_dvd_span_iff _ 1).1 h1
  have hE : multiplicity 𝔭 (Ideal.span {((a 0 : ℤ) : 𝓞 K)}) = m * e := by
    rw [hspan0] at hfin0 ⊢
    rw [multiplicity_mul hPp hfin0, FiniteMultiplicity.multiplicity_pow hPp hfinp, huzero,
      add_zero, he]
  have h0mem : ((a 0 : ℤ) : 𝓞 K) ∈ 𝔭 ^ (m * e) := by
    have := hcoeff 0 hn
    rwa [hc0, mul_comm] at this
  have h0not : ((a 0 : ℤ) : 𝓞 K) ∉ 𝔭 ^ (m * e + 1) := fun h =>
    hfin0.not_pow_dvd_of_multiplicity_lt (by rw [hE]; exact Nat.lt_succ_self _)
      ((pow_dvd_span_iff _ _).2 h)
  -- the valuation of `θ ^ n` is exactly `n * w`
  have hfinθn : FiniteMultiplicity 𝔭 (Ideal.span {θ ^ n}) := by
    refine FiniteMultiplicity.of_prime_left hPp ?_
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using pow_ne_zero n hθ0
  have hW : multiplicity 𝔭 (Ideal.span {θ ^ n}) = n * w := by
    rw [← Ideal.span_singleton_pow, FiniteMultiplicity.multiplicity_pow hPp hfinθ]
  have hnmem : θ ^ n ∈ 𝔭 ^ (n * w) := by
    rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow hθmem _
  have hnnot : θ ^ n ∉ 𝔭 ^ (n * w + 1) := fun h =>
    hfinθn.not_pow_dvd_of_multiplicity_lt (by rw [hW]; exact Nat.lt_succ_self _)
      ((pow_dvd_span_iff _ _).2 h)
  -- the trichotomy
  rcases lt_trichotomy (n * w) (m * e) with hlt | hEq | hgt
  · -- `n w < m e` is impossible: every term would push `θ ^ n` one step deeper
    exfalso
    refine hnnot ?_
    have hrw : θ ^ n = -∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i := by
      linear_combination hroot
    rw [hrw]
    refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.1 hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simpa using Ideal.pow_le_pow_right (by omega : n * w + 1 ≤ m * e) h0mem
    · refine Ideal.pow_le_pow_right ?_ (hterm i hi')
      obtain ⟨j, hj⟩ : ∃ j, n = i + j := ⟨n - i, by omega⟩
      have hj1 : 1 ≤ j := by omega
      have hcj : m * j ≤ n * c i := by have := hc i hi'; rw [hj] at this ⊢; simpa using this
      nlinarith [hlt, hcj, hj1, hipos, hn]
  · exact hEq
  · -- `n w > m e` is impossible: every term would push `a 0` one step deeper
    exfalso
    refine h0not ?_
    have hrw : ((a 0 : ℤ) : 𝓞 K)
        = -(θ ^ n + ∑ i ∈ range n \ {0}, ((a i : ℤ) : 𝓞 K) * θ ^ i) := by
      have hsplit : ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i
          = ((a 0 : ℤ) : 𝓞 K) + ∑ i ∈ range n \ {0}, ((a i : ℤ) : 𝓞 K) * θ ^ i := by
        rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.2 (Finset.mem_range.2 hn))]
        simp [add_comm]
      rw [hsplit] at hroot
      linear_combination (norm := ring_nf) hroot
    rw [hrw]
    refine neg_mem (Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i hi => ?_))
    · exact Ideal.pow_le_pow_right (by omega : m * e + 1 ≤ n * w) hnmem
    · have hi' : i < n := Finset.mem_range.1 (Finset.mem_sdiff.1 hi).1
      have hipos : 0 < i := Nat.pos_of_ne_zero (by simpa using (Finset.mem_sdiff.1 hi).2)
      refine Ideal.pow_le_pow_right ?_ (hterm i hi')
      obtain ⟨j, hj⟩ : ∃ j, n = i + j := ⟨n - i, by omega⟩
      have hj1 : 1 ≤ j := by omega
      have hcj : m * j ≤ n * c i := by have := hc i hi'; rw [hj] at this ⊢; simpa using this
      nlinarith [hgt, hcj, hj1, hipos, hn]

/-- The root of an Eisenstein–Dumas polynomial lies in every maximal ideal above `p`. -/
theorem one_le_multiplicity_root : 1 ≤ multiplicity 𝔭 (Ideal.span {θ}) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a 0 ≠ 0 := by rintro h; exact hnd (by simp [h])
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    refine ha0 ?_
    have hz : ((a 0 : ℤ) : 𝓞 K) = 0 := by
      have h1 : ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * (0 : 𝓞 K) ^ i = ((a 0 : ℤ) : 𝓞 K) := by
        rw [Finset.sum_eq_single 0] <;> simp_all [Finset.mem_range]
      rw [h1] at hroot
      simpa [zero_pow hn.ne'] using hroot
    exact_mod_cast (map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int).1 (by simpa using hz)
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  have hPp : Prime 𝔭 := Ideal.prime_of_isPrime h𝔭0 h𝔭.isPrime
  have hspanθ : Ideal.span {θ} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hθ0
  have hfinθ : FiniteMultiplicity 𝔭 (Ideal.span {θ}) := FiniteMultiplicity.of_prime_left hPp hspanθ
  have hcpos : ∀ i, i < n → 1 ≤ c i := by
    intro i hi
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · have h2 := hc i hi
      rw [h, Nat.mul_zero] at h2
      have : 1 ≤ n - i := by omega
      exact absurd h2 (by nlinarith)
    · exact h
  have hθ1 : θ ∈ 𝔭 := by
    refine h𝔭.isPrime.mem_of_pow_mem n ?_
    have hrw : θ ^ n = -∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i := by linear_combination hroot
    rw [hrw]
    refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.1 hi
    refine Ideal.mul_mem_right _ _ ?_
    have hdvdp : (p : ℤ) ∣ a i :=
      dvd_trans (dvd_pow_self _ (by have := hcpos i hi'; omega : c i ≠ 0)) (hdvd i hi')
    obtain ⟨z, hz⟩ := hdvdp
    have hrw2 : ((a i : ℤ) : 𝓞 K) = (p : 𝓞 K) * ((z : ℤ) : 𝓞 K) := by
      rw [hz]; push_cast; ring
    rw [hrw2]
    exact Ideal.mul_mem_right _ _ hmem
  exact hfinθ.le_multiplicity_of_pow_dvd ((pow_dvd_span_iff θ 1).2 (by simpa using hθ1))

/-- Since `m` and `n` are coprime, `n` divides the ramification index of `𝔭`. -/
theorem dvd_multiplicity (hmn : Nat.Coprime m n) :
    n ∣ multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) := by
  have h := mul_multiplicity_eq hp hn hm hroot hc hdvd hnd h𝔭 hmem
  exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hmn) ⟨_, h.symm⟩)

/-- The ramification index of `𝔭` is at least `n`. -/
theorem le_multiplicity (hmn : Nat.Coprime m n) :
    n ≤ multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) := by
  obtain ⟨k, hk⟩ := dvd_multiplicity hp hn hm hroot hc hdvd hnd h𝔭 hmem hmn
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exfalso
    have h := mul_multiplicity_eq hp hn hm hroot hc hdvd hnd h𝔭 hmem
    rw [hk] at h
    have hw := one_le_multiplicity_root hp hn hm hroot hc hdvd hnd h𝔭 hmem
    simp only [Nat.mul_zero, Nat.mul_eq_zero] at h
    omega
  · rw [hk]
    exact Nat.le_mul_of_pos_right _ hkpos

end Main

section Ramification

variable {p n : ℕ} {𝔭 : Ideal (𝓞 K)}

/-- The absolute norm of a maximal ideal containing `p` is a positive power of `p`. -/
theorem exists_absNorm_eq (hp : p.Prime) (h𝔭 : 𝔭.IsMaximal) (hmem : (p : 𝓞 K) ∈ 𝔭) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm 𝔭 = p ^ k := by
  have hspan : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hmem
  have hdvdq : Ideal.absNorm 𝔭 ∣ p ^ Module.finrank ℤ (𝓞 K) := by
    have h := Ideal.absNorm_dvd_absNorm_of_le hspan
    rwa [Ideal.absNorm_span_natCast] at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvdq
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using hk)) h𝔭.ne_top
  · exact h

/-- The ramification index of a maximal ideal above `p` is at most the degree of the field. -/
theorem multiplicity_le_finrank (hp : p.Prime) (h𝔭 : 𝔭.IsMaximal) (hmem : (p : 𝓞 K) ∈ 𝔭) :
    multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) ≤ Module.finrank ℚ K := by
  classical
  have hp1 : 1 < p := hp.one_lt
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  have hPp : Prime 𝔭 := Ideal.prime_of_isPrime h𝔭0 h𝔭.isPrime
  have hspanp : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    simp only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fun h => hp.ne_zero (by exact_mod_cast h)
  set e := multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) with he
  have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 ^ e := by
    rw [← Ideal.dvd_iff_le]
    exact pow_multiplicity_dvd _ _
  obtain ⟨k, hk1, hk⟩ := exists_absNorm_eq hp h𝔭 hmem
  have hdvd : Ideal.absNorm (𝔭 ^ e) ∣ Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  rw [map_pow, hk, Ideal.absNorm_span_natCast, ← pow_mul] at hdvd
  have := (Nat.pow_dvd_pow_iff_le_right hp1).1 hdvd
  rw [NumberField.RingOfIntegers.rank] at this
  nlinarith [this, hk1]

end Ramification

section Conclusion

variable (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
  (hroot : θ ^ n + ∑ i ∈ range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
  (hc : ∀ i < n, m * (n - i) ≤ n * c i) (hdvd : ∀ i < n, (p : ℤ) ^ c i ∣ a i)
  (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
  (h𝔭 : 𝔭.IsMaximal) (hmem : (p : 𝓞 K) ∈ 𝔭)

include hp hn hm hmn hroot hc hdvd hnd h𝔭 hmem

/-- **The Eisenstein–Dumas criterion.**  A number field containing a root of an
Eisenstein–Dumas polynomial of degree `n` and slope `m / n` has degree at least `n` over `ℚ`;
in particular, if it is generated by that root, its degree is exactly `n` and the polynomial is
irreducible. -/
theorem le_finrank : n ≤ Module.finrank ℚ K :=
  le_trans (le_multiplicity hp hn hm hroot hc hdvd hnd h𝔭 hmem hmn)
    (multiplicity_le_finrank hp h𝔭 hmem)

/-- **Total ramification.**  If a number field of degree `n` contains a root of an
Eisenstein–Dumas polynomial of degree `n` and slope `m / n`, then `p` is totally ramified:
`𝔭 ^ n = (p)`. -/
theorem pow_eq_span (hdeg : Module.finrank ℚ K = n) : 𝔭 ^ n = Ideal.span {(p : 𝓞 K)} := by
  classical
  have hem : multiplicity 𝔭 (Ideal.span {(p : 𝓞 K)}) = n :=
    le_antisymm (by rw [← hdeg]; exact multiplicity_le_finrank hp h𝔭 hmem)
      (le_multiplicity hp hn hm hroot hc hdvd hnd h𝔭 hmem hmn)
  have hdvdI : 𝔭 ^ n ∣ Ideal.span {(p : 𝓞 K)} := by
    rw [← hem]; exact pow_multiplicity_dvd _ _
  obtain ⟨k, hk1, hk⟩ := exists_absNorm_eq hp h𝔭 hmem
  -- the residue degree is one
  have hk : Ideal.absNorm 𝔭 = p := by
    have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 ^ n := Ideal.le_of_dvd hdvdI
    have hdvd2 : Ideal.absNorm (𝔭 ^ n) ∣ Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) :=
      Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, hk, Ideal.absNorm_span_natCast, ← pow_mul,
      NumberField.RingOfIntegers.rank, hdeg] at hdvd2
    have hkn := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd2
    have : k = 1 := by nlinarith [hkn, hk1, hn]
    rw [hk, this, pow_one]
  -- and then the norms of `𝔭 ^ n` and of `(p)` agree
  obtain ⟨J, hJ⟩ := hdvdI
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ n := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hdeg]
  have hJ1 : Ideal.absNorm J = 1 := by
    have := congrArg Ideal.absNorm hJ
    rw [hnorm, map_mul, map_pow, hk] at this
    have hpn : (p : ℕ) ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpn) (by rw [mul_one]; exact this)).symm
  rw [hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]

end Conclusion

end NumberField.EisensteinDumas
