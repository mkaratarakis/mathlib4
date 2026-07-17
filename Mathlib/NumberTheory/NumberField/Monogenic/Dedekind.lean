/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Exponent

/-!
# Sufficiency direction of Dedekind's index criterion

Let `K` be a number field, `θ : 𝓞 K` a generator of `K` over `ℚ` with minimal polynomial
`f` over `ℤ`, and `p` a rational prime.  Suppose we are given a decomposition
`f = g * h + p * M` in `ℤ[X]`.  Dedekind's index criterion states that if

* `g mod p` is squarefree,
* every irreducible factor of `h mod p` divides `g mod p`, and
* `g mod p`, `h mod p`, `M mod p` generate the unit ideal of `𝔽_p[X]`,

then `p` does not divide `[𝓞 K : ℤ[θ]]` (equivalently, `p ∤ RingOfIntegers.exponent θ`).
This is the *sufficiency* half of the criterion; the necessity half (a common factor of
`g`, `h`, `M` mod `p` forces `p` to divide the index) is provided at a double root by
`RingOfIntegers.adjoin_ne_top_of_sq_dvd_eval` and in generalized form by
`RingOfIntegers.dvd_exponent_of_sq_factor`.

The proof is Dedekind's original argument, following K. Conrad's exposition
(*Dedekind's index theorem*), stated contrapositively.  If `p ∣ exponent θ` there is
`β ∈ 𝓞 K \ ℤ[θ]` with `p * β = r(θ)` for some `r ∈ ℤ[X]` of degree `< deg f` whose
reduction mod `p` is nonzero.  Let `Ā = gcd(r̄, f̄)` in `𝔽_p[X]` and lift the Bézout
identity to write `A(θ) = p * γ` with `γ ∈ 𝓞 K` and `A` a lift of `Ā`.  Scaling the
roots of the minimal polynomial `q` of `γ` by `p` produces a polynomial multiple of `f`
reducing to `Ā ^ deg q`, whence `Ā ^ (deg q - 1) = B̄ * k̄` for the complementary factor
`B̄ = f̄ / Ā`, which is nonconstant.  Any monic irreducible factor `π̄` of `B̄` therefore
divides `Ā`, so `π̄ ^ 2 ∣ f̄`, and a second application of the scaled-roots trick shows
`π̄` divides the reduction of `N = (f - A * B) / p`.  Finally a change-of-splitting lemma
transfers this to the given decomposition: `π̄` divides `ḡ`, `h̄` and `M̄`, contradicting
the Bézout hypothesis.

## Main results

* `RingOfIntegers.exists_notMem_adjoin_of_dvd_exponent`: if `p ∣ exponent θ` there is
  `β ∉ ℤ[θ]` with `p * β ∈ ℤ[θ]`.

* `RingOfIntegers.not_dvd_exponent_of_bezout`: the sufficiency half of Dedekind's index
  criterion.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
variable {p : ℕ} [hp : Fact p.Prime]

/-- If a rational prime `p` divides the exponent of `θ`, then there is an algebraic
integer `β` outside `ℤ[θ]` with `p * β ∈ ℤ[θ]`. -/
theorem exists_notMem_adjoin_of_dvd_exponent (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hdvd : p ∣ exponent θ) :
    ∃ β : 𝓞 K, β ∉ Algebra.adjoin ℤ {θ} ∧ (p : 𝓞 K) * β ∈ Algebra.adjoin ℤ {θ} := by
  have he : exponent θ ≠ 0 := exponent_ne_zero hθ
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by rintro rfl; simp [hm] at he
  have hSne : {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ}.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [exponent_eq_sInf, hS, Nat.sInf_empty] at he
    exact he rfl
  have hmem : exponent θ ∈ {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ} := by
    rw [exponent_eq_sInf]; exact Nat.sInf_mem hSne
  have hmlt : m < exponent θ := by
    rw [hm]
    have h1 : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.out.two_le
    have h2 : 0 < m := Nat.pos_of_ne_zero hm0
    omega
  have hmnot : m ∉ {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ} := by
    rw [exponent_eq_sInf] at hmlt
    exact Nat.notMem_of_lt_sInf hmlt
  have hmcond : (m : 𝓞 K) ∉ conductor ℤ θ := fun hc =>
    hmnot ⟨Nat.pos_of_ne_zero hm0, hc⟩
  rw [mem_conductor_iff] at hmcond
  push Not at hmcond
  obtain ⟨b, hb⟩ := hmcond
  refine ⟨(m : 𝓞 K) * b, hb, ?_⟩
  have : (p : 𝓞 K) * ((m : 𝓞 K) * b) = ((exponent θ : ℕ) : 𝓞 K) * b := by
    rw [hm]; push_cast; ring
  rw [this]
  exact mem_conductor_iff.mp hmem.2 b

/-- A polynomial over `ℤ` reduces to `0` mod `p` iff it is divisible by the constant
polynomial `p`. -/
private theorem map_zmod_eq_zero_iff {q : ℤ[X]} :
    q.map (Int.castRingHom (ZMod p)) = 0 ↔ C (p : ℤ) ∣ q := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun i => ?_
  rw [coeff_map, coeff_zero, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **Change of splitting.**  If `A * B + p * N = g * h + p * M` in `ℤ[X]` and the
reduction of `Π` mod `p` divides the reductions of all of `A`, `B`, `g`, `h`, then it
divides the reduction of `M - N`.  Consequently the Dedekind test at a common repeated
factor does not depend on the choice of splitting. -/
private theorem map_dvd_map_sub_of_map_dvd {Pi A B g h N M : ℤ[X]} (hPi : Pi.Monic)
    (hid : A * B + C (p : ℤ) * N = g * h + C (p : ℤ) * M)
    (hA : Pi.map (Int.castRingHom (ZMod p)) ∣ A.map (Int.castRingHom (ZMod p)))
    (hB : Pi.map (Int.castRingHom (ZMod p)) ∣ B.map (Int.castRingHom (ZMod p)))
    (hg : Pi.map (Int.castRingHom (ZMod p)) ∣ g.map (Int.castRingHom (ZMod p)))
    (hh : Pi.map (Int.castRingHom (ZMod p)) ∣ h.map (Int.castRingHom (ZMod p))) :
    Pi.map (Int.castRingHom (ZMod p)) ∣
      M.map (Int.castRingHom (ZMod p)) - N.map (Int.castRingHom (ZMod p)) := by
  have hp0 : (C (p : ℤ) : ℤ[X]) ≠ 0 := by
    simp only [ne_eq, C_eq_zero]
    exact_mod_cast hp.out.pos.ne'
  -- decompose each of `A`, `B`, `g`, `h` as `Π * quotient + p * remainder`
  have key : ∀ X : ℤ[X], Pi.map (Int.castRingHom (ZMod p)) ∣ X.map (Int.castRingHom (ZMod p)) →
      ∃ X₁ X₂ : ℤ[X], X = Pi * X₁ + C (p : ℤ) * X₂ := by
    intro X hX
    have h0 : (X %ₘ Pi).map (Int.castRingHom (ZMod p)) = 0 := by
      rw [map_modByMonic _ hPi, (modByMonic_eq_zero_iff_dvd (hPi.map _)).mpr hX]
    obtain ⟨X₂, hX₂⟩ := map_zmod_eq_zero_iff.mp h0
    exact ⟨X /ₘ Pi, X₂, by linear_combination hX₂ - modByMonic_add_div X Pi⟩
  obtain ⟨A₁, A₂, hA'⟩ := key A hA
  obtain ⟨B₁, B₂, hB'⟩ := key B hB
  obtain ⟨g₁, g₂, hg'⟩ := key g hg
  obtain ⟨h₁, h₂, hh'⟩ := key h hh
  rw [hA', hB', hg', hh'] at hid
  -- extract the coefficient of `Π ^ 2`
  have h1 : Pi ^ 2 * (A₁ * B₁ - g₁ * h₁) =
      C (p : ℤ) * (Pi * (g₁ * h₂ + g₂ * h₁ - A₁ * B₂ - A₂ * B₁) +
        C (p : ℤ) * (g₂ * h₂ - A₂ * B₂) + (M - N)) := by
    linear_combination hid
  have hPine : Pi.map (Int.castRingHom (ZMod p)) ≠ 0 := (hPi.map _).ne_zero
  have h2 : (A₁ * B₁ - g₁ * h₁).map (Int.castRingHom (ZMod p)) = 0 := by
    have := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, map_C,
      Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_self, map_zero, zero_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hPine
    · exact h
  obtain ⟨W, hW⟩ := map_zmod_eq_zero_iff.mp h2
  -- cancel `p` in the identity
  have h3 : Pi ^ 2 * W =
      Pi * (g₁ * h₂ + g₂ * h₁ - A₁ * B₂ - A₂ * B₁) +
        C (p : ℤ) * (g₂ * h₂ - A₂ * B₂) + (M - N) := by
    apply mul_left_cancel₀ hp0
    linear_combination h1 - Pi ^ 2 * hW
  have h4 : M.map (Int.castRingHom (ZMod p)) - N.map (Int.castRingHom (ZMod p)) =
      (Pi.map (Int.castRingHom (ZMod p))) ^ 2 * (W.map (Int.castRingHom (ZMod p))) -
        (Pi.map (Int.castRingHom (ZMod p))) *
          (g₁.map (Int.castRingHom (ZMod p)) * h₂.map (Int.castRingHom (ZMod p)) +
            g₂.map (Int.castRingHom (ZMod p)) * h₁.map (Int.castRingHom (ZMod p)) -
            A₁.map (Int.castRingHom (ZMod p)) * B₂.map (Int.castRingHom (ZMod p)) -
            A₂.map (Int.castRingHom (ZMod p)) * B₁.map (Int.castRingHom (ZMod p))) := by
    have := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub,
      map_C, Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_self, map_zero,
      zero_mul] at this
    linear_combination -this
  rw [h4]
  exact dvd_sub (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _) (Dvd.dvd.mul_right dvd_rfl _)

/-- **Dedekind's index criterion (sufficiency).**  Let `θ` generate `K` over `ℚ`, with
minimal polynomial `f` over `ℤ`, and let `f = g * h + p * M` be a decomposition in
`ℤ[X]`.  If mod `p` the factor `g` is squarefree, every irreducible factor of `h`
divides `g`, and `g`, `h`, `M` generate the unit ideal of `𝔽_p[X]`, then `p` does not
divide the exponent (equivalently, the index `[𝓞 K : ℤ[θ]]`). -/
theorem not_dvd_exponent_of_bezout (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {g h M : ℤ[X]} (hf : minpoly ℤ θ = g * h + C (p : ℤ) * M)
    (hsq : Squarefree (g.map (Int.castRingHom (ZMod p))))
    (hrad : ∀ q : (ZMod p)[X], Irreducible q → q ∣ h.map (Int.castRingHom (ZMod p)) →
      q ∣ g.map (Int.castRingHom (ZMod p)))
    (hbez : ∃ u v w : (ZMod p)[X],
      u * g.map (Int.castRingHom (ZMod p)) + v * h.map (Int.castRingHom (ZMod p)) +
        w * M.map (Int.castRingHom (ZMod p)) = 1) :
    ¬ p ∣ exponent θ := by
  intro hdvd
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  have hp𝓞 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hfm : (minpoly ℤ θ).Monic := minpoly.monic θ.isIntegral
  -- Step 1: a bad denominator β and its numerator polynomial r of degree < deg f
  obtain ⟨β, hβ, hpβ⟩ := exists_notMem_adjoin_of_dvd_exponent hθ hdvd
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hpβ
  obtain ⟨c, hc⟩ := hpβ
  set r := c %ₘ minpoly ℤ θ with hrdef
  have hrθ : aeval θ r = (p : 𝓞 K) * β := by
    have hdivmod := modByMonic_add_div c (minpoly ℤ θ)
    have := congrArg (aeval θ) hdivmod
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at this
    have hc' : aeval θ c = (p : 𝓞 K) * β := hc
    rw [← hc', ← this]
  have hr0 : r.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    obtain ⟨r', hr'⟩ := map_zmod_eq_zero_iff.mp h0
    apply hβ
    have hcalc : (p : 𝓞 K) * aeval θ r' = (p : 𝓞 K) * β := by
      rw [← hrθ, hr']
      simp [mul_comm]
    have := mul_left_cancel₀ hp𝓞 hcalc
    rw [← this, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨r', rfl⟩
  have hrne : r ≠ 0 := fun h => hr0 (by rw [h, Polynomial.map_zero])
  have hrdeg : r.natDegree < (minpoly ℤ θ).natDegree :=
    natDegree_lt_natDegree hrne (degree_modByMonic_lt c hfm)
  -- Step 2: the gcd Ā and a lift A with A(θ) = p * γ
  set rbar := r.map (Int.castRingHom (ZMod p)) with hrbar
  set fbar := (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) with hfbar
  set Abar := EuclideanDomain.gcd rbar fbar with hAbardef
  have hAdvd_r : Abar ∣ rbar := EuclideanDomain.gcd_dvd_left _ _
  have hAdvd_f : Abar ∣ fbar := EuclideanDomain.gcd_dvd_right _ _
  have hA0 : Abar ≠ 0 := fun h0 => hr0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
  have hf0 : fbar ≠ 0 := (hfm.map _).ne_zero
  obtain ⟨A, hAmap⟩ := Polynomial.map_surjective _ hsurj Abar
  obtain ⟨u, humap⟩ := Polynomial.map_surjective _ hsurj (EuclideanDomain.gcdA rbar fbar)
  obtain ⟨v, hvmap⟩ := Polynomial.map_surjective _ hsurj (EuclideanDomain.gcdB rbar fbar)
  have hkey : (A - (r * u + minpoly ℤ θ * v)).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      hAmap, humap, hvmap, ← hrbar, ← hfbar, ← EuclideanDomain.gcd_eq_gcd_ab, ← hAbardef,
      sub_self]
  obtain ⟨w, hw⟩ := map_zmod_eq_zero_iff.mp hkey
  set γ : 𝓞 K := β * aeval θ u + aeval θ w with hγdef
  have hAθ : aeval θ A = (p : 𝓞 K) * γ := by
    have hAeq : A = r * u + minpoly ℤ θ * v + C (p : ℤ) * w := by linear_combination hw
    rw [hAeq]
    simp only [map_add, map_mul, minpoly.aeval, zero_mul, add_zero, map_natCast, hrθ]
    rw [hγdef]; ring
  -- Step 3: scaled minimal polynomial of γ gives Ā ^ d = f̄ * k̄
  set q := minpoly ℤ γ with hqdef
  have hqm : q.Monic := minpoly.monic γ.isIntegral
  set d := q.natDegree with hddef
  have hd1 : 0 < d := minpoly.natDegree_pos γ.isIntegral
  have hP0 : aeval θ ((q.scaleRoots (p : ℤ)).comp A) = 0 := by
    rw [aeval_comp, hAθ]
    have := scaleRoots_aeval_eq_zero (r := (p : ℤ)) (minpoly.aeval ℤ γ)
    simpa using this
  have hfP : minpoly ℤ θ ∣ (q.scaleRoots (p : ℤ)).comp A :=
    minpoly.isIntegrallyClosed_dvd θ.isIntegral hP0
  have hscale : (q.scaleRoots (p : ℤ)).map (Int.castRingHom (ZMod p)) = X ^ d := by
    ext i
    rw [coeff_map, coeff_scaleRoots, ← hddef, coeff_X_pow, map_mul, map_pow]
    have hz : (Int.castRingHom (ZMod p)) ((p : ℤ)) = 0 := by
      simp
    rcases lt_trichotomy i d with hlt | heq | hgt
    · rw [if_neg hlt.ne]
      have hne : d - i ≠ 0 := Nat.sub_ne_zero_of_lt hlt
      rw [hz, zero_pow hne, mul_zero]
    · rw [if_pos heq]
      have hcd : q.coeff i = 1 := by rw [heq, hddef]; exact hqm.coeff_natDegree
      have hdi : d - i = 0 := by omega
      rw [hcd, hdi, pow_zero, mul_one, map_one]
    · rw [if_neg hgt.ne']
      have hc0 : q.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (hddef ▸ hgt)
      rw [hc0, map_zero, zero_mul]
  have hkdvd : fbar ∣ Abar ^ d := by
    have := Polynomial.map_dvd (Int.castRingHom (ZMod p)) hfP
    rwa [Polynomial.map_comp, hscale, hAmap, X_pow_comp, ← hfbar] at this
  obtain ⟨k, hk⟩ := hkdvd
  -- Step 4: complementary factor B̄ is nonconstant; monic irreducible factor π
  obtain ⟨Bbar, hBbar⟩ := id hAdvd_f
  have hB0 : Bbar ≠ 0 := fun h0 => hf0 (by rw [hBbar, h0, mul_zero])
  have hdegA : Abar.natDegree < fbar.natDegree := by
    have h1 : Abar.natDegree ≤ rbar.natDegree := natDegree_le_of_dvd hAdvd_r hr0
    have h2 : rbar.natDegree ≤ r.natDegree := natDegree_map_le
    have h3 : fbar.natDegree = (minpoly ℤ θ).natDegree := hfm.natDegree_map _
    omega
  have hBunit : ¬ IsUnit Bbar := by
    intro hu
    have hdeg : fbar.natDegree = Abar.natDegree := by
      rw [hBbar, natDegree_mul hA0 hB0, natDegree_eq_zero_of_isUnit hu, add_zero]
    omega
  obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor hBunit hB0
  set π := normalize π₀ with hπdef
  have hπirr : Irreducible π := (associated_normalize π₀).irreducible hπ₀irr
  have hπmonic : π.Monic := monic_normalize hπ₀irr.ne_zero
  have hπB : π ∣ Bbar := by
    rw [hπdef, normalize_dvd_iff]; exact hπ₀dvd
  -- Step 5: π divides Ā, hence π² divides f̄
  have hcancel : Abar ^ (d - 1) = Bbar * k := by
    apply mul_left_cancel₀ hA0
    have : Abar * Abar ^ (d - 1) = Abar ^ d := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this, hk, hBbar]; ring
  have hπA : π ∣ Abar := by
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · exfalso
      have hd_eq : d = 1 := by omega
      rw [hd_eq] at hcancel
      simp only [Nat.sub_self, pow_zero] at hcancel
      exact hBunit (isUnit_of_dvd_one ⟨k, hcancel⟩)
    · have hπpow : π ∣ Abar ^ (d - 1) := hcancel ▸ hπB.mul_right k
      exact hπirr.prime.dvd_of_dvd_pow hπpow
  have hπf : π ∣ fbar := hπA.trans hAdvd_f
  -- Step 6: π divides ḡ and h̄
  have hfgh : fbar = g.map (Int.castRingHom (ZMod p)) * h.map (Int.castRingHom (ZMod p)) := by
    have := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hf
    simpa only [Polynomial.map_add, Polynomial.map_mul, map_C, Int.coe_castRingHom,
      Int.cast_natCast, ZMod.natCast_self, map_zero, C_0, zero_mul, add_zero] using this
  have hπg : π ∣ g.map (Int.castRingHom (ZMod p)) := by
    rcases hπirr.prime.dvd_mul.mp (hfgh ▸ hπf) with hcase | hcase
    · exact hcase
    · exact hrad π hπirr hcase
  have hπh : π ∣ h.map (Int.castRingHom (ZMod p)) := by
    obtain ⟨g₁, hg₁⟩ := hπg
    have hπ2 : π ^ 2 ∣ fbar := by
      rw [hBbar, sq]
      exact mul_dvd_mul hπA hπB
    have hstep : π ∣ g₁ * h.map (Int.castRingHom (ZMod p)) := by
      have hh2 : π * (g₁ * h.map (Int.castRingHom (ZMod p))) =
          g.map (Int.castRingHom (ZMod p)) * h.map (Int.castRingHom (ZMod p)) := by
        rw [hg₁]; ring
      have := hfgh ▸ hπ2
      rw [← hh2, sq] at this
      exact (mul_dvd_mul_iff_left hπirr.ne_zero).mp this
    rcases hπirr.prime.dvd_mul.mp hstep with hcase | hcase
    · exfalso
      apply hπirr.not_isUnit
      apply hsq π
      rw [hg₁]
      exact mul_dvd_mul_left π hcase
    · exact hcase
  -- Step 7: the polynomial N with f = A * B + p * N, and π ∣ N̄
  obtain ⟨B, hBmap⟩ := Polynomial.map_surjective _ hsurj Bbar
  have hN0 : (minpoly ℤ θ - A * B).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hAmap, hBmap, ← hfbar, ← hBbar, sub_self]
  obtain ⟨N, hN⟩ := map_zmod_eq_zero_iff.mp hN0
  have hNθ : aeval θ N = -(γ * aeval θ B) := by
    apply mul_left_cancel₀ hp𝓞
    have hh0 := congrArg (aeval θ) hN
    simp only [map_sub, map_mul, minpoly.aeval, zero_sub, map_natCast] at hh0
    linear_combination -hh0 - aeval θ B * hAθ
  set Q : ℤ[X] := ∑ i ∈ Finset.range (d + 1), C (q.coeff i) * B ^ (d - i) * (-N) ^ i with hQdef
  have hQθ : aeval θ Q = 0 := by
    rw [hQdef, map_sum]
    have hterm : ∀ i ∈ Finset.range (d + 1),
        aeval θ (C (q.coeff i) * B ^ (d - i) * (-N) ^ i) =
          q.coeff i • γ ^ i * (aeval θ B) ^ d := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hile : i ≤ d := by omega
      rw [map_mul, map_mul, map_pow, map_pow, map_neg, hNθ, neg_neg, aeval_C, mul_pow,
        zsmul_eq_mul]
      have hBpow : (aeval θ B) ^ (d - i) * (aeval θ B) ^ i = (aeval θ B) ^ d :=
        pow_sub_mul_pow (aeval θ B) hile
      calc algebraMap ℤ (𝓞 K) (q.coeff i) * (aeval θ B) ^ (d - i) * (γ ^ i * (aeval θ B) ^ i)
          = algebraMap ℤ (𝓞 K) (q.coeff i) * γ ^ i *
            ((aeval θ B) ^ (d - i) * (aeval θ B) ^ i) := by ring
        _ = (q.coeff i : 𝓞 K) * γ ^ i * (aeval θ B) ^ d := by
            rw [hBpow]; simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hsum : ∑ i ∈ Finset.range (d + 1), q.coeff i • γ ^ i = aeval γ q :=
      (aeval_eq_sum_range γ).symm
    rw [hsum, minpoly.aeval, zero_mul]
  have hfQ : minpoly ℤ θ ∣ Q := minpoly.isIntegrallyClosed_dvd θ.isIntegral hQθ
  have hπN : π ∣ N.map (Int.castRingHom (ZMod p)) := by
    have hπQ : π ∣ Q.map (Int.castRingHom (ZMod p)) :=
      hπf.trans (Polynomial.map_dvd _ hfQ)
    have hQmap : Q.map (Int.castRingHom (ZMod p)) =
        ∑ i ∈ Finset.range (d + 1), C ((q.coeff i : ZMod p)) * Bbar ^ (d - i) *
          (-(N.map (Int.castRingHom (ZMod p)))) ^ i := by
      rw [hQdef, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
        Polynomial.map_neg, map_C, hBmap]
      norm_cast
    have hsplit : Q.map (Int.castRingHom (ZMod p)) =
        (-(N.map (Int.castRingHom (ZMod p)))) ^ d +
          ∑ i ∈ Finset.range d, C ((q.coeff i : ZMod p)) * Bbar ^ (d - i) *
            (-(N.map (Int.castRingHom (ZMod p)))) ^ i := by
      have hcd : q.coeff d = 1 := by rw [hddef]; exact hqm.coeff_natDegree
      rw [hQmap, Finset.sum_range_succ, hcd, Nat.sub_self, pow_zero]
      push_cast [C_1]
      ring
    have hπsum : π ∣ ∑ i ∈ Finset.range d, C ((q.coeff i : ZMod p)) * Bbar ^ (d - i) *
        (-(N.map (Int.castRingHom (ZMod p)))) ^ i := by
      refine Finset.dvd_sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      have : π ∣ Bbar ^ (d - i) := hπB.trans (dvd_pow_self Bbar (Nat.sub_ne_zero_of_lt hi))
      exact ((this.mul_left _).mul_right _)
    have hπpow : π ∣ (-(N.map (Int.castRingHom (ZMod p)))) ^ d := by
      have := dvd_sub hπQ hπsum
      rw [hsplit, add_sub_cancel_right] at this
      exact this
    have := hπirr.prime.dvd_of_dvd_pow hπpow
    rwa [dvd_neg] at this
  -- Step 8: change of splitting transfers π ∣ N̄ to π ∣ M̄
  obtain ⟨Pi, hPimap, _, hPimonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts π).mpr
      (Polynomial.map_surjective _ hsurj π)) hπmonic
  have hid : A * B + C (p : ℤ) * N = g * h + C (p : ℤ) * M := by
    linear_combination hf - hN
  have hπMN : π ∣ M.map (Int.castRingHom (ZMod p)) - N.map (Int.castRingHom (ZMod p)) := by
    have := map_dvd_map_sub_of_map_dvd hPimonic hid
      (hPimap ▸ (hπA.trans (dvd_of_eq hAmap.symm))) (hPimap ▸ (hπB.trans (dvd_of_eq hBmap.symm)))
      (hPimap ▸ hπg) (hPimap ▸ hπh)
    rwa [hPimap] at this
  have hπM : π ∣ M.map (Int.castRingHom (ZMod p)) := by
    have := dvd_add hπMN hπN
    rwa [sub_add_cancel] at this
  -- Step 9: contradiction with the Bézout certificate
  obtain ⟨u', v', w', hbez'⟩ := hbez
  apply hπirr.not_isUnit
  apply isUnit_of_dvd_one
  rw [← hbez']
  exact dvd_add (dvd_add (hπg.mul_left u') (hπh.mul_left v')) (hπM.mul_left w')

end RingOfIntegers
