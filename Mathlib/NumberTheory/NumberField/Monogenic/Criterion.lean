/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Dedekind
public import Mathlib.NumberTheory.NumberField.Monogenic.Pure

/-!
# The local criterion for `p`-maximality, as an equivalence

Let `K` be a number field, `θ : 𝓞 K` a generator of `K` over `ℚ` with minimal polynomial
`f` over `ℤ`, and `p` a rational prime.  Call a decomposition `f = g * h + p * M` in
`ℤ[X]` *admissible* when `g` and `h` are monic with `deg g + deg h = deg f`.

The two halves of the criterion are:

* `RingOfIntegers.dvd_exponent_of_sq_factor` (the obstruction): a decomposition
  `f = h ^ 2 * g + p * (k * h) + p ^ 2 * t` with `h * g` monic of degree `< deg f` forces
  `p ∣ exponent θ`;
* `RingOfIntegers.not_dvd_exponent_of_bezout` (the certificate): for an admissible
  splitting with `ḡ` squarefree and every irreducible factor of `h̄` dividing `ḡ`, a Bézout
  relation `u ḡ + v h̄ + w M̄ = 1` in `𝔽_p[X]` forces `p ∤ exponent θ`.

This file supplies the missing link between them and deduces that the criterion is
*complete*, not merely sufficient.

## Main results

* `RingOfIntegers.dvd_exponent_of_common_factor`: if some monic `Π` of positive degree
  divides `ḡ`, `h̄` and `M̄` for an admissible splitting, then `p ∣ exponent θ`.  This is
  the converse of the certificate half: lifting the three divisibilities turns the
  splitting into the obstruction shape, with `Π` in the role of the repeated factor.

* `RingOfIntegers.not_dvd_exponent_iff_bezout`: for an admissible splitting satisfying the
  hypotheses of the certificate half, `p ∤ exponent θ` **if and only if** a Bézout relation
  exists.  Consequently exactly one of the two hypotheses can be arranged at each prime,
  and the criterion decides `p`-maximality.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
variable {p : ℕ} [hp : Fact p.Prime]

private theorem map_zmod_eq_zero_iff' {q : ℤ[X]} :
    q.map (Int.castRingHom (ZMod p)) = 0 ↔ C (p : ℤ) ∣ q := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun i => ?_
  rw [coeff_map, coeff_zero, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If a monic `P` divides a monic `G` modulo `p`, the quotient lifts to a monic
polynomial: `G = P * q + p * s` with `q` monic of complementary degree. -/
private theorem exists_monic_lift_of_map_dvd {P G : ℤ[X]} (hG : G.Monic) (hPm : P.Monic)
    (hdvd : P.map (Int.castRingHom (ZMod p)) ∣ G.map (Int.castRingHom (ZMod p))) :
    ∃ q s : ℤ[X], q.Monic ∧ q.natDegree + P.natDegree = G.natDegree ∧
      G = P * q + C (p : ℤ) * s := by
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  obtain ⟨qb, hqb⟩ := hdvd
  have hGb : (G.map (Int.castRingHom (ZMod p))).Monic := hG.map _
  have hPb : (P.map (Int.castRingHom (ZMod p))).Monic := hPm.map _
  have hqbm : qb.Monic := by
    rw [hqb] at hGb
    exact hPb.of_mul_monic_left hGb
  obtain ⟨q, hqmap, hqdeg, hqm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts qb).mpr (Polynomial.map_surjective _ hsurj qb)) hqbm
  have hzero : (G - P * q).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hqmap, ← hqb, sub_self]
  obtain ⟨s, hs⟩ := map_zmod_eq_zero_iff'.mp hzero
  refine ⟨q, s, hqm, ?_, by linear_combination hs⟩
  have h1 : q.natDegree = qb.natDegree := natDegree_eq_of_degree_eq hqdeg
  have h2 : (G.map (Int.castRingHom (ZMod p))).natDegree =
      (P.map (Int.castRingHom (ZMod p))).natDegree + qb.natDegree := by
    rw [hqb, hPb.natDegree_mul hqbm]
  rw [hG.natDegree_map, hPm.natDegree_map] at h2
  omega

/-- **Converse of the certificate half.**  Let `f = g * h + p * M` with `g`, `h` monic and
`deg g + deg h = deg f`.  If a monic polynomial `Π` of positive degree divides each of
`ḡ`, `h̄`, `M̄` in `𝔽_p[X]`, then `p` divides the exponent of `θ`.

Lifting the three divisibilities as `g = Π q + p s`, `h = Π u + p v` and `M = Π m₁ + p m₂`
turns the splitting into
`f = Π ^ 2 (q u) + p Π (q v + s u + m₁) + p ^ 2 (s v + m₂)`,
which is the shape required by the obstruction lemma; `Π * (q * u)` is monic of degree
`deg f - deg Π < deg f`. -/
theorem dvd_exponent_of_common_factor {g h M Pi : ℤ[X]}
    (hf : minpoly ℤ θ = g * h + C (p : ℤ) * M)
    (hgm : g.Monic) (hhm : h.Monic)
    (hdeg : g.natDegree + h.natDegree = (minpoly ℤ θ).natDegree)
    (hPim : Pi.Monic) (hPideg : 0 < Pi.natDegree)
    (hPig : Pi.map (Int.castRingHom (ZMod p)) ∣ g.map (Int.castRingHom (ZMod p)))
    (hPih : Pi.map (Int.castRingHom (ZMod p)) ∣ h.map (Int.castRingHom (ZMod p)))
    (hPiM : Pi.map (Int.castRingHom (ZMod p)) ∣ M.map (Int.castRingHom (ZMod p))) :
    p ∣ exponent θ := by
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  obtain ⟨q, s, hqm, hqdeg, hgeq⟩ := exists_monic_lift_of_map_dvd hgm hPim hPig
  obtain ⟨u, v, hum, hudeg, hheq⟩ := exists_monic_lift_of_map_dvd hhm hPim hPih
  obtain ⟨mb, hmb⟩ := hPiM
  obtain ⟨m₁, hm₁⟩ := Polynomial.map_surjective _ hsurj mb
  have hzero : (M - Pi * m₁).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hm₁, ← hmb, sub_self]
  obtain ⟨m₂, hm₂⟩ := map_zmod_eq_zero_iff'.mp hzero
  have hMeq : M = Pi * m₁ + C (p : ℤ) * m₂ := by linear_combination hm₂
  refine dvd_exponent_of_sq_factor (h := Pi) (g := q * u)
    (k := q * v + s * u + m₁) (t := s * v + m₂) (hPim.mul (hqm.mul hum)) ?_ ?_
  · rw [hPim.natDegree_mul (hqm.mul hum), hqm.natDegree_mul hum]
    omega
  · rw [hf, hgeq, hheq, hMeq]
    ring

/-- **Completeness of the local criterion.**  For an admissible splitting
`f = g * h + p * M` with `ḡ` squarefree and every irreducible factor of `h̄` dividing `ḡ`,
the prime `p` fails to divide the exponent of `θ` *if and only if* `ḡ`, `h̄` and `M̄`
generate the unit ideal of `𝔽_p[X]`.

Together with `dvd_exponent_of_common_factor` this shows that at each prime exactly one of
the two hypotheses of the criterion can be arranged: either a Bézout relation exists, and
then `p ∤ exponent θ`, or the three reductions share an irreducible factor, and then
`p ∣ exponent θ`. -/
theorem not_dvd_exponent_iff_bezout (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {g h M : ℤ[X]} (hf : minpoly ℤ θ = g * h + C (p : ℤ) * M)
    (hgm : g.Monic) (hhm : h.Monic)
    (hdeg : g.natDegree + h.natDegree = (minpoly ℤ θ).natDegree)
    (hsq : Squarefree (g.map (Int.castRingHom (ZMod p))))
    (hrad : ∀ q : (ZMod p)[X], Irreducible q → q ∣ h.map (Int.castRingHom (ZMod p)) →
      q ∣ g.map (Int.castRingHom (ZMod p))) :
    ¬ p ∣ exponent θ ↔ ∃ u v w : (ZMod p)[X],
      u * g.map (Int.castRingHom (ZMod p)) + v * h.map (Int.castRingHom (ZMod p)) +
        w * M.map (Int.castRingHom (ZMod p)) = 1 := by
  classical
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  refine ⟨fun hnd => ?_, not_dvd_exponent_of_bezout hθ hf hsq hrad⟩
  by_contra hbez
  refine hnd ?_
  have hgb0 : g.map (Int.castRingHom (ZMod p)) ≠ 0 := (hgm.map _).ne_zero
  -- the gcd of the three reductions
  have hd0 : EuclideanDomain.gcd (EuclideanDomain.gcd (g.map (Int.castRingHom (ZMod p)))
      (h.map (Int.castRingHom (ZMod p)))) (M.map (Int.castRingHom (ZMod p))) ≠ 0 := by
    intro h0
    rw [EuclideanDomain.gcd_eq_zero_iff] at h0
    rw [EuclideanDomain.gcd_eq_zero_iff] at h0
    exact hgb0 h0.1.1
  by_cases hdu : IsUnit (EuclideanDomain.gcd (EuclideanDomain.gcd
      (g.map (Int.castRingHom (ZMod p))) (h.map (Int.castRingHom (ZMod p))))
      (M.map (Int.castRingHom (ZMod p))))
  · -- a unit gcd produces the Bézout relation, contradicting `hbez`
    exfalso
    apply hbez
    obtain ⟨c, hc⟩ := hdu.exists_right_inv
    have e2 := EuclideanDomain.gcd_eq_gcd_ab (g.map (Int.castRingHom (ZMod p)))
      (h.map (Int.castRingHom (ZMod p)))
    have e1 := EuclideanDomain.gcd_eq_gcd_ab (EuclideanDomain.gcd
      (g.map (Int.castRingHom (ZMod p))) (h.map (Int.castRingHom (ZMod p))))
      (M.map (Int.castRingHom (ZMod p)))
    exact ⟨(EuclideanDomain.gcdA (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p))) *
            EuclideanDomain.gcdA (EuclideanDomain.gcd (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p)))) (M.map (Int.castRingHom (ZMod p)))) * c,
           (EuclideanDomain.gcdB (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p))) *
            EuclideanDomain.gcdA (EuclideanDomain.gcd (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p)))) (M.map (Int.castRingHom (ZMod p)))) * c,
           EuclideanDomain.gcdB (EuclideanDomain.gcd (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p)))) (M.map (Int.castRingHom (ZMod p))) * c,
           by linear_combination hc - c * e1 - (c * EuclideanDomain.gcdA
             (EuclideanDomain.gcd (g.map (Int.castRingHom (ZMod p)))
               (h.map (Int.castRingHom (ZMod p)))) (M.map (Int.castRingHom (ZMod p)))) * e2⟩
  · -- otherwise the three reductions share an irreducible factor
    obtain ⟨π, hπirr, hπd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
    have hπd₁ : π ∣ EuclideanDomain.gcd (g.map (Int.castRingHom (ZMod p)))
        (h.map (Int.castRingHom (ZMod p))) := hπd.trans (EuclideanDomain.gcd_dvd_left _ _)
    have hπg : π ∣ g.map (Int.castRingHom (ZMod p)) :=
      hπd₁.trans (EuclideanDomain.gcd_dvd_left _ _)
    have hπh : π ∣ h.map (Int.castRingHom (ZMod p)) :=
      hπd₁.trans (EuclideanDomain.gcd_dvd_right _ _)
    have hπM : π ∣ M.map (Int.castRingHom (ZMod p)) :=
      hπd.trans (EuclideanDomain.gcd_dvd_right _ _)
    -- normalise to a monic irreducible and lift it
    have hπbmonic : (normalize π).Monic := monic_normalize hπirr.ne_zero
    have hπbirr : Irreducible (normalize π) := (associated_normalize π).irreducible hπirr
    obtain ⟨Pi, hPimap, hPidegeq, hPim⟩ := lifts_and_degree_eq_and_monic
      ((mem_lifts (normalize π)).mpr (Polynomial.map_surjective _ hsurj (normalize π)))
      hπbmonic
    have hPideg : 0 < Pi.natDegree := by
      have hb : 0 < (normalize π).natDegree := by
        rcases Nat.eq_zero_or_pos (normalize π).natDegree with h0 | hpos
        · rw [eq_one_of_monic_natDegree_zero hπbmonic h0] at hπbirr
          exact absurd hπbirr not_irreducible_one
        · exact hpos
      rwa [natDegree_eq_of_degree_eq hPidegeq]
    refine dvd_exponent_of_common_factor hf hgm hhm hdeg hPim hPideg ?_ ?_ ?_
    · rw [hPimap, normalize_dvd_iff]; exact hπg
    · rw [hPimap, normalize_dvd_iff]; exact hπh
    · rw [hPimap, normalize_dvd_iff]; exact hπM

end RingOfIntegers

end

end
