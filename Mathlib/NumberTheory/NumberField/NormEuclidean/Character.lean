/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.NormEuclidean.Density
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Producing an `n`-th power residue by a character sum

To apply Heilbronn's criterion one needs to write `p = u q₁ + v q₂` with `q₁ ∤ u`, `q₂ ∤ v` and
`u q₁` an `n`-th power residue modulo `p`.  When `gcd (p - 1, n) = 1` every residue is an `n`-th
power and there is nothing to do; in general one has to *find* a suitable `u`, and this is done by
a character sum.

Let `ψ` be a Dirichlet character modulo `p` of order `g = gcd (p - 1, n)`, so that `ψ y = 1`
exactly when `y` is an `n`-th power residue.  For `1 ≤ k ≤ g` the sums `ψ ^ k` detect that
condition (`NumberField.sum_pow_apply_eq`), and summing over a set `S` of candidates `u` — in the
application, an arithmetic progression modulo `q₁ q₂ ^ 2` chosen so that `q₁ ∤ u` and so that
`q₂ ∤ v` — expresses the number of good `u` as a main term plus character sums attached to the `k`
with `ψ ^ k ≠ 1`.  If those are small the count is positive, and a good `u`
exists: this is `NumberField.exists_apply_eq_one_of_lt_card`.

Such a `ψ` always exists, and this is proved here: `(ZMod p)ˣ` is cyclic of order `p - 1`, so it
embeds in `ℂˣ` by a faithful character `f`, and the `(p - 1) / g`-th power of `f` is a character
whose kernel is the group of `n`-th powers.

## Main results

* `NumberField.sum_pow_apply_eq`: `∑_{k=1}^{g} ψ^k x` is `g` if `ψ x = 1` and `0` otherwise.
* `NumberField.exists_apply_eq_one_of_lt_card`: if the character sums over `S` attached to the
  non-principal `ψ ^ k` are bounded by `B`, and the number of `u ∈ S` with `q₁ u` invertible
  exceeds `(g - 1) B`, then some `u ∈ S` has `ψ (q₁ u) = 1`.
* `NumberField.exists_dirichletCharacter_pow_residues`: existence of the detecting character.
* `NumberField.not_normEuclidean_of_charSum`: the criterion, given a detecting character and a
  bound for the character sums.
* `NumberField.not_normEuclidean_of_forall_charSum`: the same with no hypothesis on `ψ` at all,
  the character being produced rather than assumed.

## References

The character-sum argument is the one sketched in the final section of [Hibbler, McGown,
Treviño, *Polynomial densities and Heilbronn's criterion*][hibbler_mcgown_trevino2025]; the
character sums themselves are bounded by the inequality of [Pólya, *Über die Verteilung der
quadratischen Reste und Nichtreste*][polya1918] and [Vinogradov, *Sur la distribution des résidus
et des non-résidus des puissances*][vinogradov1918], proved in
`Mathlib/NumberTheory/DirichletCharacter/PolyaVinogradov.lean`.
-/

public section

open Finset

namespace NumberField

set_option linter.style.haveILetI false

/-- The sum of `ψ ^ k (x)` over `1 ≤ k ≤ g`, for a character `ψ` with `ψ ^ g = 1`, detects
`ψ x = 1`. -/
theorem sum_pow_apply_eq {p g : ℕ} [NeZero p] (hg : 0 < g) (ψ : DirichletCharacter ℂ p)
    (hψg : ψ ^ g = 1) (x : ZMod p) :
    ∑ k ∈ Finset.Icc 1 g, (ψ ^ k) x = if ψ x = 1 then (g : ℂ) else 0 := by
  by_cases hx : IsUnit x
  · set z := ψ x with hz
    have hzg : z ^ g = 1 := by
      have h1 : (ψ ^ g) x = z ^ g := MulChar.pow_apply' ψ hg.ne' x
      rw [hψg, MulChar.one_apply hx] at h1
      exact h1.symm
    have hterm : ∀ k ∈ Finset.Icc 1 g, (ψ ^ k) x = z ^ k := by
      intro k hk
      exact MulChar.pow_apply' ψ (by simp only [Finset.mem_Icc] at hk; omega) x
    rw [Finset.sum_congr rfl hterm]
    by_cases hz1 : z = 1
    · simp [hz1, Nat.card_Icc]
    · have hIco : Finset.Icc 1 g = Finset.Ico 1 (g + 1) := (Finset.val_inj.mp rfl).symm
      rw [hIco, Finset.sum_Ico_eq_sub _ (by omega), geom_sum_eq hz1, geom_sum_eq hz1]
      have hzz : z ^ (g + 1) = z := by rw [pow_succ, hzg, one_mul]
      have hz10 : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      rw [hzz, pow_one, div_self hz10, sub_self]
      simp only [hz1, ite_false]
  · have h0 : ∀ k ∈ Finset.Icc 1 g, (ψ ^ k) x = 0 := by
      intro k _
      exact MulChar.map_nonunit _ hx
    have hne1 : ¬ (ψ x = 1) := by
      rw [MulChar.map_nonunit ψ hx]
      exact zero_ne_one
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    simp only [hne1, ite_false]

open scoped Classical in
/-- **The character-sum count.**  Let `ψ` be a Dirichlet character mod `p` with `ψ ^ g = 1`, and
let `S` be any finite set of natural numbers — in the application, the `u < p / q₁` lying in a
fixed class modulo `q₂ ^ 2` and prime to `q₁`.  If every character sum `∑_{u ∈ S} ψ^k (q₁ u)` with
`ψ ^ k ≠ 1` is bounded by `B`, and the number of `u ∈ S` with `q₁ u` invertible mod `p` exceeds
`(g - 1) B`, then some `u ∈ S` has `ψ (q₁ u) = 1`, that is, `q₁ u` is an `n`-th power residue.

The hypothesis `hPV` is what the Pólya–Vinogradov inequality supplies: the sum of a non-principal
character over an interval, restricted to an arithmetic progression, is `O(√M log M)`. -/
theorem exists_apply_eq_one_of_lt_card {p q₁ g : ℕ} [NeZero p] (hg : 0 < g)
    (ψ : DirichletCharacter ℂ p) (hψg : ψ ^ g = 1) (S : Finset ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hPV : ∀ k ∈ Finset.Icc 1 g, ψ ^ k ≠ 1 →
      ‖∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ B)
    (hmain : ((g : ℝ) - 1) * B <
      #{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))}) :
    ∃ u ∈ S, ψ ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  -- with no good `u`, the double sum vanishes
  have hzero : ∑ u ∈ S, ∑ k ∈ Finset.Icc 1 g, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [sum_pow_apply_eq hg ψ hψg]
    simp only [hcon u hu, ite_false]
  -- the same double sum, summed the other way, splits off the terms with `ψ ^ k = 1`
  rw [Finset.sum_comm] at hzero
  have hsplit : ∑ k ∈ Finset.Icc 1 g, ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))
      = (∑ k ∈ {k ∈ Finset.Icc 1 g | ψ ^ k = 1},
            ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)))
        + ∑ k ∈ {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1},
            ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- each principal term is the main term
  have hprin : ∀ k ∈ {k ∈ Finset.Icc 1 g | ψ ^ k = 1},
      ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))
        = (#{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))} : ℂ) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2, Finset.sum_congr rfl (fun u _ => rfl)]
    rw [← Finset.sum_filter_add_sum_filter_not S
      (fun u => IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)))]
    rw [Finset.sum_congr rfl (fun u hu => MulChar.one_apply (Finset.mem_filter.1 hu).2),
      Finset.sum_congr rfl (fun u hu =>
        MulChar.map_nonunit (1 : DirichletCharacter ℂ p) (Finset.mem_filter.1 hu).2)]
    simp
  -- there is at least one principal term, and at most `g - 1` others
  have hone : (1 : ℕ) ≤ #{k ∈ Finset.Icc 1 g | ψ ^ k = 1} := by
    refine Finset.card_pos.2 ⟨g, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hg, le_refl g⟩, hψg⟩
  have hcard : #{k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} ≤ g - 1 := by
    have hsub : {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} ⊆ (Finset.Icc 1 g).erase g := by
      intro k hk
      rw [Finset.mem_filter] at hk
      exact Finset.mem_erase.2 ⟨fun h => hk.2 (h ▸ hψg), hk.1⟩
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_erase_of_mem (Finset.mem_Icc.2 ⟨hg, le_refl g⟩), Nat.card_Icc]
    omega
  -- bound the non-principal part
  have hbound : ‖∑ k ∈ {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1},
      ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ ((g : ℝ) - 1) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ B (fun k hk => ?_)) ?_
    · rw [Finset.mem_filter] at hk
      exact hPV k hk.1 hk.2
    · rw [nsmul_eq_mul]
      have hle : (#{k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} : ℝ) ≤ (g : ℝ) - 1 := by
        have h1 : (#{k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1} : ℝ) ≤ ((g - 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
        have h2 : ((g - 1 : ℕ) : ℝ) ≤ (g : ℝ) - 1 := by
          have : 1 ≤ g := hg
          push_cast [Nat.cast_sub this]
          linarith
        linarith
      nlinarith
  -- put it together
  rw [hsplit, Finset.sum_congr rfl hprin, Finset.sum_const, nsmul_eq_mul] at hzero
  set M : ℝ := (#{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))} : ℝ) with hM
  have hMle : M ≤ ((g : ℝ) - 1) * B := by
    have heq : ((#{k ∈ Finset.Icc 1 g | ψ ^ k = 1} : ℂ)) * (M : ℂ)
        = -∑ k ∈ {k ∈ Finset.Icc 1 g | ¬ ψ ^ k = 1},
            ∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) := by
      rw [hM]
      push_cast at hzero ⊢
      linear_combination hzero
    have hnorm : ‖((#{k ∈ Finset.Icc 1 g | ψ ^ k = 1} : ℂ)) * (M : ℂ)‖ ≤ ((g : ℝ) - 1) * B := by
      rw [heq, norm_neg]
      exact hbound
    rw [norm_mul] at hnorm
    have h1 : (1 : ℝ) ≤ ‖((#{k ∈ Finset.Icc 1 g | ψ ^ k = 1} : ℂ))‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast hone
    have h2 : ‖(M : ℂ)‖ = M := by
      rw [hM]
      push_cast
      simp
    rw [h2] at hnorm
    nlinarith [hnorm, h1, Nat.cast_nonneg (α := ℝ)
      (#{u ∈ S | IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))})]
  linarith [hmain, hMle]

/-- **Existence of the detecting character.**  For `p` prime there is a Dirichlet character `ψ`
modulo `p` with `ψ ^ gcd (p - 1, n) = 1` whose value `1` characterises the `n`-th power residues.

The group `(ZMod p)ˣ` is cyclic of order `N = p - 1`, hence isomorphic to the group of `N`-th
roots of unity in `ℂˣ`; composing such an isomorphism with the inclusion gives a faithful
character `f`, and `ψ = f ^ (N / g)` has kernel the `n`-th powers. -/
theorem exists_dirichletCharacter_pow_residues (p n : ℕ) (hp : p.Prime) :
    ∃ ψ : DirichletCharacter ℂ p, ψ ^ Nat.gcd (p - 1) n = 1 ∧
      ∀ y : ZMod p, ψ y = 1 → ∃ x : ZMod p, x ^ n = y := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N := p - 1 with hNdef
  have hN : 0 < N := by have := hp.one_lt; omega
  have hcard : Nat.card (ZMod p)ˣ = N := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  haveI : NeZero ((N : ℕ) : ℂ) := ⟨by exact_mod_cast hN.ne'⟩
  -- a primitive `N`-th root of unity in `ℂˣ`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ N
  set ω : ℂˣ := (hζ.isUnit hN.ne').unit with hωdef
  have hω : IsPrimitiveRoot ω N := hζ.isUnit_unit hN.ne'
  have hordω : orderOf ω = N := hω.eq_orderOf.symm
  -- a faithful character of `(ZMod p)ˣ`
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  have hcards : Nat.card (ZMod p)ˣ = Nat.card (Subgroup.zpowers ω) := by
    rw [hcard, Nat.card_zpowers, hordω]
  set e := mulEquivOfCyclicCardEq hcards with hedef
  set f : (ZMod p)ˣ →* ℂˣ := (Subgroup.zpowers ω).subtype.comp e.toMonoidHom with hfdef
  have hfinj : Function.Injective f := fun a b hab => e.injective (Subtype.val_injective hab)
  -- the character
  set d := Nat.gcd N n with hddef
  have hdN : d ∣ N := Nat.gcd_dvd_left _ _
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hN
  set k := N / d with hkdef
  have hkd : k * d = N := Nat.div_mul_cancel hdN
  refine ⟨(MulChar.ofUnitHom f) ^ k, ?_, ?_⟩
  · rw [← pow_mul, hkd]
    refine MulChar.ext fun a => ?_
    rw [MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MulChar.one_apply_coe]
    have h1 : (f a) ^ N = 1 := by rw [← map_pow, ← hcard, pow_card_eq_one', map_one]
    calc ((f a : ℂ)) ^ N = ((f a ^ N : ℂˣ) : ℂ) := by push_cast; ring
      _ = 1 := by rw [h1]; rfl
  · intro y hy
    by_cases hyu : IsUnit y
    · obtain ⟨u, rfl⟩ := hyu
      rw [MulChar.pow_apply_coe, MulChar.ofUnitHom_coe] at hy
      have hu : u ^ k = 1 := by
        refine hfinj ?_
        rw [map_pow, map_one]
        refine Units.val_injective ?_
        push_cast
        exact hy
      obtain ⟨x, hx⟩ : ∃ x : (ZMod p)ˣ, x ^ n = u := by
        refine IsCyclic.exists_pow_eq_of_pow_natCard_div_gcd ?_
        rw [hcard, ← hddef, ← hkdef]
        exact hu
      exact ⟨(x : ZMod p), by rw [← Units.val_pow_eq_pow_val, hx]⟩
    · rw [MulChar.map_nonunit _ hyu] at hy
      exact absurd hy zero_ne_one

open scoped Classical in
/-- **The criterion, assembled.**  Let `f` satisfy the Eisenstein–Dumas condition at `p` of slope
`m / n`, and suppose `f` has no root modulo two primes `q₁ ≠ q₂`, both different from `p`.  Let
`ψ` be a Dirichlet character mod `p` with `ψ ^ g = 1` whose value `1` characterises the `n`-th
power residues, and let `r₀` be a residue with `r₀ q₁ ≡ p + q₁ q₂ (mod q₂ ^ 2)`.  Let `S` be any
set of candidates `u`, each `< p / q₁`, prime to `q₁` and congruent to `r₀` modulo `q₂ ^ 2`.  If
the character sums over `S` attached to the non-principal `ψ ^ k` are bounded by `B`, and
`#S > (g - 1) B`, then the field generated by a root of `f` is not norm-Euclidean.

No hypothesis on `gcd (p - 1, n)` is needed: the character sum produces the `n`-th power residue
that the criterion requires. -/
theorem not_normEuclidean_of_charSum {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
    {n m p q₁ q₂ g r₀ : ℕ} {a : ℕ → ℤ} {cc : ℕ → ℕ}
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i ∈ Finset.range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
    (hc : ∀ i < n, m * (n - i) ≤ n * cc i) (hdvd : ∀ i < n, (p : ℤ) ^ cc i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hq₁q₂ : ¬ (q₂ : ℤ) ∣ (q₁ : ℤ)) (hq₁p : q₁ ≠ p)
    (hr₁ : ∀ r : ZMod q₁, Polynomial.eval₂ (Int.castRingHom (ZMod q₁)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hr₂ : ∀ r : ZMod q₂, Polynomial.eval₂ (Int.castRingHom (ZMod q₂)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hg : 0 < g) (ψ : DirichletCharacter ℂ p) (hψg : ψ ^ g = 1)
    (hψres : ∀ y : ZMod p, ψ y = 1 → ∃ x : ZMod p, x ^ n = y)
    (hr₀ : ((r₀ * q₁ : ℕ) : ZMod (q₂ ^ 2)) = ((p + q₁ * q₂ : ℕ) : ZMod (q₂ ^ 2)))
    (S : Finset ℕ) (hSlt : ∀ u ∈ S, u < p / q₁) (hSnd : ∀ u ∈ S, ¬ q₁ ∣ u)
    (hScong : ∀ u ∈ S, ((u : ℕ) : ZMod (q₂ ^ 2)) = ((r₀ : ℕ) : ZMod (q₂ ^ 2)))
    {B : ℝ} (hB : 0 ≤ B)
    (hPV : ∀ k ∈ Finset.Icc 1 g, ψ ^ k ≠ 1 →
      ‖∑ u ∈ S, (ψ ^ k) ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ B)
    (hmain : ((g : ℝ) - 1) * B < #S) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : NeZero (q₂ ^ 2) := ⟨pow_ne_zero 2 hq₂.pos.ne'⟩
  -- every candidate is prime to `p`, so `q₁ u` is invertible and the count is all of `S`
  have hall : ∀ u ∈ S, IsUnit ((q₁ : ZMod p) * ((u : ℕ) : ZMod p)) := by
    intro u hu
    have hupos : 0 < u := by
      rcases Nat.eq_zero_or_pos u with rfl | h
      · exact absurd (dvd_zero q₁) (hSnd 0 hu)
      · exact h
    have hup : u < p := lt_of_lt_of_le (hSlt u hu) (Nat.div_le_self p q₁)
    have hcop : Nat.Coprime (q₁ * u) p :=
      Nat.coprime_mul_iff_left.2 ⟨(Nat.coprime_primes hq₁ hp).2 hq₁p,
        (hp.coprime_iff_not_dvd.2 fun h => absurd (Nat.le_of_dvd hupos h) (not_le.2 hup)).symm⟩
    have h := (ZMod.isUnit_iff_coprime (q₁ * u) p).2 hcop
    rwa [Nat.cast_mul] at h
  -- the character sum produces a `u`
  obtain ⟨u, huS, huψ⟩ := exists_apply_eq_one_of_lt_card hg ψ hψg S hB hPV
    (by rw [Finset.filter_true_of_mem hall]; exact hmain)
  have huN := hSlt u huS
  have hqu := hSnd u huS
  have hucong := hScong u huS
  -- `u q₁ < p`
  have hult : u * q₁ < p := by
    have h1 : u + 1 ≤ p / q₁ := huN
    have h2 : (u + 1) * q₁ ≤ (p / q₁) * q₁ := Nat.mul_le_mul_right _ h1
    have h3 : (p / q₁) * q₁ ≤ p := Nat.div_mul_le_self p q₁
    have h4 : 0 < q₁ := hq₁.pos
    calc u * q₁ < (u + 1) * q₁ := by
          have h5 : u * q₁ + 0 < u * q₁ + q₁ := by omega
          calc u * q₁ = u * q₁ + 0 := by ring
            _ < u * q₁ + q₁ := h5
            _ = (u + 1) * q₁ := by ring
      _ ≤ p := le_trans h2 h3
  -- the congruence forcing `q₂ ∤ v`
  have hcong : ((u * q₁ : ℕ) : ℤ) ≡ (p : ℤ) + (q₁ : ℤ) * q₂ [ZMOD ((q₂ : ℤ) ^ 2)] := by
    have h0 := hr₀
    push_cast at h0
    set z : ℤ := (p : ℤ) + (q₁ : ℤ) * (q₂ : ℤ) - ((u * q₁ : ℕ) : ℤ) with hzdef
    have hz : ((z : ℤ) : ZMod (q₂ ^ 2)) = 0 := by
      rw [hzdef]
      push_cast
      rw [hucong, h0]
      ring
    have hdvd2 := (ZMod.intCast_zmod_eq_zero_iff_dvd z (q₂ ^ 2)).1 hz
    have hcast : (((q₂ ^ 2 : ℕ) : ℤ)) = ((q₂ : ℤ) ^ 2) := by push_cast; ring
    rw [hcast] at hdvd2
    rw [Int.modEq_iff_dvd]
    exact hdvd2
  obtain ⟨v, hv0, hpuv, hqv⟩ := exists_rep_of_congr hq₂.one_lt hq₁q₂ hult hcong
  -- the power residue
  have hres : ∃ x : ℤ, (p : ℤ) ∣ x ^ n - ((u * q₁ : ℕ) : ℤ) := by
    obtain ⟨x, hx⟩ := hψres _ huψ
    refine ⟨(x.val : ℤ), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, sub_eq_zero, hx]
    ring
  -- Heilbronn's criterion
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · exact absurd (dvd_zero q₁) hqu
    · exact h
  exact not_normEuclidean_of_eisensteinDumas_of_isPow hp hn hm hmn
    ⟨hu0, hv0, hpuv, hqu, hqv⟩ hres hdeg hroot hc hdvd hnd hq₁ hq₂ hr₁ hr₂

open scoped Classical in
/-- **The criterion with no hypothesis on the character.**  Same as
`not_normEuclidean_of_charSum`,
but with the detecting character produced rather than assumed: the only analytic input left is
the bound `hPV`, quantified over *all* non-principal characters modulo `p`, which is precisely
the shape in which the Pólya–Vinogradov inequality is applied. -/
theorem not_normEuclidean_of_forall_charSum {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
    {n m p q₁ q₂ r₀ : ℕ} {a : ℕ → ℤ} {cc : ℕ → ℕ}
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i ∈ Finset.range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
    (hc : ∀ i < n, m * (n - i) ≤ n * cc i) (hdvd : ∀ i < n, (p : ℤ) ^ cc i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hq₁q₂ : ¬ (q₂ : ℤ) ∣ (q₁ : ℤ)) (hq₁p : q₁ ≠ p)
    (hr₁ : ∀ r : ZMod q₁, Polynomial.eval₂ (Int.castRingHom (ZMod q₁)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hr₂ : ∀ r : ZMod q₂, Polynomial.eval₂ (Int.castRingHom (ZMod q₂)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hr₀ : ((r₀ * q₁ : ℕ) : ZMod (q₂ ^ 2)) = ((p + q₁ * q₂ : ℕ) : ZMod (q₂ ^ 2)))
    (S : Finset ℕ) (hSlt : ∀ u ∈ S, u < p / q₁) (hSnd : ∀ u ∈ S, ¬ q₁ ∣ u)
    (hScong : ∀ u ∈ S, ((u : ℕ) : ZMod (q₂ ^ 2)) = ((r₀ : ℕ) : ZMod (q₂ ^ 2)))
    {B : ℝ} (hB : 0 ≤ B)
    (hPV : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      ‖∑ u ∈ S, χ ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ B)
    (hmain : ((Nat.gcd (p - 1) n : ℝ) - 1) * B < #S) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : NeZero (q₂ ^ 2) := ⟨pow_ne_zero 2 hq₂.pos.ne'⟩
  obtain ⟨ψ, hψg, hψres⟩ := exists_dirichletCharacter_pow_residues p n hp
  exact not_normEuclidean_of_charSum hp hn hm hmn hdeg hroot hc hdvd hnd hq₁ hq₂ hq₁q₂ hq₁p
    hr₁ hr₂ (Nat.gcd_pos_of_pos_right _ hn) ψ hψg hψres hr₀ S hSlt hSnd hScong hB
    (fun k _ hk => hPV (ψ ^ k) hk) hmain

/-- The residue `r₀` required by `not_normEuclidean_of_charSum` always exists: `q₁` is invertible
modulo `q₂ ^ 2` whenever `q₁` and `q₂` are distinct primes. -/
theorem exists_residue_mul_eq {p q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hne : q₁ ≠ q₂) :
    ∃ r₀ : ℕ, ((r₀ * q₁ : ℕ) : ZMod (q₂ ^ 2)) = ((p + q₁ * q₂ : ℕ) : ZMod (q₂ ^ 2)) := by
  have : NeZero (q₂ ^ 2) := ⟨pow_ne_zero 2 hq₂.pos.ne'⟩
  have hcop : Nat.Coprime q₁ (q₂ ^ 2) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hq₁ hq₂).2 hne)
  have hunit : IsUnit ((q₁ : ZMod (q₂ ^ 2))) := (ZMod.isUnit_iff_coprime q₁ (q₂ ^ 2)).2 hcop
  obtain ⟨w, hw⟩ := hunit
  refine ⟨(((p + q₁ * q₂ : ℕ) : ZMod (q₂ ^ 2)) * (↑w⁻¹ : ZMod (q₂ ^ 2))).val, ?_⟩
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, ← hw, mul_assoc]
  simp

end NumberField
