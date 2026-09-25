/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Padic.Core

/-!
# The choice of parameters for the `p`-adic Baker theorem

The parameters of `PadicBaker.core` are powers of `X = 2 ^ t`:
`h = X ^ (3 k + 7)`, `L = X ^ (6 k + 11)`, `R J = X ^ (3 k + 7 + J)` and
`S J = 2 ^ (kmax k - J) * X ^ (6 k + 13)`, for `J ≤ kmax k = (2 k + 3) (3 k + 7)`.
Each side of the inequalities `hext` and `hfin` of `PadicBaker.core` is a power of `r₀`, and
every factor of the left side is at most `r₀ ^ (c * Y)` with `c` independent of `t`, while the
right side is `r₀ ^ (X * Y)` (`PadicBaker.SizeLe`). Once `X` exceeds the sum of the `c`, the
inequalities hold.
-/

@[expose] public section

namespace PadicBaker

/-- The number of extrapolation steps in the `p`-adic Baker theorem for `k + 1` logarithms. -/
def kmax (k : ℕ) : ℕ := (2 * k + 3) * (3 * k + 7)

theorem mul_le_kmax (k : ℕ) : (6 * k + 11) * (k + 3) ≤ 9 * k + 19 + kmax k := by
  unfold kmax; nlinarith

theorem pow_le_pow_mul_of_le {r₀ a : ℝ} {m : ℕ} (ha : 0 ≤ a) (h : a ≤ r₀ ^ m) (x : ℕ) :
    a ^ x ≤ r₀ ^ (m * x) := by
  rw [pow_mul]; exact pow_le_pow_left₀ ha h x

theorem cast_two_pow_pow_le {r₀ : ℝ} {e : ℕ} (h2e : (2 : ℝ) ≤ r₀ ^ e) (t a : ℕ) :
    (((2 ^ t) ^ a : ℕ) : ℝ) ≤ r₀ ^ (e * (t * a)) := by
  rw [← pow_mul]; push_cast; exact pow_le_pow_mul_of_le zero_le_two h2e _

section SizeLe

variable {r₀ x y : ℝ} {Y a b : ℕ}

/-- `x` is nonnegative and at most `r₀ ^ (c * Y)`: the bookkeeping of the sizes in the choice of
parameters. -/
def SizeLe (r₀ : ℝ) (Y c : ℕ) (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ r₀ ^ (c * Y)

theorem SizeLe.mul (hx : SizeLe r₀ Y a x) (hy : SizeLe r₀ Y b y) :
    SizeLe r₀ Y (a + b) (x * y) :=
  ⟨mul_nonneg hx.1 hy.1, by
    rw [add_mul, pow_add]; exact mul_le_mul hx.2 hy.2 hy.1 (hx.1.trans hx.2)⟩

theorem SizeLe.pow (hx : SizeLe r₀ Y a x) (n : ℕ) : SizeLe r₀ Y (a * n) (x ^ n) :=
  ⟨pow_nonneg hx.1 n, by
    rw [mul_right_comm]; exact pow_le_pow_mul_of_le hx.1 hx.2 n⟩

theorem SizeLe.of_le (hr₀ : 1 ≤ r₀) {E c : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ r₀ ^ E)
    (hE : E ≤ c * Y) : SizeLe r₀ Y c x :=
  ⟨hx0, hx.trans (pow_le_pow_right₀ hr₀ hE)⟩

theorem SizeLe.of_pow (hr₀ : 1 ≤ r₀) {E c n : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ r₀ ^ E)
    (hE : E * n ≤ c * Y) : SizeLe r₀ Y c (x ^ n) :=
  SizeLe.of_le hr₀ (pow_nonneg hx0 n) (pow_le_pow_mul_of_le hx0 hx n) hE

theorem SizeLe.lt (hr₀ : 1 < r₀) {c X : ℕ} (hx : SizeLe r₀ Y c x) (hY : 0 < Y) (hc : c < X) :
    x < r₀ ^ (X * Y) :=
  hx.2.trans_lt (pow_lt_pow_right₀ hr₀ (Nat.mul_lt_mul_of_pos_right hc hY))

end SizeLe

theorem one_le_two_pow_pow (t a : ℕ) : 1 ≤ (2 ^ t) ^ a := Nat.one_le_pow _ _ (by positivity)

/-- The parameters of `PadicBaker.core` exist. -/
theorem exists_parameters (k D p : ℕ) {r₀ B G C lmin : ℝ} (hr₀ : 1 < r₀) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hlmin0 : 0 < lmin) :
    ∃ (L h Kmax : ℕ) (S R : ℕ → ℕ), 1 ≤ L ∧ 1 ≤ h ∧
      2 * ((h ^ 2 + 1) ^ (k + 1) * h) ≤ (L + 1) ^ (k + 2) ∧
      S 0 ≤ h ^ 2 ∧ R 0 ≤ h ∧ (∀ J < Kmax, 2 * S (J + 1) ≤ S J) ∧
      (∀ J < Kmax, B ^ S (J + 1) * r₀ ^ L *
        ((L + 1) ^ (k + 2) * (C * ((L + 1) ^ (k + 2) * entryBound k L h G) *
          ((L + 1) * (R (J + 1) : ℝ) ^ L * (2 * L * G) ^ S (J + 1) *
            G ^ ((k + 1) * L * R (J + 1))))) ^ D <
        lmin ^ S (J + 1) * r₀ ^ (R J * S (J + 1))) ∧
      (C * ((L + 1) ^ (k + 2) * entryBound k L h G)) ^ D * (p : ℝ) ^ L *
        ((2 * G ^ ((k + 1) * L)) ^ D) ^ ((L + 1) ^ (k + 1) * (L + 1)) * r₀ ^ L <
        r₀ ^ (R Kmax * S Kmax) := by
  have hr₀1 := hr₀.le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hli0 : 0 ≤ lmin⁻¹ := inv_nonneg.mpr hlmin0.le
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (2 + B + G + C + p + lmin⁻¹) hr₀
  have h2e : (2 : ℝ) ≤ r₀ ^ e := by linarith
  have hBe : B ≤ r₀ ^ e := by linarith
  have hGe : G ≤ r₀ ^ e := by linarith
  have hCe : C ≤ r₀ ^ e := by linarith
  have hpe : (p : ℝ) ≤ r₀ ^ e := by linarith
  have hle : lmin⁻¹ ≤ r₀ ^ e := by linarith
  -- the constants
  set W := 6 * k + 13 + kmax k with hW
  set cEB := 2 * e * (k + 1) + (e * W + e * W + e * W * (k + 1) + e * (k + 1)) with hcEB
  set cPH := e + (e * W * (k + 2) + cEB) with hcPH
  set cHx := e * W * (k + 2) + (cPH + (e * W + e * W + e * W + e * (k + 1))) with hcHx
  set Q := e + 1 + cHx * D + e with hQ
  set Q' := cPH * D + e + e * (k + 2) * D * 2 ^ (k + 2) + 1 with hQ'
  set t := Q + Q' + kmax k + k + 2 with ht
  set X := 2 ^ t with hX
  have htX : t < X := Nat.lt_two_pow_self
  have hQX : Q < X := by omega
  have hQ'X : Q' < X := by omega
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hkX : 2 ^ (k + 2) ≤ X := Nat.pow_le_pow_right two_pos (by omega)
  have hkmaxX : 2 ^ kmax k ≤ X := Nat.pow_le_pow_right two_pos (by omega)
  set L := X ^ (6 * k + 11) with hL
  set h := X ^ (3 * k + 7) with hh
  have hL1 : 1 ≤ L := one_le_two_pow_pow _ _
  have hh1 : 1 ≤ h := one_le_two_pow_pow _ _
  have hXpow : ∀ a b, a ≤ b → X ^ a ≤ X ^ b := fun a b hab => Nat.pow_le_pow_right hX1 hab
  -- the quantities depending on `t` are at most `r₀ ^ V`
  set V := e * (t * W) with hV
  have hmono : ∀ E, E ≤ t * W → r₀ ^ (e * E) ≤ r₀ ^ V := fun E hE =>
    pow_le_pow_right₀ hr₀1 (Nat.mul_le_mul_left e hE)
  have htW : ∀ a, a ≤ W → t * a ≤ t * W := fun a ha => Nat.mul_le_mul_left t ha
  have ht1 : 1 ≤ t := by omega
  have h2L : 2 * (L : ℝ) ≤ r₀ ^ (e * (1 + t * (6 * k + 11))) := by
    rw [mul_add, mul_one, pow_add]
    exact mul_le_mul h2e (cast_two_pow_pow_le h2e _ _) (Nat.cast_nonneg _) (by positivity)
  have hLV : (L : ℝ) + 1 ≤ r₀ ^ V := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    refine le_trans (by linarith) (h2L.trans (hmono _ ?_))
    have := htW (6 * k + 12) (by omega)
    rw [show t * (6 * k + 12) = t * (6 * k + 11) + t by ring] at this
    omega
  have hhV : (h : ℝ) ≤ r₀ ^ V := (cast_two_pow_pow_le h2e _ _).trans (hmono _ (htW _ (by omega)))
  have hRV : ∀ J, J ≤ kmax k → ((X ^ (3 * k + 7 + J) : ℕ) : ℝ) ≤ r₀ ^ V := fun J hJ =>
    (cast_two_pow_pow_le h2e _ _).trans (hmono _ (htW _ (by omega)))
  have h2LGV : 2 * (L : ℝ) * G ≤ r₀ ^ V := by
    refine (mul_le_mul h2L hGe hG (by positivity)).trans ?_
    rw [← pow_add, show e * (1 + t * (6 * k + 11)) + e = e * (2 + t * (6 * k + 11)) by ring]
    refine hmono _ ?_
    have := htW (6 * k + 13) (by omega)
    rw [show t * (6 * k + 13) = t * (6 * k + 11) + 2 * t by ring] at this
    omega
  -- `entryBound` is at most `r₀ ^ (cEB * Y)`
  have hEB : ∀ Y, X ^ (9 * k + 18) ≤ Y → SizeLe r₀ Y cEB (entryBound k L h G) := by
    intro Y hY
    have htY : t ≤ Y := htX.le.trans ((Nat.le_self_pow (by omega) X).trans hY)
    have htLY : t * L ≤ Y := by
      calc t * L ≤ X * X ^ (6 * k + 11) := Nat.mul_le_mul_right _ htX.le
        _ = X ^ (6 * k + 12) := by ring
        _ ≤ Y := (hXpow _ _ (by omega)).trans hY
    have hth2Y : t * h ^ 2 ≤ Y := by
      calc t * h ^ 2 ≤ X * (X ^ (3 * k + 7)) ^ 2 := Nat.mul_le_mul_right _ htX.le
        _ = X ^ (6 * k + 15) := by ring
        _ ≤ Y := (hXpow _ _ (by omega)).trans hY
    have hh2Y : h ^ 2 ≤ Y := by
      calc h ^ 2 = X ^ (6 * k + 14) := by rw [hh]; ring
        _ ≤ Y := (hXpow _ _ (by omega)).trans hY
    have hLhY : L * h = X ^ (9 * k + 18) := by rw [hL, hh]; ring
    unfold entryBound
    refine SizeLe.mul (SizeLe.of_pow hr₀1 hG hGe ?_) (SizeLe.mul (SizeLe.mul (SizeLe.mul
      (SizeLe.of_le hr₀1 (by positivity) hLV ?_) (SizeLe.of_pow hr₀1 (Nat.cast_nonneg _) hhV ?_))
      (SizeLe.of_pow hr₀1 (by positivity) h2LGV ?_)) (SizeLe.of_pow hr₀1 hG hGe ?_))
    · calc e * ((k + 1) * h ^ 2 + (k + 1) * L * h) = e * (k + 1) * (h ^ 2 + L * h) := by ring
        _ ≤ e * (k + 1) * (Y + Y) := Nat.mul_le_mul_left _ (Nat.add_le_add hh2Y (hLhY ▸ hY))
        _ = 2 * e * (k + 1) * Y := by ring
    · calc V = e * W * t := by ring
        _ ≤ e * W * Y := Nat.mul_le_mul_left _ htY
    · calc V * L = e * W * (t * L) := by ring
        _ ≤ e * W * Y := Nat.mul_le_mul_left _ htLY
    · calc V * ((k + 1) * h ^ 2) = e * W * (k + 1) * (t * h ^ 2) := by ring
        _ ≤ e * W * (k + 1) * Y := Nat.mul_le_mul_left _ hth2Y
    · calc e * ((k + 1) * L * h) = e * (k + 1) * (L * h) := by ring
        _ ≤ e * (k + 1) * Y := Nat.mul_le_mul_left _ (hLhY ▸ hY)
  have hPH : ∀ Y, X ^ (9 * k + 18) ≤ Y →
      SizeLe r₀ Y cPH (C * (((L : ℝ) + 1) ^ (k + 2) * entryBound k L h G)) := by
    intro Y hY
    have htY : t ≤ Y := htX.le.trans ((Nat.le_self_pow (by omega) X).trans hY)
    have hY1 : 1 ≤ Y := ht1.trans htY
    refine SizeLe.mul (SizeLe.of_le hr₀1 hC hCe ?_)
      (SizeLe.mul (SizeLe.of_pow hr₀1 (by positivity) hLV ?_) (hEB Y hY))
    · simpa using Nat.mul_le_mul_left e hY1
    · calc V * (k + 2) = e * W * (k + 2) * t := by ring
        _ ≤ e * W * (k + 2) * Y := Nat.mul_le_mul_left _ htY
  clear_value t
  refine ⟨L, h, kmax k, fun J => 2 ^ (kmax k - J) * X ^ (6 * k + 13),
    fun J => X ^ (3 * k + 7 + J), hL1, hh1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the count of unknowns and equations
    calc 2 * ((h ^ 2 + 1) ^ (k + 1) * h) ≤ 2 * ((2 * h ^ 2) ^ (k + 1) * h) := by
          gcongr; nlinarith
      _ = 2 ^ (k + 2) * X ^ ((2 * k + 3) * (3 * k + 7)) := by rw [hh]; ring
      _ ≤ X * X ^ ((2 * k + 3) * (3 * k + 7)) := Nat.mul_le_mul_right _ hkX
      _ = L ^ (k + 2) := by rw [hL]; ring
      _ ≤ (L + 1) ^ (k + 2) := Nat.pow_le_pow_left (by omega) _
  · calc 2 ^ (kmax k - 0) * X ^ (6 * k + 13) ≤ X * X ^ (6 * k + 13) :=
          Nat.mul_le_mul_right _ (by simpa using hkmaxX)
      _ = h ^ 2 := by rw [hh]; ring
  · simp [hh]
  · intro J hJ
    rw [← mul_assoc, ← pow_succ']
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega))
  · -- the extrapolation inequality
    intro J hJ
    set s := 2 ^ (kmax k - (J + 1)) with hs
    have hs1 : 1 ≤ s := Nat.one_le_two_pow
    set S' := s * X ^ (6 * k + 13) with hS'
    set R' := X ^ (3 * k + 7 + (J + 1)) with hR'
    set Y := s * X ^ (9 * k + 19 + J) with hY
    have hXY : X ^ (9 * k + 18) ≤ Y :=
      (hXpow _ _ (by omega)).trans (Nat.le_mul_of_pos_left _ hs1)
    have hY0 : 0 < Y := by positivity
    have hsXY : ∀ a, a ≤ 9 * k + 19 + J → s * X ^ a ≤ Y := fun a ha =>
      Nat.mul_le_mul_left _ (hXpow _ _ ha)
    have htY : t ≤ Y := htX.le.trans ((Nat.le_self_pow (by omega) X).trans hXY)
    have hSY : S' ≤ Y := hsXY _ (by omega)
    have hLY : L ≤ Y := hL ▸ (hXpow _ _ (by omega)).trans hXY
    have hRR : X ^ (3 * k + 7 + J) * S' = X * Y := by rw [hS', hY]; ring
    have hHx : SizeLe r₀ Y cHx (((L : ℝ) + 1) ^ (k + 2) *
        (C * (((L : ℝ) + 1) ^ (k + 2) * entryBound k L h G) *
          (((L : ℝ) + 1) * (R' : ℝ) ^ L * (2 * L * G) ^ S' * G ^ ((k + 1) * L * R')))) := by
      refine SizeLe.mul (SizeLe.of_pow hr₀1 (by positivity) hLV ?_) (SizeLe.mul (hPH Y hXY)
        (SizeLe.mul (SizeLe.mul (SizeLe.mul (SizeLe.of_le hr₀1 (by positivity) hLV ?_)
          (SizeLe.of_pow hr₀1 (Nat.cast_nonneg _) (hRV (J + 1) (by omega)) ?_))
          (SizeLe.of_pow hr₀1 (by positivity) h2LGV ?_)) (SizeLe.of_pow hr₀1 hG hGe ?_)))
      · calc V * (k + 2) = e * W * (k + 2) * t := by ring
          _ ≤ e * W * (k + 2) * Y := Nat.mul_le_mul_left _ htY
      · calc V = e * W * t := by ring
          _ ≤ e * W * Y := Nat.mul_le_mul_left _ htY
      · calc V * L = e * W * (t * L) := by ring
          _ ≤ e * W * (X * X ^ (6 * k + 11)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htX.le)
          _ = e * W * X ^ (6 * k + 12) := by ring
          _ ≤ e * W * Y := Nat.mul_le_mul_left _ ((hXpow _ _ (by omega)).trans hXY)
      · calc V * S' = e * W * (s * (t * X ^ (6 * k + 13))) := by ring
          _ ≤ e * W * (s * (X * X ^ (6 * k + 13))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htX.le))
          _ = e * W * (s * X ^ (6 * k + 14)) := by ring
          _ ≤ e * W * Y := Nat.mul_le_mul_left _ (hsXY _ (by omega))
      · calc e * ((k + 1) * L * R') = e * (k + 1) * X ^ (9 * k + 19 + J) := by
              rw [hL, hR']; ring
          _ ≤ e * (k + 1) * Y := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hs1)
    have hall := (((SizeLe.of_pow hr₀1 hB hBe (c := e) (Nat.mul_le_mul_left e hSY)).mul
      (SizeLe.of_pow hr₀1 (zero_le_one.trans hr₀1) (pow_one r₀).symm.le (c := 1)
        (by simpa using hLY))).mul (hHx.pow D)).mul
      (SizeLe.of_pow hr₀1 hli0 hle (c := e) (Nat.mul_le_mul_left e hSY))
    have hlt := hall.lt hr₀ hY0 hQX
    rw [← hRR] at hlt
    have hl : 0 < lmin ^ S' := pow_pos hlmin0 _
    rw [inv_pow, ← div_eq_mul_inv, div_lt_iff₀ hl] at hlt
    beta_reduce
    rw [mul_comm (lmin ^ _)]
    exact hlt
  · -- the final inequality
    clear_value V L h X
    set Y := X ^ (9 * k + 19 + kmax k) with hY
    have hXY : X ^ (9 * k + 18) ≤ Y := hXpow _ _ (by omega)
    have hY0 : 0 < Y := by positivity
    have hLY : L ≤ Y := hL ▸ (hXpow _ _ (by omega)).trans hXY
    have hRR : X ^ (3 * k + 7 + kmax k) * (2 ^ (kmax k - kmax k) * X ^ (6 * k + 13)) =
        X * Y := by rw [Nat.sub_self, pow_zero, one_mul, hY]; ring
    have h2G : 2 * G ^ ((k + 1) * L) ≤ r₀ ^ (e + e * ((k + 1) * L)) := by
      rw [pow_add]
      exact mul_le_mul h2e (pow_le_pow_mul_of_le hG hGe _) (pow_nonneg hG _)
        (pow_nonneg (zero_le_one.trans hr₀1) _)
    have hbig : (e + e * ((k + 1) * L)) * D * ((L + 1) ^ (k + 1) * (L + 1)) ≤
        e * (k + 2) * D * 2 ^ (k + 2) * Y := by
      have h1 : e + e * ((k + 1) * L) ≤ e * (k + 2) * L := by
        calc e + e * ((k + 1) * L) ≤ e * L + e * ((k + 1) * L) :=
              Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hL1) _
          _ = e * (k + 2) * L := by ring
      have h2 : (L + 1) ^ (k + 1) * (L + 1) ≤ 2 ^ (k + 2) * L ^ (k + 2) := by
        rw [← pow_succ, ← mul_pow]
        exact Nat.pow_le_pow_left (by omega) _
      have h3 : L ^ (k + 3) ≤ Y := by
        rw [hL, ← pow_mul, hY]
        exact hXpow _ _ (mul_le_kmax k)
      calc (e + e * ((k + 1) * L)) * D * ((L + 1) ^ (k + 1) * (L + 1))
          ≤ e * (k + 2) * L * D * (2 ^ (k + 2) * L ^ (k + 2)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2
        _ = e * (k + 2) * D * 2 ^ (k + 2) * L ^ (k + 3) := by ring
        _ ≤ e * (k + 2) * D * 2 ^ (k + 2) * Y := Nat.mul_le_mul_left _ h3
    have h2G0 : 0 ≤ 2 * G ^ ((k + 1) * L) := mul_nonneg zero_le_two (pow_nonneg hG _)
    have hall := ((((hPH Y hXY).pow D).mul (SizeLe.of_pow hr₀1 hp0 hpe (c := e)
      (Nat.mul_le_mul_left e hLY))).mul (SizeLe.of_le hr₀1 (pow_nonneg (pow_nonneg h2G0 _) _)
        (pow_le_pow_mul_of_le (pow_nonneg h2G0 _) (pow_le_pow_mul_of_le h2G0 h2G D) _)
        hbig)).mul (SizeLe.of_pow hr₀1 (zero_le_one.trans hr₀1) (pow_one r₀).symm.le (c := 1)
          (by simpa using hLY))
    have hlt := hall.lt hr₀ hY0 hQ'X
    rwa [← hRR] at hlt

end PadicBaker
