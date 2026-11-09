import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The real two-point Bonami inequality

An elementary calculus proof of the scalar inequality used to tensorize
hypercontractivity. The second derivative estimate is reduced to AM–GM.
-/

noncomputable section
open Set

namespace PL1.BonamiTwoPoint

private theorem negative_power_pair (x q : ℝ) (hx : -1 < x) (hx' : x < 1)
    (hq : q ≤ 0) : 2 ≤ (1 + x) ^ q + (1 - x) ^ q := by
  have hplus : 0 < 1 + x := by linarith
  have hminus : 0 < 1 - x := by linarith
  have hprod : 1 ≤ ((1 + x) * (1 - x)) ^ q :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos hplus hminus)
      (by nlinarith [sq_nonneg x]) hq
  rw [Real.mul_rpow hplus.le hminus.le] at hprod
  have hp := Real.rpow_pos_of_pos hplus q
  have hm := Real.rpow_pos_of_pos hminus q
  nlinarith [sq_nonneg ((1 + x) ^ q - (1 - x) ^ q)]

private def remainder (p x : ℝ) : ℝ :=
  ((1 + x) ^ p + (1 - x) ^ p) / 2 - 1 - p * (p - 1) / 2 * x ^ 2

private def remainderDeriv (p x : ℝ) : ℝ :=
  p / 2 * ((1 + x) ^ (p - 1) - (1 - x) ^ (p - 1)) - p * (p - 1) * x

private theorem hasDerivAt_remainder (p x : ℝ) (hp : 1 ≤ p) :
    HasDerivAt (remainder p) (remainderDeriv p x) x := by
  have hplus := ((hasDerivAt_id x).const_add 1).rpow_const (Or.inr hp)
  have hminus := ((hasDerivAt_id x).const_sub 1).rpow_const (Or.inr hp)
  convert (((hplus.add hminus).div_const 2).sub_const 1).sub
    (((hasDerivAt_id x).pow 2).const_mul (p * (p - 1) / 2)) using 1 <;>
    first | rfl | (dsimp [remainder, remainderDeriv]; ring)

private theorem hasDerivAt_remainderDeriv (p x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    HasDerivAt (remainderDeriv p)
      (p * (p - 1) / 2 * ((1 + x) ^ (p - 2) + (1 - x) ^ (p - 2) - 2)) x := by
  have hplus := ((hasDerivAt_id x).const_add 1).rpow_const
    (p := p - 1) (Or.inl (by linarith : 1 + x ≠ 0))
  have hminus := ((hasDerivAt_id x).const_sub 1).rpow_const
    (p := p - 1) (Or.inl (by linarith : 1 - x ≠ 0))
  convert ((hplus.sub hminus).const_mul (p / 2)).sub
    ((hasDerivAt_id x).const_mul (p * (p - 1))) using 1 <;>
    first | rfl | (dsimp [remainderDeriv]; ring_nf)

private theorem remainderDeriv_nonneg (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) : 0 ≤ remainderDeriv p x := by
  have hd : ∀ y ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (remainderDeriv p)
        (p * (p - 1) / 2 * ((1 + y) ^ (p - 2) + (1 - y) ^ (p - 2) - 2)) y :=
    fun y hy => hasDerivAt_remainderDeriv p y hy.1 hy.2
  have hm : MonotoneOn (remainderDeriv p) (Ioo (-1 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    · intro y hy
      exact (hd y (by simpa only [interior_Ioo] using hy)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Ioo (-1 : ℝ) 1 := by simpa only [interior_Ioo] using hy
      exact mul_nonneg (by positivity) (sub_nonneg.mpr
        (negative_power_pair y (p - 2) hy'.1 hy'.2 (by linarith)))
  have h := hm (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num)
    (show x ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith) hx
  simpa [remainderDeriv] using h

/-- Quadratic lower bound for the normalized two-point p-moment. -/
theorem normalized_moment_lower (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    1 + p * (p - 1) / 2 * x ^ 2 ≤ ((1 + x) ^ p + (1 - x) ^ p) / 2 := by
  have hm : MonotoneOn (remainder p) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun y _ => (hasDerivAt_remainder p y hp).continuousAt.continuousWithinAt)
    · intro y _
      exact (hasDerivAt_remainder p y hp).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hy
      exact remainderDeriv_nonneg p hp hp' y hy'.1.le hy'.2
  have h := hm (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    ⟨hx, hx'⟩ hx
  have h0 : remainder p 0 = 0 := by simp [remainder]
  rw [h0] at h
  dsimp [remainder] at h
  linarith

/-- The sharp normalized real two-point Bonami inequality. -/
theorem normalized (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    1 + (p - 1) * x ^ 2 ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hz : 0 ≤ p * (p - 1) / 2 * x ^ 2 := by positivity
  have hbernoulli := one_add_mul_self_le_rpow_one_add
    (s := p * (p - 1) / 2 * x ^ 2) (p := 2 / p) (by linarith)
    ((le_div_iff₀ hp0).mpr (by linarith))
  have heq : 1 + (2 / p) * (p * (p - 1) / 2 * x ^ 2) = 1 + (p - 1) * x ^ 2 := by
    field_simp
  rw [heq] at hbernoulli
  exact hbernoulli.trans (Real.rpow_le_rpow (by linarith)
    (normalized_moment_lower p hp hp' x hx hx') (by positivity))

private theorem coefficient_ordered (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    a ^ 2 + (p - 1) * b ^ 2 ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (2 / p) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · have hb0 : b = 0 := le_antisymm hba hb
    subst b
    simp [Real.zero_rpow (by linarith : p ≠ 0),
      Real.zero_rpow (by positivity : 2 / p ≠ 0)]
  have hx : 0 ≤ b / a := div_nonneg hb ha.le
  have hx' : b / a ≤ 1 := (div_le_one ha).mpr hba
  have h := mul_le_mul_of_nonneg_left (normalized p hp hp' (b / a) hx hx')
    (sq_nonneg a)
  have heqplus : a + b = a * (1 + b / a) := by field_simp
  have heqminus : a - b = a * (1 - b / a) := by field_simp
  have hmoment : (|a + b| ^ p + |a - b| ^ p) / 2 =
      a ^ p * (((1 + b / a) ^ p + (1 - b / a) ^ p) / 2) := by
    rw [abs_of_nonneg (add_nonneg ha.le hb), abs_of_nonneg (sub_nonneg.mpr hba),
      heqplus, heqminus, Real.mul_rpow ha.le (by linarith),
      Real.mul_rpow ha.le (by linarith)]
    ring
  rw [hmoment, Real.mul_rpow (Real.rpow_nonneg ha.le p) (by positivity),
    ← Real.rpow_mul ha.le, show p * (2 / p) = (2 : ℝ) by field_simp,
    Real.rpow_two]
  convert h using 1 <;> first | rfl | field_simp

private theorem coefficient_nonneg (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + (p - 1) * b ^ 2 ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (2 / p) := by
  rcases le_total b a with hba | hab
  · exact coefficient_ordered p hp hp' a b ha hb hba
  · have h := coefficient_ordered p hp hp' b a hb ha hab
    rw [add_comm b a, abs_sub_comm b a] at h
    have hs : a ^ 2 ≤ b ^ 2 := by nlinarith
    have hc := mul_nonneg (show 0 ≤ 2 - p by linarith) (sub_nonneg.mpr hs)
    nlinarith

private theorem abs_moment (p a b : ℝ) :
    |(|a| + |b|)| ^ p + |(|a| - |b|)| ^ p = |a + b| ^ p + |a - b| ^ p := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · simp only [abs_of_nonneg ha, abs_of_nonneg hb]
  · simp only [abs_of_nonneg ha, abs_of_nonpos hb, sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  · simp only [abs_of_nonpos ha, abs_of_nonneg hb]
    rw [show -a + b = -(a - b) by ring, show -a - b = -(a + b) by ring,
      abs_neg, abs_neg]
    ring
  · simp only [abs_of_nonpos ha, abs_of_nonpos hb]
    rw [show -a + -b = -(a + b) by ring, show -a - -b = -(a - b) by ring,
      abs_neg, abs_neg]

/-- Sharp coefficient form of the real two-point Bonami inequality. -/
theorem coefficient (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2) (a b : ℝ) :
    a ^ 2 + (p - 1) * b ^ 2 ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (2 / p) := by
  have h := coefficient_nonneg p hp hp' |a| |b| (abs_nonneg a) (abs_nonneg b)
  rwa [abs_moment, sq_abs, sq_abs] at h

/-- Noise coefficient form, allowing either sign of rho. -/
theorem noise_coefficient (p ρ : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (hρ : ρ ^ 2 ≤ p - 1) (a b : ℝ) :
    a ^ 2 + (ρ * b) ^ 2 ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (2 / p) := by
  have h := coefficient p hp hp' a b
  have hc := mul_le_mul_of_nonneg_right hρ (sq_nonneg b)
  nlinarith

/-- Moment form used directly by finite-product tensorization. -/
theorem noise_moment (p ρ : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (hρ : ρ ^ 2 ≤ p - 1) (a b : ℝ) :
    (a ^ 2 + (ρ * b) ^ 2) ^ (p / 2) ≤ (|a + b| ^ p + |a - b| ^ p) / 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h := Real.rpow_le_rpow (by positivity) (noise_coefficient p ρ hp hp' hρ a b)
    (show 0 ≤ p / 2 by positivity)
  rwa [← Real.rpow_mul (by positivity), show (2 / p) * (p / 2) = (1 : ℝ) by field_simp,
    Real.rpow_one] at h

#print axioms coefficient
#print axioms noise_moment

end PL1.BonamiTwoPoint
