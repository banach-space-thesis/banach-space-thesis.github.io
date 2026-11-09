import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar estimates for the common singular carrier

The dyadic thresholds and square-root logarithmic bias lower bounds used in
the Borel--Cantelli construction, including arbitrary nonnegative tail shifts.
-/

noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology

namespace PL1.CarrierAsymptotics

def threshold (r : ℕ) : ℝ := (Real.exp (-Real.log 2 / 4)) ^ r

def biasLower (u c : ℝ) (r : ℕ) : ℝ :=
  Real.exp (-u * Real.sqrt (((r : ℝ) + c) * Real.log 2))

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem threshold_pos (r : ℕ) : 0 < threshold r := pow_pos (Real.exp_pos _) _

theorem biasLower_pos (u c : ℝ) (r : ℕ) : 0 < biasLower u c r := Real.exp_pos _

/-- A fixed square-root logarithmic bias exponent grows slower than every
positive linear function of the dyadic index. -/
theorem eventually_sqrt_le_linear (u : ℝ) (hu : 0 ≤ u) (c : ℝ) (hc : 0 ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, u * Real.sqrt (((r : ℝ) + c) * Real.log 2) ≤ ε * r := by
  have h₁ : ∀ᶠ r : ℕ in atTop, c ≤ (r : ℝ) := (eventually_ge_atTop c).natCast_atTop
  have h₂ : ∀ᶠ r : ℕ in atTop, 2 * u ^ 2 * Real.log 2 / ε ^ 2 ≤ (r : ℝ) :=
    (eventually_ge_atTop (2 * u ^ 2 * Real.log 2 / ε ^ 2)).natCast_atTop
  filter_upwards [h₁, h₂] with r hrc hrbound
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hscale : 2 * u ^ 2 * Real.log 2 ≤ ε ^ 2 * r :=
    (div_le_iff₀ (sq_pos_of_pos hε)).1 hrbound |>.trans_eq (mul_comm _ _)
  have harg : 0 ≤ ((r : ℝ) + c) * Real.log 2 :=
    mul_nonneg (add_nonneg hr hc) log_two_pos.le
  have hs := Real.sq_sqrt harg
  have hsq : (u * Real.sqrt (((r : ℝ) + c) * Real.log 2)) ^ 2 =
      u ^ 2 * (((r : ℝ) + c) * Real.log 2) := by rw [mul_pow, hs]
  have hsum : ((r : ℝ) + c) * Real.log 2 ≤ 2 * r * Real.log 2 := by
    nlinarith [log_two_pos]
  have hleft := mul_le_mul_of_nonneg_left hsum (sq_nonneg u)
  have hright := mul_le_mul_of_nonneg_right hscale hr
  have hlinear : 0 ≤ ε * (r : ℝ) := mul_nonneg hε.le hr
  have hsqrt : 0 ≤ u * Real.sqrt (((r : ℝ) + c) * Real.log 2) :=
    mul_nonneg hu (Real.sqrt_nonneg _)
  nlinarith

theorem threshold_eq_exp (r : ℕ) :
    threshold r = Real.exp ((r : ℝ) * (-Real.log 2 / 4)) := by
  exact (Real.exp_nat_mul (-Real.log 2 / 4) r).symm

/-- The bias lower bound eventually exceeds twice the carrier threshold. -/
theorem eventually_two_threshold_le_biasLower (u : ℝ) (hu : 0 ≤ u) (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ r : ℕ in atTop, 2 * threshold r ≤ biasLower u c r := by
  have hε : 0 < Real.log 2 / 8 := div_pos log_two_pos (by norm_num)
  have hg := eventually_sqrt_le_linear u hu c hc (Real.log 2 / 8) hε
  filter_upwards [hg, (eventually_ge_atTop (8 : ℝ)).natCast_atTop] with r hr hr8
  rw [threshold_eq_exp, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [Real.log_exp]
  change Real.log 2 + (r : ℝ) * (-Real.log 2 / 4) ≤ -u * Real.sqrt (((r : ℝ) + c) * Real.log 2)
  nlinarith [log_two_pos]

theorem half_pow_eq_exp (r : ℕ) :
    (1 / 2 : ℝ) ^ r = Real.exp ((r : ℝ) * (-Real.log 2)) := by
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [one_div]

/-- The summable Chebyshev bounds for all fixed positive-time noise laws. -/
theorem summable_noise_failure_bound (u : ℝ) (hu : 0 ≤ u) (c : ℝ) (hc : 0 ≤ c) :
    Summable (fun r : ℕ => 4 * (1 / 2 : ℝ) ^ r *
      Real.exp (2 * u * Real.sqrt (((r : ℝ) + c) * Real.log 2))) := by
  have hgeom : Summable (fun r : ℕ => 4 * Real.exp ((r : ℝ) * (-Real.log 2 / 2))) :=
    (Real.summable_exp_nat_mul_iff.2 (by linarith [log_two_pos])).mul_left 4
  apply hgeom.of_norm_bounded_eventually_nat
  have hg := eventually_sqrt_le_linear u hu c hc (Real.log 2 / 4)
    (div_pos log_two_pos (by norm_num))
  filter_upwards [hg] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [half_pow_eq_exp, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.2
  nlinarith

/-- The Haar Chebyshev bounds form a convergent geometric series. -/
theorem summable_haar_failure_bound :
    Summable (fun r : ℕ => (1 / 2 : ℝ) ^ r / (threshold r) ^ 2) := by
  have hg : Summable (fun r : ℕ => Real.exp ((r : ℝ) * (-Real.log 2 / 2))) :=
    Real.summable_exp_nat_mul_iff.2 (by linarith [log_two_pos])
  apply hg.congr
  intro r
  rw [threshold_eq_exp, half_pow_eq_exp, ← Real.exp_nat_mul, ← Real.exp_sub]
  congr 1
  push_cast
  ring

/-- The slow rates remain controlled after deleting an arbitrary finite prefix. -/
theorem shifted_rate_le (d r j : ℕ) (hj : j < 2 ^ r) :
    Real.sqrt (Real.log ((d + j : ℕ) + 2 : ℝ)) ≤
      Real.sqrt (((r : ℝ) + (d : ℝ) + 1) * Real.log 2) := by
  have hd : d + 2 ≤ 2 ^ (d + 1) := by
    have h : d + 1 < 2 ^ (d + 1) := Nat.lt_two_pow_self
    omega
  have hr : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_two_pow
  have hn : d + j + 2 ≤ 2 ^ (r + d + 1) := by
    calc
      d + j + 2 ≤ d + 2 ^ r + 1 := by omega
      _ ≤ (d + 2) * 2 ^ r := by nlinarith
      _ ≤ 2 ^ (d + 1) * 2 ^ r := Nat.mul_le_mul_right _ hd
      _ = 2 ^ (r + d + 1) := by rw [← pow_add]; congr 1; omega
  have hcast : ((d + j : ℕ) + 2 : ℝ) ≤ (2 : ℝ) ^ (r + d + 1) := by exact_mod_cast hn
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ Real.log ((2 : ℝ) ^ (r + d + 1)) := Real.log_le_log (by positivity) hcast
    _ = _ := by rw [Real.log_pow]; push_cast; ring

theorem noise_failure_bound_eq (u c : ℝ) (r : ℕ) :
    (1 / 2 : ℝ) ^ r / (biasLower u c r / 2) ^ 2 =
      4 * (1 / 2 : ℝ) ^ r * Real.exp (2 * u * Real.sqrt (((r : ℝ) + c) * Real.log 2)) := by
  unfold biasLower
  have he : Real.exp (2 * u * Real.sqrt (((r : ℝ) + c) * Real.log 2)) =
      (Real.exp (-u * Real.sqrt (((r : ℝ) + c) * Real.log 2)) ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [he]
  field_simp
  norm_num

end PL1.CarrierAsymptotics
