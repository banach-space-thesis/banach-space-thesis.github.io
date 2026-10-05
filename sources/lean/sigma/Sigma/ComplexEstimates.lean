import Sigma.Estimates
import Mathlib.Analysis.Complex.Basic

/-! The scalar obstruction needed by the unnumbered complex extension of the
Sigma paper. The cited Section 5 of de Hevia et al. supplies the complex
three-level strategy. These estimates treat every complex coefficient directly;
no reduction of that coefficient to a nonnegative real number is assumed. -/
namespace SigmaNonprimarity

/-- A fixed positive distance between the two sets of complex evaluations. -/
def ComplexUniformGap (z : ℕ → ℂ) (S T : Set ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n ∈ S, ∀ k ∈ T, ε ≤ ‖z n - z k‖

/-- Perturbation of a complex value and of its real, nonnegative modulus. -/
theorem complex_modulus_approximation {u v r z : ℂ} {δ : ℝ}
    (hu : ‖u - v‖ < 3 * δ) (hz : ‖(‖u‖ : ℂ) - (r * u + z)‖ < δ) :
    ‖(‖v‖ : ℂ) - (r * v + z)‖ < δ * (4 + 3 * ‖r‖) := by
  have hmod : ‖(‖v‖ : ℂ) - (‖u‖ : ℂ)‖ ≤ ‖u - v‖ := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      norm_sub_rev v u] using abs_norm_sub_norm_le v u
  have htri : ‖(‖v‖ : ℂ) - (r * v + z)‖ ≤
      ‖(‖v‖ : ℂ) - (‖u‖ : ℂ)‖ + ‖(‖u‖ : ℂ) - (r * u + z)‖ +
        ‖r‖ * ‖u - v‖ := by
    calc
      _ = ‖((‖v‖ : ℂ) - (‖u‖ : ℂ)) + ((‖u‖ : ℂ) - (r*u+z)) + r*(u-v)‖ := by
        congr 1; ring
      _ ≤ ‖((‖v‖ : ℂ) - (‖u‖ : ℂ)) + ((‖u‖ : ℂ) - (r*u+z))‖ + ‖r*(u-v)‖ :=
        norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; exact add_le_add_right (norm_add_le _ _) _
  have hmul := mul_le_mul_of_nonneg_left hu.le (norm_nonneg r)
  nlinarith

/-- The small-coefficient case uses a reverse triangle inequality, so both
complex signs are handled with the same quantitative bound. -/
theorem complex_small_coefficient_gap {a r v z w : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (ha : 11 * δ < ‖a‖) (hr : ‖r‖ ≤ 1/2)
    (hv : v = 2*a ∨ v = -(2*a))
    (hz : ‖(‖v‖ : ℂ) - (r*v+z)‖ < δ*(4+3*‖r‖))
    (hw : ‖w‖ < δ*(4+3*‖r‖)) : ‖a‖ - 11*δ < ‖z-w‖ := by
  have hvnorm : ‖v‖ = 2 * ‖a‖ := by rcases hv with rfl | rfl <;> simp [norm_mul]
  have hlow : ‖v‖ - ‖r‖ * ‖v‖ ≤ ‖(‖v‖ : ℂ) - r*v‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v),
      norm_mul] using norm_sub_norm_le (‖v‖ : ℂ) (r*v)
  have hupper : ‖(‖v‖ : ℂ) - r*v‖ ≤
      ‖(‖v‖ : ℂ) - (r*v+z)‖ + ‖z-w‖ + ‖w‖ := by
    calc
      _ = ‖((‖v‖ : ℂ) - (r*v+z)) + (z-w) + w‖ := by congr 1; ring
      _ ≤ _ := norm_add₃_le
  have hb : δ*(4+3*‖r‖) ≤ 11/2*δ := by nlinarith
  rw [hvnorm] at hlow hupper hz
  have hprod : 0 ≤ (1 - 2 * ‖r‖) * ‖a‖ := mul_nonneg (by linarith) (norm_nonneg _)
  nlinarith

/-- For every large complex coefficient, the positive and negative levels
remain uniformly separated; no ordering of the coefficient is needed. -/
theorem complex_large_coefficient_gap {a r zp zm : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (ha : 11*δ < ‖a‖) (hr : 1/2 < ‖r‖)
    (hp : ‖(2*‖a‖ : ℂ) - (r*(2*a)+zp)‖ < δ*(4+3*‖r‖))
    (hm : ‖(2*‖a‖ : ℂ) - (r*(-(2*a))+zm)‖ < δ*(4+3*‖r‖)) :
    2*‖a‖ - 11*δ < ‖zp-zm‖ := by
  have hsum : 4 * ‖r‖ * ‖a‖ ≤
      ‖(2*‖a‖ : ℂ) - (r*(2*a)+zp)‖ + ‖zp-zm‖ +
        ‖(2*‖a‖ : ℂ) - (r*(-(2*a))+zm)‖ := by
    calc
      4 * ‖r‖ * ‖a‖ = ‖(4 : ℂ)*r*a‖ := by simp [norm_mul]
      _ = ‖(-((2*‖a‖ : ℂ) - (r*(2*a)+zp))) + (-(zp-zm)) +
          ((2*‖a‖ : ℂ) - (r*(-(2*a))+zm))‖ := by congr 1; ring
      _ ≤ ‖-((2*‖a‖ : ℂ) - (r*(2*a)+zp))‖ + ‖-(zp-zm)‖ +
          ‖(2*‖a‖ : ℂ) - (r*(-(2*a))+zm)‖ := norm_add₃_le
      _ = _ := by rw [norm_neg, norm_neg]
  have hprod : 0 < (2*‖r‖-1)*(2*‖a‖-3*δ) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- The complex analogue of the final Section 6 contradiction. Its hypotheses
are precisely the three complex levels and a putative complex modulus. -/
theorem complex_three_level_separation (u z : ℕ → ℂ) (J₀ J₁ J₂ : Set ℕ)
    (a : ℂ) (δ : ℝ) (r : ℂ) (hδ : 0 < δ) (ha : 11*δ < ‖a‖)
    (hp : ∀ n ∈ J₂, ‖u n - 2*a‖ < 3*δ)
    (hm : ∀ n ∈ J₁ \ J₂, ‖u n - (-(2*a))‖ < 3*δ)
    (hz : ∀ n ∈ J₀ \ J₁, ‖u n‖ < 3*δ)
    (happrox : ∀ n, ‖(‖u n‖ : ℂ) - (r*u n+z n)‖ < δ) :
    ComplexUniformGap z J₁ (J₀ \ J₁) ∨ ComplexUniformGap z J₂ (J₁ \ J₂) := by
  have hplus (n) (hn : n ∈ J₂) :
      ‖(2*‖a‖ : ℂ) - (r*(2*a)+z n)‖ < δ*(4+3*‖r‖) := by
    simpa [norm_mul] using
      complex_modulus_approximation (hp n hn) (happrox n)
  have hminus (n) (hn : n ∈ J₁ \ J₂) :
      ‖(2*‖a‖ : ℂ) - (r*(-(2*a))+z n)‖ < δ*(4+3*‖r‖) := by
    simpa [norm_mul] using
      complex_modulus_approximation (hm n hn) (happrox n)
  by_cases hr : ‖r‖ ≤ 1/2
  · left
    refine ⟨‖a‖-11*δ, by linarith, ?_⟩
    intro n hn k hk
    have hk' : ‖z k‖ < δ*(4+3*‖r‖) := by
      simpa only [sub_zero, norm_zero, Complex.ofReal_zero, mul_zero, zero_add,
        zero_sub, norm_neg] using
        complex_modulus_approximation (v := 0) (by simpa using hz k hk) (happrox k)
    by_cases hn₂ : n ∈ J₂
    · exact (complex_small_coefficient_gap hδ ha hr (Or.inl rfl)
        (complex_modulus_approximation (hp n hn₂) (happrox n)) hk').le
    · exact (complex_small_coefficient_gap hδ ha hr (Or.inr rfl)
        (complex_modulus_approximation (hm n ⟨hn, hn₂⟩) (happrox n)) hk').le
  · right
    refine ⟨2*‖a‖-11*δ, by linarith [norm_nonneg a], ?_⟩
    intro n hn k hk
    exact (complex_large_coefficient_gap hδ ha (lt_of_not_ge hr)
      (hplus n hn) (hminus k hk)).le

end SigmaNonprimarity
