import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Section 6, equations (5)--(8) and the final two cases.
The source prints δ(4r+3) in (8), but the triangle estimate is δ(4+3|r|).
The following proves the corrected bound from the preceding hypotheses.
-/
namespace SigmaNonprimarity

/-- Perturb a scalar and its modulus simultaneously, retaining the coefficient dependence. -/
theorem modulus_approximation {u v r z δ : ℝ} (_hδ : 0 < δ)
    (hu : |u - v| < 3 * δ) (hz : abs (|u| - (r * u + z)) < δ) :
    abs (|v| - (r * v + z)) < δ * (4 + 3 * |r|) := by
  have hmod : abs (|v| - |u|) ≤ |u - v| := by
    simpa only [abs_sub_comm v u] using abs_abs_sub_abs_le_abs_sub v u
  have hmul := mul_le_mul_of_nonneg_left hu.le (abs_nonneg r)
  have htri : abs (|v| - (r * v + z)) ≤
      abs (|v| - |u|) + abs (|u| - (r * u + z)) + |r| * |u - v| := by
    calc
      abs (|v| - (r * v + z)) = |(|v| - |u|) + (|u| - (r*u+z)) + r*(u-v)| := by
        congr 1; ring
      _ ≤ |(|v| - |u|) + (|u| - (r*u+z))| + |r*(u-v)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; exact add_le_add_right (abs_add_le _ _) _
  nlinarith

/-- For |r| ≤ 1/2 both nonzero levels lie above the zero level by a uniform gap.
This explicitly covers negative coefficients, omitted in the paper's displayed proof. -/
theorem small_coefficient_gap {a δ r v z w : ℝ} (hδ : 0 < δ) (ha : 11*δ < a)
    (hr : |r| ≤ 1/2) (hv : v = 2*a ∨ v = -(2*a))
    (hz : abs (|v| - (r*v+z)) < δ*(4+3*|r|))
    (hw : |w| < δ*(4+3*|r|)) : a - 11*δ < z - w := by
  have ha0 : 0 ≤ a := by linarith
  have hb : δ*(4+3*|r|) ≤ 11/2*δ := by nlinarith
  have hrr := abs_le.mp hr
  have hw' := (abs_lt.mp hw).2
  rcases hv with rfl | rfl
  · rw [abs_of_nonneg (by positivity : 0 ≤ 2*a)] at hz
    have hz' := (abs_lt.mp hz).2
    nlinarith
  · rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2*a)] at hz
    have hz' := (abs_lt.mp hz).2
    nlinarith

/-- For r > 1/2 the negative level lies uniformly above the positive level. -/
theorem positive_coefficient_gap {a δ r zp zm : ℝ} (hδ : 0 < δ) (ha : 11*δ < a)
    (hr : 1/2 < r)
    (hp : |2*a - (r*(2*a)+zp)| < δ*(4+3*|r|))
    (hm : |2*a - (r*(-(2*a))+zm)| < δ*(4+3*|r|)) :
    2*a - 11*δ < zm - zp := by
  have hr0 : 0 ≤ r := by linarith
  rw [abs_of_nonneg hr0] at hp hm
  have hp' := (abs_lt.mp hp).1
  have hm' := (abs_lt.mp hm).2
  have hpos : 0 < 2*a - 3*δ := by linarith
  have hprod : 0 < (2*r-1)*(2*a-3*δ) := mul_pos (by linarith) hpos
  nlinarith

/-- For r < -1/2 the positive level lies uniformly above the negative level. -/
theorem negative_coefficient_gap {a δ r zp zm : ℝ} (hδ : 0 < δ) (ha : 11*δ < a)
    (hr : r < -(1/2))
    (hp : |2*a - (r*(2*a)+zp)| < δ*(4+3*|r|))
    (hm : |2*a - (r*(-(2*a))+zm)| < δ*(4+3*|r|)) :
    2*a - 11*δ < zp - zm := by
  have hr0 : r ≤ 0 := by linarith
  rw [abs_of_nonpos hr0] at hp hm
  have hp' := (abs_lt.mp hp).2
  have hm' := (abs_lt.mp hm).1
  have hpos : 0 < 2*a - 3*δ := by linarith
  have hprod : 0 < (-2*r-1)*(2*a-3*δ) := mul_pos (by linarith) hpos
  nlinarith

/-! The three scalar levels force one of exactly the two forbidden separations. -/

def UniformGap (z : ℕ → ℝ) (S T : Set ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n ∈ S, ∀ k ∈ T, ε ≤ |z n - z k|

/-- The quantitative end of Section 6, including the omitted r < 0 case.
No Banach-space existence or transfinite construction is assumed implicitly. -/
theorem three_level_separation (u z : ℕ → ℝ) (J₀ J₁ J₂ : Set ℕ)
    (a δ r : ℝ) (hδ : 0 < δ) (ha : 11*δ < a)
    (hp : ∀ n ∈ J₂, |u n - 2*a| < 3*δ)
    (hm : ∀ n ∈ J₁ \ J₂, |u n - (-(2*a))| < 3*δ)
    (hzero : ∀ n ∈ J₀ \ J₁, |u n| < 3*δ)
    (happrox : ∀ n, abs (|u n| - (r*u n+z n)) < δ) :
    UniformGap z J₁ (J₀ \ J₁) ∨ UniformGap z J₂ (J₁ \ J₂) := by
  have ha0 : 0 ≤ 2*a := by linarith
  have hplus (n) (hn : n ∈ J₂) :
      |2*a - (r*(2*a)+z n)| < δ*(4+3*|r|) := by
    simpa only [abs_of_nonneg ha0] using modulus_approximation hδ (hp n hn) (happrox n)
  have hminus (n) (hn : n ∈ J₁ \ J₂) :
      |2*a - (r*(-(2*a))+z n)| < δ*(4+3*|r|) := by
    simpa only [abs_neg, abs_of_nonneg ha0] using
      modulus_approximation hδ (hm n hn) (happrox n)
  by_cases hr : |r| ≤ 1/2
  · left
    refine ⟨a-11*δ, by linarith, ?_⟩
    intro n hn k hk
    have hk' : |z k| < δ*(4+3*|r|) := by
      simpa only [sub_zero, abs_zero, mul_zero, zero_add, zero_sub, abs_neg] using
        modulus_approximation (v := 0) hδ (by simpa using hzero k hk) (happrox k)
    have hgap : a-11*δ < z n-z k := by
      by_cases hn₂ : n ∈ J₂
      · exact small_coefficient_gap hδ ha hr (Or.inl rfl)
          (modulus_approximation hδ (hp n hn₂) (happrox n)) hk'
      · exact small_coefficient_gap hδ ha hr (Or.inr rfl)
          (modulus_approximation hδ (hm n ⟨hn, hn₂⟩) (happrox n)) hk'
    exact hgap.le.trans (le_abs_self _)
  · right
    refine ⟨2*a-11*δ, by linarith, ?_⟩
    intro n hn k hk
    have hr' : 1/2 < |r| := lt_of_not_ge hr
    rcases (lt_abs.mp hr') with hrp | hrn
    · have hgap := positive_coefficient_gap hδ ha hrp (hplus n hn) (hminus k hk)
      rw [abs_sub_comm]
      exact hgap.le.trans (le_abs_self _)
    · have hrn' : r < -(1/2) := by linarith
      exact (negative_coefficient_gap hδ ha hrn' (hplus n hn) (hminus k hk)).le.trans
        (le_abs_self _)

end SigmaNonprimarity
