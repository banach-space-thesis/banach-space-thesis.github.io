import PL1.GeneratorGraphBanach

/-! # Standard norm properties of the actual graph K-functional -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.KFunctional
open Noise Walsh ResolventGeneratorGraph

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

@[simp] theorem value_zero {t : ℝ} (ht : 0 ≤ t) : value K rates t 0 = 0 := by
  apply le_antisymm
  · simpa only [norm_zero] using value_le_norm K rates ht 0
  · exact value_nonneg K rates ht 0

theorem min_mul_norm_le {t : ℝ} (ht : 0 ≤ t) (f : Lp K 1 haar) :
    min 1 t * ‖f‖ ≤ value K rates t f := by
  apply le_value K rates
  intro z
  have hc : 0 ≤ min 1 t := le_min zero_le_one ht
  have htriangle := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add f z.val.1) hc
  have hfirst := mul_le_mul_of_nonneg_right (min_le_left 1 t) (norm_nonneg (f-z.val.1))
  have hsecond := mul_le_mul_of_nonneg_right (min_le_right 1 t) (norm_nonneg z.val.1)
  have hlast := mul_nonneg ht (norm_nonneg z.val.2)
  dsimp only [cost, graphNorm]
  nlinarith

theorem cost_le_norm_sub_add_cost {t : ℝ} (f g : Lp K 1 haar) (z : graph K rates) :
    cost K rates t f z ≤ ‖f-g‖ + cost K rates t g z := by
  have h : f-z.val.1 = (f-g)+(g-z.val.1) := by abel
  have htri := norm_add_le (f-g) (g-z.val.1)
  rw [← h] at htri
  dsimp only [cost]
  linarith

theorem value_le_norm_sub_add_value {t : ℝ} (ht : 0 ≤ t) (f g : Lp K 1 haar) :
    value K rates t f ≤ ‖f-g‖ + value K rates t g := by
  have h : value K rates t f - ‖f-g‖ ≤ value K rates t g := by
    apply le_value K rates
    intro z
    have h1 := value_le_cost K rates ht f z
    have h2 := cost_le_norm_sub_add_cost K rates f g z (t:=t)
    linarith
  linarith

theorem abs_value_sub_le {t : ℝ} (ht : 0 ≤ t) (f g : Lp K 1 haar) :
    |value K rates t f - value K rates t g| ≤ ‖f-g‖ := by
  apply abs_le.mpr
  have hfg := value_le_norm_sub_add_value K rates ht f g
  have hgf := value_le_norm_sub_add_value K rates ht g f
  rw [norm_sub_rev g f] at hgf
  constructor <;> linarith

theorem lipschitzWith_value {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith 1 (value K rates t) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    abs_value_sub_le K rates ht f g

theorem continuous_value {t : ℝ} (ht : 0 ≤ t) : Continuous (value K rates t) :=
  (lipschitzWith_value K rates ht).continuous

theorem cost_add_le {t : ℝ} (ht : 0 ≤ t) (f g : Lp K 1 haar)
    (z w : graph K rates) :
    cost K rates t (f+g) (z+w) ≤ cost K rates t f z + cost K rates t g w := by
  have he : f+g-(z.val.1+w.val.1) = (f-z.val.1)+(g-w.val.1) := by abel
  have h1 := norm_add_le (f-z.val.1) (g-w.val.1)
  have h2 := mul_le_mul_of_nonneg_left (norm_add_le z.val.1 w.val.1) ht
  have h3 := mul_le_mul_of_nonneg_left (norm_add_le z.val.2 w.val.2) ht
  change ‖f+g-(z.val.1+w.val.1)‖+t*(‖z.val.1+w.val.1‖+‖z.val.2+w.val.2‖) ≤ _
  rw [he]
  dsimp only [cost, graphNorm]
  nlinarith

theorem value_add_le {t : ℝ} (ht : 0 ≤ t) (f g : Lp K 1 haar) :
    value K rates t (f+g) ≤ value K rates t f + value K rates t g := by
  have h : value K rates t (f+g)-value K rates t g ≤ value K rates t f := by
    apply le_value K rates
    intro z
    have hz : value K rates t (f+g)-cost K rates t f z ≤ value K rates t g := by
      apply le_value K rates
      intro w
      have h1 := value_le_cost K rates ht (f+g) (z+w)
      have h2 := cost_add_le K rates ht f g z w
      linarith
    linarith
  linarith

theorem cost_smul {t : ℝ} (a : K) (f : Lp K 1 haar) (z : graph K rates) :
    cost K rates t (a • f) (a • z) = ‖a‖ * cost K rates t f z := by
  change ‖a • f - a • z.val.1‖ + t * (‖a • z.val.1‖ + ‖a • z.val.2‖) = _
  rw [← smul_sub]
  simp only [norm_smul, cost, graphNorm]
  ring

theorem value_smul_le {t : ℝ} (ht : 0 ≤ t) (a : K) (f : Lp K 1 haar) :
    value K rates t (a • f) ≤ ‖a‖ * value K rates t f := by
  by_cases ha : a=0
  · simp only [ha, zero_smul, norm_zero, zero_mul, value_zero K rates ht]
    exact le_rfl
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [mul_comm ‖a‖]
  apply (div_le_iff₀ hnorm).mp
  apply le_value K rates
  intro z
  apply (div_le_iff₀ hnorm).mpr
  simpa only [cost_smul, mul_comm] using value_le_cost K rates ht (a • f) (a • z)

theorem value_smul {t : ℝ} (ht : 0 ≤ t) (a : K) (f : Lp K 1 haar) :
    value K rates t (a • f) = ‖a‖ * value K rates t f := by
  apply le_antisymm (value_smul_le K rates ht a f)
  by_cases ha : a=0
  · simp only [ha, zero_smul, norm_zero, zero_mul, value_zero K rates ht]
    exact le_rfl
  have h := mul_le_mul_of_nonneg_left
    (value_smul_le K rates ht a⁻¹ (a • f)) (norm_nonneg a)
  simpa only [inv_smul_smul₀ ha, norm_inv, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul] using h

end PL1.KFunctional
