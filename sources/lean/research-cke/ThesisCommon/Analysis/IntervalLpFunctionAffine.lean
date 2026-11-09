import ThesisCommon.Analysis.LebesgueLpTransport
import ThesisCommon.Analysis.LebesgueLpMeasureScale
import Mathlib.MeasureTheory.Group.Measure

/-! Affine identification of a nondegenerate dyadic interval with `[0,1]`,
including the exact normalization of Lebesgue measure and the `Lp` norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon

def intervalLpAffineEquiv (a : ℝ) (ha : 0 < a) : ℝ ≃ᵐ ℝ :=
  ((Homeomorph.mulLeft₀ a ha.ne').trans (Homeomorph.addLeft a)).toMeasurableEquiv

theorem intervalLpAffineEquiv_apply (a : ℝ) (ha : 0 < a) (x : ℝ) :
    intervalLpAffineEquiv a ha x = a + a * x := rfl

theorem intervalLpAffineMeasure (a : ℝ) (ha : 0 < a) :
    MeasurePreserving (intervalLpAffineEquiv a ha) volume
      (ENNReal.ofReal a⁻¹ • volume) := by
  refine ⟨(intervalLpAffineEquiv a ha).measurable, ?_⟩
  change Measure.map ((fun x : ℝ => a + x) ∘ (fun x : ℝ => a * x)) volume = _
  rw [← Measure.map_map (measurable_const_add a) (measurable_const_mul a),
    Real.map_volume_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha),
    Measure.map_smul, map_add_left_eq_self]

theorem intervalLpAffine_preimage (a : ℝ) (ha : 0 < a) :
    intervalLpAffineEquiv a ha ⁻¹' Ioc a (2 * a) = Ioc 0 1 := by
  ext x
  change (a < a + a * x ∧ a + a * x ≤ 2 * a) ↔ 0 < x ∧ x ≤ 1
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · exact (mul_pos_iff_of_pos_left ha).mp (by linarith)
    · exact (mul_le_mul_left ha).mp (by linarith : a * x ≤ a * 1)
  · rintro ⟨h₁, h₂⟩
    constructor
    · have := mul_pos ha h₁
      linarith
    · have := (mul_le_mul_left ha).mpr h₂
      nlinarith

theorem intervalLpAffineMeasure_restrict (a : ℝ) (ha : 0 < a) :
    MeasurePreserving (intervalLpAffineEquiv a ha)
      (volume.restrict (Icc (0 : ℝ) 1))
      (ENNReal.ofReal a⁻¹ • volume.restrict (Ioc a (2 * a))) := by
  have h := (intervalLpAffineMeasure a ha).restrict_preimage (s := Ioc a (2 * a)) measurableSet_Ioc
  simpa only [intervalLpAffine_preimage, restrict_Ioc_eq_restrict_Icc,
    Measure.restrict_smul] using h

/-- Exact normalized affine block isometry, valid over both real and complex scalars. -/
def intervalLpFunctionAffine (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (a : ℝ) (ha : 0 < a) :
    Lp 𝕜 p.val (volume.restrict (Ioc a (2 * a))) ≃ₗᵢ[𝕜] IntervalLp 𝕜 p :=
  (lebesgueLpMeasureScaleEquiv (𝕜 := 𝕜) hp (ENNReal.ofReal a⁻¹)
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) ENNReal.ofReal_ne_top).symm.trans
    (lebesgueLpTransport (intervalLpAffineEquiv a ha) (intervalLpAffineMeasure_restrict a ha))

end ThesisCommon
