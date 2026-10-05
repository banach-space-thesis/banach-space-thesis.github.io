import ThesisCommon.Analysis.ClosedFiniteDimensionalSum
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Operator.Banach

/-! A bounded below restriction to a closed finite-codimensional subspace
has closed full range. The complement is an actual finite-dimensional
submodule, and its image is added to the closed restricted range. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ContinuousLinearMap.isClosed_range_of_finiteCodimensional_lower_bound
    (T : X →L[𝕜] Y) (E : Submodule 𝕜 X) (hE : IsClosed (E : Set X))
    [FiniteDimensional 𝕜 (X ⧸ E)] {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : E, c * ‖x.val‖ ≤ ‖T x.val‖) :
    IsClosed (LinearMap.range T.toLinearMap : Set Y) := by
  letI : CompleteSpace E := hE.completeSpace_coe
  let A : E →L[𝕜] Y := T.comp E.subtypeL
  have ha : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ A := by
    apply A.antilipschitz_of_bound
    intro x
    have hh := mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hc.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh
  have hclosed : IsClosed (E.map T.toLinearMap : Set Y) := by
    have hr := ha.isClosed_range A.uniformContinuous
    convert hr using 1
    ext y
    exact ⟨fun ⟨x,hx,hxy⟩ => ⟨⟨x,hx⟩,hxy⟩,
      fun ⟨x,hxy⟩ => ⟨x.val,x.property,hxy⟩⟩
  obtain ⟨N,hN⟩ := E.exists_isCompl
  letI : FiniteDimensional 𝕜 N := (E.quotientEquivOfIsCompl N hN).finiteDimensional
  have hs := submodule_isClosed_sup_of_finiteDimensional_right
    (E.map T.toLinearMap) (N.map T.toLinearMap) hclosed
  rw [← Submodule.map_sup, hN.sup_eq_top, Submodule.map_top] at hs
  exact hs

end ThesisCommon
