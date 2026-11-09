import ThesisCommon.Analysis.LpHaarBackwardMass
import ThesisCommon.Analysis.LebesgueLpToOne

/-! Backward Haar interactions vanish for every actual interval Lp
function. The proof uses contractive L1 inclusion and dyadic averaging,
and is valid for complex scalars and even the bounded endpoint. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

theorem lebesgueLpToOne_HaarCoefficient (n k : ℕ) (hk : k < 2 ^ n) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k (lebesgueLpToOne f) =
      lpHaarDyadicCoefficient 𝕜 p n k f := by
  rw [lpHaarDyadicCoefficient_apply_integrals 𝕜 ⟨1, le_rfl⟩ n k hk,
    lpHaarDyadicCoefficient_apply_integrals 𝕜 p n k hk]
  congr 2 <;> exact integral_congr_ae (ae_restrict_of_ae (lebesgueLpToOne_coe f))

theorem lpHaar_backward_mass_tendsto_zero (f : IntervalLp 𝕜 p) :
    Tendsto (fun n => ∑ k : Fin (2 ^ n), intervalLpDyadicRadius n *
      ‖lpHaarDyadicCoefficient 𝕜 p n k f‖) atTop (𝓝 0) := by
  have h := lpHaar_L1_backward_mass_tendsto_zero 𝕜 (lebesgueLpToOne f)
  simpa only [lebesgueLpToOne_HaarCoefficient 𝕜 p _ _ (Fin.isLt _)] using h

end ThesisCommon
