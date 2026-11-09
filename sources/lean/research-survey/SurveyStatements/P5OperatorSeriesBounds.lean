import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Absolutely bounded series of actual continuous linear maps. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P5
variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem summable_operators_of_norm_bound {ι : Type*} (L : ι → X →L[𝕜] Y)
    (b : ι → ℝ) (hb : Summable b) (hL : ∀ i, ‖L i‖ ≤ b i) : Summable L :=
  hb.of_norm_bounded hL

theorem norm_operator_tsum_le {ι : Type*} (L : ι → X →L[𝕜] Y)
    (b : ι → ℝ) (hb : Summable b) (hL : ∀ i, ‖L i‖ ≤ b i) :
    ‖∑' i, L i‖ ≤ ∑' i, b i := by
  have hnorm : Summable (fun i => ‖L i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hL hb
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hL hb)

theorem operator_tsum_apply {ι : Type*} (L : ι → X →L[𝕜] Y)
    (b : ι → ℝ) (hb : Summable b) (hL : ∀ i, ‖L i‖ ≤ b i) (x : X) :
    (∑' i, L i) x = ∑' i, L i x := by
  exact (ContinuousLinearMap.apply 𝕜 Y x).map_tsum (hb.of_norm_bounded hL)

end SurveyStatements.P5
