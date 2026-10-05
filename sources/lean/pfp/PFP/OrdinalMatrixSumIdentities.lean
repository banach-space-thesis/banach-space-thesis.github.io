import JLMS.CZeroSumOperators
import Posets.CZeroContinuousAmplification

/-! The coordinatewise bounded map acts on actual c₀ single-coordinate
vectors. The identity keeps the index and fibre universes independent. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
open JLMS
universe u v
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096

theorem cZeroSum_mapCLM_single {I : Type u} {E F : I → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (A : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (i : I) (x : E i) :
    CZeroSum.mapCLM A hC hA (CZeroSum.single i x) = CZeroSum.single i (A i x) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp only [CZeroSum.mapCLM_apply, CZeroSum.single_apply_ne _ _ hj, map_zero]

end Posets.UniverseRegularMatrix
