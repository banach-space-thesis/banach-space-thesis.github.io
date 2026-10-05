import LPCK.OrdinalBackground
import ThesisCommon.Analysis.EllOneCotype
import ThesisCommon.Analysis.CotypeEquiv
import ThesisCommon.Analysis.DualCotypePreservation

/-! The genuine Rudin representation supplies finite cotype of every
ordinal C-space dual, over real and complex scalars and arbitrary universes. -/
noncomputable section
namespace LPCK
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalContinuousDual_hasFiniteCotype (α : Ordinal) :
    HasFiniteCotype (OrdinalContinuous 𝕜 α →L[𝕜] 𝕜) := by
  let e := ordinalContinuousDualEllOneEquiv (𝕜 := 𝕜) α
  exact ⟨2, _, (scalar_ellOne_hasRademacherCotype_two (𝕜 := 𝕜)
    (OrdinalInterval α)).two_of_equiv (𝕜 := 𝕜) e⟩

theorem ordinal_ellOne_hasUPFP_of_base (α : Ordinal)
    (hX : HasUPFP 𝕜 (OrdinalContinuous 𝕜 α)) :
    HasUPFP 𝕜 (EllOneSum ℕ (OrdinalContinuous 𝕜 α)) :=
  hX.ellOne_of_dualFiniteCotype (ordinalContinuousDual_hasFiniteCotype α)

end LPCK
