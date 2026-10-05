import Posets.CountableOrdinalPFPBandSum
import PosetsCommon.CountableCZero
import ThesisCommon.Analysis.CountableOrdinalContinuous
import JLMS.CompactCZeroEquiv

/-! The closed ordinal interval conventions are related by an actual
continuous-function equivalence. Countability supplies separability. -/

noncomputable section
open Set Topology TopologicalSpace ThesisCommon
universe u
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem ordinalIic_compact (θ : Ordinal.{u}) : IsCompact (Iic θ) := by
  have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
  rw [← heq]
  exact isCompact_Icc

theorem ordinalIic_countable_of_card {θ : Ordinal.{u}} (hc : θ.card ≤ Cardinal.aleph0) :
    Countable (Iic θ) := by
  have heq : Iic θ = Icc (0 : Ordinal.{u}) θ := by ext x; simp
  rw [heq]
  exact ordinalInterval_countable (Cardinal.lt_ord.mpr (hc.trans_lt Cardinal.aleph0_lt_aleph_one))

local instance countableOrdinalPFPAmbientCompact (θ : Ordinal.{u}) : CompactSpace (Iic θ) :=
  isCompact_iff_compactSpace.mp (ordinalIic_compact θ)

def ordinalIicContinuousCZeroEquiv (θ : Ordinal.{u}) :
    OrdinalContinuous 𝕜 θ ≃L[𝕜] JLMS.CZero 𝕜 (Iic θ) :=
  (continuousMapHomeomorphEquiv (Homeomorph.setCongr
    (show Icc (0 : Ordinal.{u}) θ = Iic θ by ext x; simp))).trans
    JLMS.compactContinuousCZeroEquiv.toContinuousLinearEquiv

theorem ordinalIicCZero_separable {θ : Ordinal.{u}} (hc : θ.card ≤ Cardinal.aleph0) :
    SeparableSpace (JLMS.CZero 𝕜 (Iic θ)) := by
  letI := ordinalIic_countable_of_card hc
  exact countable_cZero_separable (𝕜 := 𝕜) (Iic θ)

end Posets
