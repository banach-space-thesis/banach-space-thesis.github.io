import CKEUPFP.ContinuousMapVectorLift
import CKEUPFP.Isomorphism
import CKEUPFP.MainStatements
import ThesisCommon.Analysis.CompactMetricMilutin
import Mathlib.Topology.MetricSpace.PiNat

/-!
# The vector-valued Milutin reduction

The vendored scalar Milutin theorem has a complete proof, rather than a
scalar-isomorphism hypothesis. Its actual scalar equivalence is lifted by
finite-rank approximation and Hahn--Banach to any Banach range space.
-/

noncomputable section

namespace CKEUPFP

theorem cantorSpace_uncountable : Uncountable CantorSpace := by
  apply uncountable_iff_forall_not_surjective.mpr
  intro f hf
  let d : CantorSpace := fun n => if f n n = 0 then 1 else 0
  obtain ⟨n, hn⟩ := hf d
  have hdiag : f n n ≠ d n := by
    by_cases hz : f n n = 0 <;> simp [d, hz]
  exact hdiag (congrFun hn n)

variable {𝕜 : Type*} [RCLike 𝕜]
variable (K : Type*) [TopologicalSpace K] [TopologicalSpace.MetrizableSpace K]
  [CompactSpace K] [Uncountable K]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- An actual bounded linear equivalence between the two vector-valued spaces. -/
def milutinVectorEquiv : C(K, E) ≃L[𝕜] C(CantorSpace, E) := by
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  letI : MetricSpace CantorSpace := PiNat.metricSpace
  letI : Uncountable CantorSpace := cantorSpace_uncountable
  exact continuousMapVectorEquiv (ThesisCommon.milutinCompactMetricEquiv K CantorSpace)

theorem hasUPFP_continuousMap_iff_cantor :
    HasUPFP 𝕜 C(K, E) ↔ HasUPFP 𝕜 C(CantorSpace, E) :=
  hasUPFP_iff_of_equiv (milutinVectorEquiv (𝕜 := 𝕜) K E)

variable [TopologicalSpace.SeparableSpace E]

/-- Reduce the paper's complete main statement to its quantitative Cantor case. -/
theorem transferTheorem_of_cantor
    (h : CantorQuantitativeTransfer 𝕜 E) : TransferTheorem 𝕜 K E := by
  intro hno hE
  obtain ⟨C, hC⟩ := hE
  have hCantor : HasUPFP 𝕜 C(CantorSpace, E) := ⟨4 * C / 3, h hno C hC⟩
  exact (hasUPFP_continuousMap_iff_cantor (𝕜 := 𝕜) K E).mpr hCantor

end CKEUPFP
