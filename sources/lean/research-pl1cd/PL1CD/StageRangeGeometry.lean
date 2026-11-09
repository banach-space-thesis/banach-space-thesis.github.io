import PL1CD.StageCarrier
import PL1CD.Cardinality
import PL1.MainTheoremA
import PL1.RNPTransport

noncomputable section
open MeasureTheory
open scoped NNReal

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

theorem stageProjectionFamily_range_not_RNP (a : ContinuumIndex) :
    ¬ @PL1.HasRadonNikodymProperty.{_, 0}
      (PL1.UnderlyingReal 𝕜 (stageProjectionFamily 𝕜 a).range)
      (inferInstanceAs (NormedAddCommGroup (stageProjectionFamily 𝕜 a).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (stageProjectionFamily 𝕜 a).range) := by
  let rates := StageParameters.rates (AlmostDisjoint.family a)
  obtain ⟨B, hB, hmB, hnoise⟩ := StageParameters.exists_common_null_carrier
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)
  have hνB : PL1.Noise.resolventMeasure rates (PL1.Noise.dyadicTime 0) B ≠ 0 := by
    rw [PL1.Noise.resolventMeasure_carrier rates (PL1.Noise.dyadicTime 0).property B hB hnoise]
    exact one_ne_zero
  have hsource : ¬ @PL1.HasRadonNikodymProperty.{_, 0}
      (PL1.UnderlyingReal 𝕜 (PL1.Noise.projection 𝕜 rates).range)
      (inferInstanceAs (NormedAddCommGroup (PL1.Noise.projection 𝕜 rates).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (PL1.Noise.projection 𝕜 rates).range) := by
    change ¬ @PL1.HasRadonNikodymProperty.{_, 0}
      ((PL1.Noise.dyadicSystem 𝕜 rates).projection.range) _
      (NormedSpace.restrictScalars ℝ 𝕜 (PL1.Noise.dyadicSystem 𝕜 rates).projection.range)
    rw [PL1.DyadicSystem.projection_range]
    exact PL1.Noise.intrinsic_not_RNP_of_resolvent_carrier_scalar 𝕜 rates B hmB hνB
  intro h
  exact hsource ((PL1.RNPTransport.hasRadonNikodymProperty_restrictScalars_iff
    ((PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).rangeEquiv
      (PL1.Noise.projection 𝕜 rates))).mpr h)

theorem stageProjectionFamily_range_not_lattice (a : ContinuumIndex) :
    ¬ @PL1.HasEquivalentRealLatticeNorm
      (PL1.UnderlyingReal 𝕜 (stageProjectionFamily 𝕜 a).range)
      (inferInstanceAs (NormedAddCommGroup (stageProjectionFamily 𝕜 a).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (stageProjectionFamily 𝕜 a).range) := by
  let : CompleteSpace (stageProjectionFamily 𝕜 a).range :=
    (intervalProjection_range_closed 𝕜 _).isComplete.completeSpace_coe
  let := intervalL1_separableSpace 𝕜
  let : NormedSpace ℝ (stageProjectionFamily 𝕜 a).range :=
    NormedSpace.restrictScalars ℝ 𝕜 (stageProjectionFamily 𝕜 a).range
  change ¬ PL1.HasEquivalentRealLatticeNorm (stageProjectionFamily 𝕜 a).range
  apply PL1.not_hasEquivalentRealLatticeNorm_of_structural_RNP PL1.separableSchurLatticeRNP
  · exact (PL1.hasSchurProperty_iff_underlyingReal 𝕜 _).mp
      (stageProjectionFamily_range_schur 𝕜 a)
  · exact stageProjectionFamily_range_not_RNP 𝕜 a

theorem stageProjectionFamily_additionalStrongSpec :
    TheoremCAdditionalStrongSpec 𝕜 (stageProjectionFamily 𝕜) :=
  fun a => ⟨stageProjectionFamily_range_infiniteDimensional 𝕜 a,
    stageProjectionFamily_range_schur 𝕜 a,
    stageProjectionFamily_range_not_RNP 𝕜 a,
    stageProjectionFamily_range_not_lattice 𝕜 a⟩

end PL1CD
