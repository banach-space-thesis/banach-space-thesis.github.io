import ThesisCommon.Analysis.GowersMaureyCoordinates
import ThesisCommon.Analysis.StrictlySingularFiniteRank

/-! The unilateral boundary defect is an actual rank-one operator. In
particular, Laurent representatives are not themselves an algebra of
operators; the multiplicative identification must take place in a quotient. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem spread_right_left_defect (x : C00 𝕜) :
    x - spread 0 1 (spread 1 0 x) = Finsupp.single 0 (x 0) := by
  have h : (LinearMap.id - (spread (𝕜 := 𝕜) 0 1).comp (spread 1 0)) =
      (Finsupp.lsingle 0).comp (Finsupp.lapply 0) := by
    apply Finsupp.lhom_ext
    intro i c
    by_cases hi : i = 0
    · subst i
      simp [spread_single]
    · have hpos : 1 ≤ i := by omega
      have heq : i - 1 + 1 = i := by omega
      simp [spread_single, hi, hpos, heq]
  exact DFunLike.congr_fun h x

theorem completedSpread_right_left_defect (D : ConstructionData 𝕜) :
    ContinuousLinearMap.id 𝕜 (ShiftSpace D) -
      (completedSpread D 0 1).comp (completedSpread D 1 0) =
      (completedCoordinate D 0).smulRight (basisVector D 0) := by
  apply ContinuousLinearMap.ext
  intro x
  change x - completedSpread D 0 1 (completedSpread D 1 0 x) =
    completedCoordinate D 0 x • basisVector D 0
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_id.sub ((completedSpread D 0 1).continuous.comp
        (completedSpread D 1 0).continuous))
      ((completedCoordinate D 0).continuous.smul continuous_const)
  · intro a
    rw [completedSpread_denseEmbedding, completedSpread_denseEmbedding,
      completedCoordinate_denseEmbedding]
    rw [basisVector, ← map_sub, ← map_smul]
    apply congrArg (denseEmbedding D)
    change PreSpace.coefficients a - spread 0 1 (spread 1 0 (PreSpace.coefficients a)) =
      (PreSpace.coefficients a) 0 • (Finsupp.single 0 (1 : 𝕜) : C00 𝕜)
    rw [spread_right_left_defect]
    simp

theorem completedCoordinate_ne_zero (D : ConstructionData 𝕜) (n : ℕ) :
    completedCoordinate D n ≠ 0 := by
  intro h
  have heq := DFunLike.congr_fun h (basisVector D n)
  simp at heq

theorem completedSpread_defect_finiteDimensional (D : ConstructionData 𝕜) :
    FiniteDimensional 𝕜 (LinearMap.range
      (ContinuousLinearMap.id 𝕜 (ShiftSpace D) -
        (completedSpread D 0 1).comp (completedSpread D 1 0)).toLinearMap) := by
  rw [completedSpread_right_left_defect]
  have hr : LinearMap.range
      ((completedCoordinate D 0).smulRight (basisVector D 0)).toLinearMap =
      Submodule.span 𝕜 {basisVector D 0} :=
    ContinuousLinearMap.range_smulRight_apply (completedCoordinate_ne_zero D 0) (basisVector D 0)
  rw [hr]
  infer_instance

theorem completedSpread_defect_strictlySingular (D : ConstructionData 𝕜) :
    IsStrictlySingularOperator
      (ContinuousLinearMap.id 𝕜 (ShiftSpace D) -
        (completedSpread D 0 1).comp (completedSpread D 1 0)) := by
  letI := completedSpread_defect_finiteDimensional D
  exact isStrictlySingularOperator_of_finiteDimensional_range _

end ThesisCommon.GowersMaurey
