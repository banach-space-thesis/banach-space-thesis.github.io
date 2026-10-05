import ThesisCommon.Analysis.GowersMaureyShiftDefects
import ThesisCommon.Analysis.GowersMaureyAdjointSpreads
import ThesisCommon.Analysis.HyperplaneScalarExtension

/-! Actual hyperplane isomorphisms of the shift-generated space. The
right shift identifies the space isometrically with the kernel of its
first coordinate. The common-transverse-vector argument then transfers
this isomorphism to every genuine closed hyperplane. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem completedCoordinate_zero_rightShift (D : ConstructionData 𝕜) (x : ShiftSpace D) :
    completedCoordinate D 0 (completedSpread D 0 1 x) = 0 := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_eq ((completedCoordinate D 0).continuous.comp
      (completedSpread D 0 1).continuous) continuous_const
  · intro a
    rw [completedSpread_denseEmbedding, completedCoordinate_denseEmbedding]
    change spread 0 1 (PreSpace.coefficients a) 0 = 0
    rw [spread_apply]
    norm_num

def rightShiftCoordinateKernelEquiv (D : ConstructionData 𝕜) :
    ShiftSpace D ≃L[𝕜] LinearMap.ker (completedCoordinate D 0).toLinearMap := by
  let J := (completedSpread D 0 1).codRestrict
    (LinearMap.ker (completedCoordinate D 0).toLinearMap)
    (fun x => completedCoordinate_zero_rightShift D x)
  let R := (completedSpread D 1 0).comp
    (LinearMap.ker (completedCoordinate D 0).toLinearMap).subtypeL
  refine ContinuousLinearEquiv.equivOfInverse J R ?_ ?_
  · intro x
    exact DFunLike.congr_fun (completedSpread_left_right D 1) x
  · intro y
    apply Subtype.ext
    have hh := DFunLike.congr_fun (completedSpread_right_left_defect D) y.val
    change y.val - completedSpread D 0 1 (completedSpread D 1 0 y.val) =
      completedCoordinate D 0 y.val • basisVector D 0 at hh
    have hy : completedCoordinate D 0 y.val = 0 := y.property
    rw [hy, zero_smul] at hh
    exact (sub_eq_zero.mp hh).symm

theorem rightShiftCoordinateKernelEquiv_norm (D : ConstructionData 𝕜) (x : ShiftSpace D) :
    ‖rightShiftCoordinateKernelEquiv D x‖ = ‖x‖ :=
  completedRightShift_norm D 1 x

def rightShiftCoordinateKernelIsometry (D : ConstructionData 𝕜) :
    ShiftSpace D ≃ₗᵢ[𝕜] LinearMap.ker (completedCoordinate D 0).toLinearMap :=
  { (rightShiftCoordinateKernelEquiv D).toLinearEquiv with
    norm_map' := rightShiftCoordinateKernelEquiv_norm D }

theorem shiftSpace_scalarExtension (D : ConstructionData 𝕜) :
    IsIsomorphicToScalarExtension 𝕜 (ShiftSpace D) := by
  let f := completedCoordinate D 0
  have hH := scalarFunctional_closedHyperplane f (completedCoordinate_ne_zero D 0)
  exact ⟨(closedHyperplaneProductEquiv _ hH).trans
    ((rightShiftCoordinateKernelEquiv D).symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))⟩

theorem shiftSpace_everyHyperplane (D : ConstructionData 𝕜) :
    IsIsomorphicToEveryHyperplane 𝕜 (ShiftSpace D) :=
  (shiftSpace_scalarExtension D).everyHyperplane

end ThesisCommon.GowersMaurey
