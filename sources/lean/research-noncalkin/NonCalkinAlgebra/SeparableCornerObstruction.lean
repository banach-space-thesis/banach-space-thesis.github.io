import NonCalkinAlgebra.QuotientIsoEquiv
import NonCalkinAlgebra.CalkinCornersFromLifting

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 TopologicalSpace Set
universe u v
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]
  (hLift : IdempotentLiftingStatement.{v})
  (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

theorem coefficient_idempotent_in_quotient (iso : OperatorQuotientIso X convention (matrixAlgebra D)) :
    let e := iso.toContinuousLinearEquiv.symm (canonicalMatrixUnit D 0 0)
    e * e = e := by
  dsimp
  rw [← iso.symm_map_mul]
  have hp := (matrixCornerModel D 0).idempotent
  rw [hp]

include hLift

theorem not_representable_separable_from_lifting [SeparableSpace X]
    (hD : ∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace ℂ Y]
      [CompleteSpace Y] [SeparableSpace Y],
      ¬ Nonempty (OperatorQuotientIso Y convention D)) :
    ¬ Nonempty (OperatorQuotientIso X convention (matrixAlgebra D)) := by
  rintro ⟨iso⟩
  let p := canonicalMatrixUnit D 0 0
  let e := iso.toContinuousLinearEquiv.symm p
  have he : e * e = e := coefficient_idempotent_in_quotient D X convention iso
  obtain ⟨C, hCsep⟩ := separable_calkin_corner_from_lifting hLift X convention e he
  letI : SeparableSpace C.subspace := hCsep
  exact hD C.subspace ⟨coefficientQuotientIsoOfCorner iso (matrixCornerModel D 0) C
    (iso.toContinuousLinearEquiv.apply_symm_apply p)⟩

theorem not_representable_separable_corner_from_lifting
    (hD : ∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace ℂ Y]
      [CompleteSpace Y] [SeparableSpace Y],
      ¬ Nonempty (OperatorQuotientIso Y convention D))
    (iso : OperatorQuotientIso X convention (matrixAlgebra D))
    (hrep : ∃ T : BoundedOperators X, IsSeparable (Set.range T) ∧
      operatorQuotientMap X convention T =
        iso.toContinuousLinearEquiv.symm (canonicalMatrixUnit D 0 0)) : False := by
  let p := canonicalMatrixUnit D 0 0
  let e := iso.toContinuousLinearEquiv.symm p
  have he : e * e = e := coefficient_idempotent_in_quotient D X convention iso
  obtain ⟨C, hCsep⟩ := separable_range_calkin_corner_from_lifting hLift X convention e he hrep
  letI : SeparableSpace C.subspace := hCsep
  exact hD C.subspace ⟨coefficientQuotientIsoOfCorner iso (matrixCornerModel D 0) C
    (iso.toContinuousLinearEquiv.apply_symm_apply p)⟩

end NonCalkinAlgebra
