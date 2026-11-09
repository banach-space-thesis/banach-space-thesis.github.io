import NonCalkinAlgebra.SeparableCornerObstruction
import NonCalkinAlgebra.SeparableRangeQuotient
import NonCalkinAlgebra.ConstructionTheorem

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 TopologicalSpace
universe u v

variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

/-- Every proper closed ideal of the constructed algebra is zero or its
specified matrix ideal. -/
theorem matrixAlgebra_proper_closed_ideal (hD : IsTopologicallySimple D)
    (I : TwoSidedIdeal (matrixAlgebra D)) (hc : IsClosed (I : Set (matrixAlgebra D)))
    (ht : I ≠ ⊤) : I = ⊥ ∨ I = matrixIdeal D := by
  by_cases hz : I = ⊥
  · exact Or.inl hz
  obtain ⟨J, hJ, hu⟩ := matrixAlgebra_has_exactly_one_ideal D hD
  have hI : I = J := hu I ⟨hc, hz, ht⟩
  have hm : matrixIdeal D = J := hu (matrixIdeal D) (matrixIdeal_isNonzeroProperClosed D)
  exact Or.inr (hI.trans hm.symm)

variable [Nontrivial D]

/-- The separable and nonseparable cases of the last proof in Section 5.
Both prerequisite theorems remain explicit hypotheses of this reduction. -/
theorem matrixAlgebra_not_representable_from_prerequisites
    (hLift : IdempotentLiftingStatement.{v}) (hDsimple : IsTopologicallySimple D)
    (convention : QuotientConvention)
    (hD : ∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace ℂ Y]
      [CompleteSpace Y] [SeparableSpace Y],
      ¬ Nonempty (OperatorQuotientIso Y convention D))
    (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] :
    ¬ Nonempty (OperatorQuotientIso X convention (matrixAlgebra D)) := by
  classical
  by_cases hX : SeparableSpace X
  · letI : SeparableSpace X := hX
    exact not_representable_separable_from_lifting D hLift X convention hD
  rintro ⟨iso⟩
  let R := separableRangeQuotientIdeal X convention
  let f := iso.toContinuousAlgEquiv.symm
  let I : TwoSidedIdeal (matrixAlgebra D) := R.comap f
  have hmem (a : matrixAlgebra D) : a ∈ I ↔ f a ∈ R := TwoSidedIdeal.mem_comap f
  have hIclosed : IsClosed (I : Set (matrixAlgebra D)) := by
    have heq : (I : Set (matrixAlgebra D)) = f ⁻¹' (R : Set (OperatorQuotient X convention)) := by
      ext a
      exact hmem a
    rw [heq]
    exact (separableRangeQuotientIdeal_isClosed X convention).preimage f.continuous
  have hIproper : I ≠ ⊤ := by
    intro htop
    apply separableRangeQuotientIdeal_ne_top X convention hX
    apply le_antisymm le_top
    intro z hz
    obtain ⟨a, rfl⟩ := f.surjective z
    exact (hmem a).mp (by rw [htop]; trivial)
  rcases matrixAlgebra_proper_closed_ideal D hDsimple I hIclosed hIproper with hz | hm
  · have hsep : ∀ T : BoundedOperators X, IsSeparable (Set.range T) →
        T ∈ operatorIdeal X convention := by
      intro T hT
      let z := operatorQuotientMap X convention T
      have hzR : z ∈ R := (mem_separableRangeQuotientIdeal X convention z).mpr
        ⟨T, (mem_separableRangeOperators T).mpr hT, rfl⟩
      have haI : iso.toContinuousAlgEquiv z ∈ I := (hmem _).mpr (by
        simpa only [f, ContinuousAlgEquiv.symm_apply_apply] using hzR)
      have ha0 : iso.toContinuousAlgEquiv z = 0 := by
        simpa only [hz, TwoSidedIdeal.mem_bot] using haI
      have hz0 : z = 0 := iso.toContinuousAlgEquiv.injective
        (ha0.trans (_root_.map_zero iso.toContinuousAlgEquiv).symm)
      exact (operatorQuotientMap_eq_zero X convention T).mp hz0
    exact not_representable_of_separableRange_in_operatorIdeal D X convention hsep ⟨iso⟩
  · have hpI : canonicalMatrixUnit D 0 0 ∈ I := by
      rw [hm]
      exact matrixTheta_mem_matrixIdeal D 0 0 1
    have hpR := (hmem _).mp hpI
    exact not_representable_separable_corner_from_lifting D hLift X convention hD iso
      (exists_separable_representative X convention hpR)

/-- Theorem 1.1 reduced to the coefficient-existence theorem and the spectral
lifting theorem, with all construction and representation arguments proved.
This theorem does not assert either prerequisite. -/
theorem main_from_prerequisites
    (hCoefficient : CoefficientExistenceStatement.{v})
    (hLift : IdempotentLiftingStatement.{v}) : MainStatement.{v} := by
  obtain ⟨D, hDnorm, hDdensity, hDsimple, hDavoid⟩ := hCoefficient
  letI : NormOneClass D.Carrier := ⟨hDnorm⟩
  refine ⟨matrixBanachAlgebra D.Carrier, matrixAlgebra_density_continuum D.Carrier hDdensity,
    matrixAlgebra_has_exactly_one_ideal D.Carrier hDsimple, ?_⟩
  intro convention X _ _ _
  exact matrixAlgebra_not_representable_from_prerequisites D.Carrier hLift hDsimple
    convention (hDavoid convention) X

end NonCalkinAlgebra
