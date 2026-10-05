import ThesisCommon.Analysis.MeasureAlgebraBandTransport
import ThesisCommon.Analysis.MeasureAlgebraIdentity

/-! The two source orientations of singular-operator preservation under
arbitrary finite measure-algebra isomorphisms. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']

theorem IsSingularOperator.measureAlgebra_precomp (Φ : MeasureAlgebraIso μ' μ)
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsSingularOperator S) :
    IsSingularOperator (S.comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap) := by
  have h := (isSingularOperator_measureAlgebraTransport_iff Φ.symm (MeasureAlgebraIso.refl ν) S).mpr hS
  have heq : measureAlgebraOperatorEquiv Φ.symm (MeasureAlgebraIso.refl ν) S =
      S.comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro f
    change (MeasureAlgebraIso.refl ν).lOneEquiv (S (Φ.symm.lOneEquiv.symm f)) = S (Φ.lOneEquiv f)
    rw [MeasureAlgebraIso.refl_lOneEquiv_apply, Φ.lOneEquiv_symm_eq]
    rfl
  rwa [heq] at h

theorem IsSingularOperator.measureAlgebra_postcomp (Ψ : MeasureAlgebraIso ν ν')
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsSingularOperator S) :
    IsSingularOperator (Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp S) := by
  have h := (isSingularOperator_measureAlgebraTransport_iff (MeasureAlgebraIso.refl μ) Ψ S).mpr hS
  have heq : measureAlgebraOperatorEquiv (MeasureAlgebraIso.refl μ) Ψ S =
      Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp S := by
    apply ContinuousLinearMap.ext
    intro f
    change Ψ.lOneEquiv (S ((MeasureAlgebraIso.refl μ).lOneEquiv.symm f)) = Ψ.lOneEquiv (S f)
    rw [MeasureAlgebraIso.refl_lOneEquiv]
    rfl
  rwa [heq] at h

end ThesisCommon
