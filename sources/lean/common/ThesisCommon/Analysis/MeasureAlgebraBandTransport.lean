import ThesisCommon.Analysis.MeasureAlgebraIntegral
import ThesisCommon.Analysis.IntegralPrincipalBand
import ThesisCommon.Analysis.OperatorTransportEquiv
import ThesisCommon.Analysis.OperatorOrderTransport
import ThesisCommon.Analysis.BandIdealTransport

/-! Arbitrary finite measure-algebra isomorphisms preserve the genuine
integral and singular bands. The proof uses the constructed L1 lift and the
proved principal-band characterization; no spatiality or countable
generation assumption on either replacement space is required. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
variable (Φ : MeasureAlgebraIso μ μ') (Ψ : MeasureAlgebraIso ν ν')

def measureAlgebraOperatorEquiv :
    (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) ≃ₗᵢ[ℝ] (Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 ν') :=
  operatorTransportLinearIsometryEquiv Φ.lOneEquiv Ψ.lOneEquiv

def measureAlgebraOperatorOrderIso :
    (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) ≃o (Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 ν') :=
  operatorTransportOrderIso Φ.lOneEquiv Ψ.lOneEquiv Φ.lOneEquiv_le_iff Ψ.lOneEquiv_le_iff

theorem measureAlgebraOperatorEquiv_rankOne :
    measureAlgebraOperatorEquiv Φ Ψ (integralRankOne μ ν) = integralRankOne μ' ν' := by
  apply ContinuousLinearMap.ext
  intro f
  change Ψ.lOneEquiv (integralRankOne μ ν (Φ.lOneEquiv.symm f)) = integralRankOne μ' ν' f
  rw [integralRankOne_apply, integralRankOne_apply, map_smul, Ψ.lOneEquiv_one,
    Φ.integral_lOneEquiv_symm]

theorem measureAlgebraOperatorEquiv_abs (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    measureAlgebraOperatorEquiv Φ Ψ |T| = |measureAlgebraOperatorEquiv Φ Ψ T| := by
  let e := measureAlgebraOperatorEquiv Φ Ψ
  have h : e (T ⊔ -T) = e T ⊔ e (-T) := (measureAlgebraOperatorOrderIso Φ Ψ).map_sup T (-T)
  simpa only [map_neg] using h

theorem measureAlgebraOperatorEquiv_inf (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    measureAlgebraOperatorEquiv Φ Ψ (S ⊓ T) =
      measureAlgebraOperatorEquiv Φ Ψ S ⊓ measureAlgebraOperatorEquiv Φ Ψ T :=
  (measureAlgebraOperatorOrderIso Φ Ψ).map_inf S T

theorem IsIntegralOperator.measureAlgebraTransport
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hK : IsIntegralOperator K) :
    IsIntegralOperator (measureAlgebraOperatorEquiv Φ Ψ K) := by
  let e := measureAlgebraOperatorEquiv Φ Ψ
  let I := (integralOperatorSubmodule μ' ν').comap e.toLinearEquiv.toLinearMap
  have hI : IsOrderClosedIdeal I :=
    integralOperatorOrderClosedIdeal.comap_linearOrderIso e.toLinearEquiv
      (measureAlgebraOperatorOrderIso Φ Ψ) (fun _ => rfl)
  have hJ : integralRankOne μ ν ∈ I := by
    change IsIntegralOperator (measureAlgebraOperatorEquiv Φ Ψ (integralRankOne μ ν))
    rw [measureAlgebraOperatorEquiv_rankOne]
    exact integralRankOne_isIntegral
  exact integralOperatorSubmodule_le_of_rankOne_mem hI hJ hK

theorem measureAlgebraOperatorEquiv_symm_apply (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    measureAlgebraOperatorEquiv Φ.symm Ψ.symm (measureAlgebraOperatorEquiv Φ Ψ T) = T := by
  change operatorTransport Φ.symm.lOneEquiv Ψ.symm.lOneEquiv
    (operatorTransport Φ.lOneEquiv Ψ.lOneEquiv T) = T
  rw [Φ.lOneEquiv_symm_eq, Ψ.lOneEquiv_symm_eq]
  exact operatorTransport_symm _ _ T

theorem isIntegralOperator_measureAlgebraTransport_iff
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsIntegralOperator (measureAlgebraOperatorEquiv Φ Ψ K) ↔ IsIntegralOperator K := by
  refine ⟨?_, IsIntegralOperator.measureAlgebraTransport Φ Ψ⟩
  intro hK
  have h := hK.measureAlgebraTransport Φ.symm Ψ.symm
  rwa [measureAlgebraOperatorEquiv_symm_apply] at h

theorem isSingularOperator_measureAlgebraTransport_iff
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator (measureAlgebraOperatorEquiv Φ Ψ S) ↔ IsSingularOperator S := by
  let e := measureAlgebraOperatorEquiv Φ Ψ
  have hinf (T U) : e (|T| ⊓ |U|) = |e T| ⊓ |e U| := by
    rw [measureAlgebraOperatorEquiv_inf, measureAlgebraOperatorEquiv_abs,
      measureAlgebraOperatorEquiv_abs]
  constructor
  · intro hS K hK
    apply e.injective
    rw [hinf, map_zero]
    exact hS (e K) (hK.measureAlgebraTransport Φ Ψ)
  · intro hS K hK
    obtain ⟨H, rfl⟩ := e.surjective K
    change |e S| ⊓ |e H| = 0
    rw [← hinf, hS H ((isIntegralOperator_measureAlgebraTransport_iff Φ Ψ H).mp hK), map_zero]

theorem integralBandProjection_measureAlgebraTransport
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    integralBandProjection (measureAlgebraOperatorEquiv Φ Ψ T) =
      measureAlgebraOperatorEquiv Φ Ψ (integralBandProjection T) := by
  let e := measureAlgebraOperatorEquiv Φ Ψ
  have hI : IsIntegralOperator (e (integralBandProjection T)) :=
    (integralBandProjection_isIntegral T).measureAlgebraTransport Φ Ψ
  have hS : IsSingularOperator (e (T - integralBandProjection T)) :=
    (isSingularOperator_measureAlgebraTransport_iff Φ Ψ _).mpr
      (integralBandProjection_residual_singular T)
  have hdecomp : e T = e (integralBandProjection T) + e (T - integralBandProjection T) := by
    rw [← map_add]
    congr 1
    abel
  change integralBandProjection (e T) = e (integralBandProjection T)
  rw [hdecomp, map_add, integralBandProjection_eq_self hI,
    (integralBandProjection_eq_zero_iff _).mpr hS, add_zero]

end ThesisCommon
