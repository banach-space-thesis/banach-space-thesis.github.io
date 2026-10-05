import ThesisCommon.Analysis.IntegralOperatorOrderClosed
import ThesisCommon.Analysis.IntegralOperatorLattice
import ThesisCommon.Analysis.BandProjection
import ThesisCommon.Analysis.L1RegularOperators

/-! Integral/singular decomposition of actual bounded real L1 operators
on sigma-finite spaces. Both the integral band and its projection are proved. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- Lattice disjointness from every actual integral operator. -/
def IsSingularOperator (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : Prop :=
  ∀ K, IsIntegralOperator K → |S| ⊓ |K| = 0

variable [SigmaFinite μ] [SigmaFinite ν]

theorem integralOperatorOrderClosedIdeal : IsOrderClosedIdeal (integralOperatorSubmodule μ ν) where
  solid := integralOperatorSubmodule_solid
  closed := by
    intro s hs hI hpos hdir S hS
    exact IsIntegralOperator.of_directed_sup_sigmaFinite hs hI hpos hdir hS

/-- The constructed integral-part projection on the full bounded-operator space. -/
def integralBandProjection : (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) →L[ℝ] (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :=
  bandProjection integralOperatorOrderClosedIdeal

theorem integralBandProjection_isIntegral (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsIntegralOperator (integralBandProjection T) := integralOperatorOrderClosedIdeal.bandProjection_mem T

theorem integralBandProjection_eq_self {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : IsIntegralOperator T) :
    integralBandProjection T = T := integralOperatorOrderClosedIdeal.bandProjection_eq_self hT

theorem integralBandProjection_idempotent (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    integralBandProjection (integralBandProjection T) = integralBandProjection T :=
  integralOperatorOrderClosedIdeal.bandProjection_idempotent T

theorem integralBandProjection_nonneg : 0 ≤ integralBandProjection (μ := μ) (ν := ν) :=
  integralOperatorOrderClosedIdeal.bandProjection_nonneg

theorem integralBandProjection_le_id : integralBandProjection (μ := μ) (ν := ν) ≤
    ContinuousLinearMap.id ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :=
  integralOperatorOrderClosedIdeal.bandProjection_le_id

theorem norm_integralBandProjection_le_one : ‖integralBandProjection (μ := μ) (ν := ν)‖ ≤ 1 :=
  integralOperatorOrderClosedIdeal.norm_bandProjection_le_one

theorem integralBandProjection_residual_singular (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator (T - integralBandProjection T) :=
  fun _ hK => integralOperatorOrderClosedIdeal.residual_disjoint T hK

theorem integralBandProjection_eq_zero_iff (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    integralBandProjection T = 0 ↔ IsSingularOperator T :=
  integralOperatorOrderClosedIdeal.bandProjection_eq_zero_iff T

/-- The complement is a genuine submodule, identified below with lattice
disjointness; no linear closure of the singularity predicate is assumed. -/
def singularOperatorSubmodule (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    Submodule ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :=
  LinearMap.ker (integralBandProjection (μ := μ) (ν := ν)).toLinearMap

theorem mem_singularOperatorSubmodule (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    T ∈ singularOperatorSubmodule μ ν ↔ IsSingularOperator T := integralBandProjection_eq_zero_iff T

theorem integral_singular_isCompl :
    IsCompl (integralOperatorSubmodule μ ν) (singularOperatorSubmodule μ ν) :=
  integralOperatorOrderClosedIdeal.bandProjection_isCompl

theorem exists_unique_integral_singular_decomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃! p : (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) × (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν),
      IsIntegralOperator p.1 ∧ IsSingularOperator p.2 ∧ T = p.1 + p.2 :=
  integralOperatorOrderClosedIdeal.exists_unique_band_decomposition T

end ThesisCommon
