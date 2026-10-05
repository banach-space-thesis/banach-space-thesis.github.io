import ThesisCommon.Analysis.ComplexIntegralKernelCoordinates
import ThesisCommon.Analysis.ComplexL1BandMembership
import ThesisCommon.Analysis.ComplexL1BandSingularity
import ThesisCommon.Analysis.IntegralOperatorBand

/-! The actual complex integral/singular decomposition on sigma-finite
spaces. Its projection is constructed from the proved real integral band;
membership is identified with genuine jointly measurable integral kernels. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def complexIntegralOperatorSubmodule (μ : Measure X) (ν : Measure Y) :
    Submodule ℂ (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) where
  carrier := {T | IsIntegralOperator T}
  zero_mem' := ⟨_,isIntegralKernel_zero_rclike⟩
  add_mem' := by
    rintro _ _ ⟨k,hk⟩ ⟨h,hh⟩
    exact ⟨_,hk.add_rclike hh⟩
  smul_mem' := by
    rintro c _ ⟨k,hk⟩
    exact ⟨_,hk.smul_rclike c⟩

/-- Disjointness of the actual complex modulus from all integral operators. -/
def IsComplexSingularOperator (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) : Prop :=
  ∀ K, IsIntegralOperator K → complexL1OperatorModulus S ⊓ complexL1OperatorModulus K = 0

variable [SigmaFinite μ] [SigmaFinite ν]

theorem isIntegralOperator_complex_iff_modulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsIntegralOperator T ↔ IsIntegralOperator (complexL1OperatorModulus T) := by
  exact (isIntegralOperator_complex_coordinates_iff T).trans
    (complexL1OperatorModulus_mem_iff integralOperatorOrderClosedIdeal T).symm

/-- The actual contractive complex-linear integral-part projection. -/
def complexIntegralBandProjection :
    (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) →L[ℂ] (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :=
  complexL1BandProjection integralOperatorOrderClosedIdeal

theorem complexIntegralBandProjection_eq_self_iff (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexIntegralBandProjection T = T ↔ IsIntegralOperator T :=
  (complexL1BandProjection_eq_self_iff_components integralOperatorOrderClosedIdeal T).trans
    (isIntegralOperator_complex_coordinates_iff T).symm

theorem complexIntegralBandProjection_idempotent (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexIntegralBandProjection (complexIntegralBandProjection T) = complexIntegralBandProjection T :=
  complexL1BandProjection_idempotent integralOperatorOrderClosedIdeal T

theorem complexIntegralBandProjection_isIntegral (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsIntegralOperator (complexIntegralBandProjection T) :=
  (complexIntegralBandProjection_eq_self_iff _).mp (complexIntegralBandProjection_idempotent T)

theorem complexIntegralBandProjection_eq_self {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hT : IsIntegralOperator T) : complexIntegralBandProjection T = T :=
  (complexIntegralBandProjection_eq_self_iff T).mpr hT

theorem norm_complexIntegralBandProjection_le_one :
    ‖complexIntegralBandProjection (μ := μ) (ν := ν)‖ ≤ 1 :=
  norm_complexL1BandProjection_le_one integralOperatorOrderClosedIdeal

theorem complexIntegralBandProjection_modulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (complexIntegralBandProjection T) =
      integralBandProjection (complexL1OperatorModulus T) :=
  complexL1BandProjection_modulus integralOperatorOrderClosedIdeal T

theorem complexIntegralBandProjection_residual_modulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (T-complexIntegralBandProjection T) =
      complexL1OperatorModulus T - integralBandProjection (complexL1OperatorModulus T) :=
  complexL1BandProjection_residual_modulus integralOperatorOrderClosedIdeal T

theorem complexIntegralBandProjection_eq_zero_iff (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexIntegralBandProjection S = 0 ↔ IsComplexSingularOperator S := by
  constructor
  · intro hS K hK
    have hz := (complexL1BandProjection_eq_zero_iff_modulus integralOperatorOrderClosedIdeal S).mp hS
    have hmem : complexL1OperatorModulus K ∈ integralOperatorSubmodule μ ν :=
      (isIntegralOperator_complex_iff_modulus K).mp hK
    have h := (integralOperatorOrderClosedIdeal.bandProjection_eq_zero_iff
      (complexL1OperatorModulus S)).mp hz (complexL1OperatorModulus K) hmem
    simpa only [abs_of_nonneg (show 0 ≤ complexL1OperatorModulus S from complexL1OperatorModulus_nonneg S),
      abs_of_nonneg (show 0 ≤ complexL1OperatorModulus K from complexL1OperatorModulus_nonneg K)] using h
  · intro hS
    have h := hS (complexIntegralBandProjection S) (complexIntegralBandProjection_isIntegral S)
    rw [complexIntegralBandProjection_modulus] at h
    have hle : integralBandProjection (complexL1OperatorModulus S) ≤ complexL1OperatorModulus S :=
      integralBandProjection_le_id _ (complexL1OperatorModulus_nonneg S)
    rw [inf_eq_right.mpr hle] at h
    exact (complexL1BandProjection_eq_zero_iff_modulus integralOperatorOrderClosedIdeal S).mpr h

theorem complexIntegralBandProjection_residual_singular (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsComplexSingularOperator (T-complexIntegralBandProjection T) := by
  apply (complexIntegralBandProjection_eq_zero_iff _).mp
  rw [map_sub,complexIntegralBandProjection_idempotent,sub_self]

theorem isComplexSingularOperator_iff_signed_modulus (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsComplexSingularOperator S ↔ ∀ K, IsIntegralOperator K →
      complexL1OperatorModulus (S-K) = complexL1OperatorModulus (S+K) := by
  rw [← complexIntegralBandProjection_eq_zero_iff]
  change complexL1BandProjection integralOperatorOrderClosedIdeal S = 0 ↔ _
  rw [complexL1BandProjection_eq_zero_iff_signed_modulus]
  change (∀ K, complexIntegralBandProjection K = K →
    complexL1OperatorModulus (S-K) = complexL1OperatorModulus (S+K)) ↔ _
  simp only [complexIntegralBandProjection_eq_self_iff]

def complexSingularOperatorSubmodule (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] : Submodule ℂ (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :=
  LinearMap.ker (complexIntegralBandProjection (μ := μ) (ν := ν)).toLinearMap

theorem mem_complexSingularOperatorSubmodule (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    T ∈ complexSingularOperatorSubmodule μ ν ↔ IsComplexSingularOperator T :=
  complexIntegralBandProjection_eq_zero_iff T

theorem complexIntegralBandProjection_isProj :
    LinearMap.IsProj (complexIntegralOperatorSubmodule μ ν)
      (complexIntegralBandProjection (μ := μ) (ν := ν)).toLinearMap :=
  ⟨complexIntegralBandProjection_isIntegral,fun _ hT => complexIntegralBandProjection_eq_self hT⟩

theorem complex_integral_singular_isCompl :
    IsCompl (complexIntegralOperatorSubmodule μ ν) (complexSingularOperatorSubmodule μ ν) :=
  complexIntegralBandProjection_isProj.isCompl

theorem exists_unique_complex_integral_singular_decomposition (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ∃! p : (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) × (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν),
      IsIntegralOperator p.1 ∧ IsComplexSingularOperator p.2 ∧ T = p.1+p.2 := by
  refine ⟨(complexIntegralBandProjection T,T-complexIntegralBandProjection T),
    ⟨complexIntegralBandProjection_isIntegral T,complexIntegralBandProjection_residual_singular T,by simp⟩,?_⟩
  intro p hp
  have hpzero := (complexIntegralBandProjection_eq_zero_iff p.2).mpr hp.2.1
  have hpfirst : complexIntegralBandProjection T = p.1 := by
    rw [hp.2.2,map_add,complexIntegralBandProjection_eq_self hp.1,hpzero,add_zero]
  apply Prod.ext
  · exact hpfirst.symm
  · dsimp
    rw [hpfirst,hp.2.2]
    abel

theorem complex_singular_integral_modulus_add {S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hS : IsComplexSingularOperator S) (hK : IsIntegralOperator K) :
    complexL1OperatorModulus (S+K) = complexL1OperatorModulus S + complexL1OperatorModulus K :=
  complexL1BandProjection_modulus_add integralOperatorOrderClosedIdeal
    ((complexIntegralBandProjection_eq_zero_iff S).mpr hS) (complexIntegralBandProjection_eq_self hK)

theorem complex_singular_integral_modulus_sub {S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hS : IsComplexSingularOperator S) (hK : IsIntegralOperator K) :
    complexL1OperatorModulus (S-K) = complexL1OperatorModulus S + complexL1OperatorModulus K :=
  complexL1BandProjection_modulus_sub integralOperatorOrderClosedIdeal
    ((complexIntegralBandProjection_eq_zero_iff S).mpr hS) (complexIntegralBandProjection_eq_self hK)

theorem complex_integral_singular_modulus_decomposition (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus T = complexL1OperatorModulus (T-complexIntegralBandProjection T) +
      complexL1OperatorModulus (complexIntegralBandProjection T) :=
  complexL1BandProjection_modulus_decomposition integralOperatorOrderClosedIdeal T

end ThesisCommon
