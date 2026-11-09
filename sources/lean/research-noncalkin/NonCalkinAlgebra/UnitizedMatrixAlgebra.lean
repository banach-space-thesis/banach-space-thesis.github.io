import NonCalkinAlgebra.NonunitalMatrixClosure
import NonCalkinAlgebra.ClosedScalarExtension
import SurveyStatements.P2InvariantQuotient
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

def scalarQuotientSpan :
    Submodule ℂ ((CoefficientSpace D →L[ℂ] CoefficientSpace D) ⧸ matrixClosure D) :=
  Submodule.span ℂ {(matrixClosure D).mkQ 1}

/-- The preimage of the scalar line modulo J_D; the next theorem identifies
this subspace with the paper's literal sum ℂ I + J_D. -/
def unitizedMatrixSubspace : Submodule ℂ (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
  (scalarQuotientSpan D).comap (matrixClosure D).mkQ

theorem mem_unitizedMatrixSubspace (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) :
    a ∈ unitizedMatrixSubspace D ↔
      ∃ c : ℂ, ∃ j ∈ matrixClosure D, a = c • 1 + j := by
  constructor
  · intro ha
    change (matrixClosure D).mkQ a ∈ Submodule.span ℂ {(matrixClosure D).mkQ 1} at ha
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨c, a - c • 1, ?_, ?_⟩
    · apply (Submodule.Quotient.mk_eq_zero _).mp
      change (matrixClosure D).mkQ (a - c • 1) = 0
      rw [map_sub, map_smul, hc, sub_self]
    · abel
  · rintro ⟨c, j, hj, rfl⟩
    change (matrixClosure D).mkQ (c • 1 + j) ∈
      Submodule.span ℂ {(matrixClosure D).mkQ 1}
    have hzero : (matrixClosure D).mkQ j = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hj
    rw [map_add, map_smul, hzero, add_zero]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))

theorem one_mem_unitizedMatrixSubspace :
    (1 : CoefficientSpace D →L[ℂ] CoefficientSpace D) ∈ unitizedMatrixSubspace D :=
  (mem_unitizedMatrixSubspace D 1).mpr ⟨1, 0, (matrixClosure D).zero_mem, by simp⟩

theorem unitizedMatrixSubspace_mul {a b : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (ha : a ∈ unitizedMatrixSubspace D) (hb : b ∈ unitizedMatrixSubspace D) :
    a * b ∈ unitizedMatrixSubspace D := by
  obtain ⟨c, j, hj, rfl⟩ := (mem_unitizedMatrixSubspace D a).mp ha
  obtain ⟨d, k, hk, rfl⟩ := (mem_unitizedMatrixSubspace D b).mp hb
  apply (mem_unitizedMatrixSubspace D _).mpr
  refine ⟨c * d, c • k + d • j + j * k, ?_, ?_⟩
  · exact (matrixClosure D).add_mem
      ((matrixClosure D).add_mem ((matrixClosure D).smul_mem c hk)
        ((matrixClosure D).smul_mem d hj)) (matrixClosure_mul D hj hk)
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_add, smul_smul]
    simp only [mul_comm d c]
    abel

/-- The concrete algebra A_D = ℂ I + J_D, as a subalgebra of bounded operators. -/
def matrixAlgebra : Subalgebra ℂ (CoefficientSpace D →L[ℂ] CoefficientSpace D) where
  carrier := unitizedMatrixSubspace D
  zero_mem' := (unitizedMatrixSubspace D).zero_mem
  add_mem' := (unitizedMatrixSubspace D).add_mem
  one_mem' := one_mem_unitizedMatrixSubspace D
  mul_mem' := unitizedMatrixSubspace_mul D
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (unitizedMatrixSubspace D).smul_mem c (one_mem_unitizedMatrixSubspace D)

instance matrixAlgebra_normedAlgebra : NormedAlgebra ℂ (matrixAlgebra D) where
  norm_smul_le c a :=
    ContinuousLinearMap.opNorm_smul_le c (a : CoefficientSpace D →L[ℂ] CoefficientSpace D)

theorem matrixAlgebra_isClosed :
    IsClosed (matrixAlgebra D : Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) := by
  change IsClosed (unitizedMatrixSubspace D : Set (CoefficientSpace D →L[ℂ] CoefficientSpace D))
  unfold unitizedMatrixSubspace scalarQuotientSpan
  exact @closed_scalar_extension (CoefficientSpace D →L[ℂ] CoefficientSpace D)
    inferInstance inferInstance (matrixClosure D) (matrixClosure_isClosed D) 1

theorem matrixClosure_mem_matrixAlgebra {j : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (hj : j ∈ matrixClosure D) : j ∈ matrixAlgebra D :=
  (mem_unitizedMatrixSubspace D j).mpr ⟨0, j, hj, by simp⟩

theorem theta_mem_matrixAlgebra (i j : ℕ) (d : D) : theta D i j d ∈ matrixAlgebra D :=
  matrixClosure_mem_matrixAlgebra D (theta_mem_matrixClosure D i j d)

instance matrixAlgebra_completeSpace [CompleteSpace D] : CompleteSpace (matrixAlgebra D) :=
  (matrixAlgebra_isClosed D).completeSpace_coe

instance matrixAlgebra_nontrivial [Nontrivial D] : Nontrivial (matrixAlgebra D) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hvalue := congrArg (fun T : matrixAlgebra D =>
    (T : CoefficientSpace D →L[ℂ] CoefficientSpace D) (lp.single 1 0 (1 : D)) 0) h
  have hzero : (0 : D) = 1 := by simpa [lp.single_apply] using hvalue
  exact zero_ne_one hzero

end NonCalkinAlgebra
