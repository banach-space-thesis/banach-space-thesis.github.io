import NonCalkinAlgebra.MatrixRowEstimate
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

def matrixGenerators : Set (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
  {T | ∃ i j : ℕ, ∃ d : D, T = theta D i j d}

/-- Finite-support D-valued matrices as an actual complex vector subspace. -/
def finiteMatrixSpan : Submodule ℂ (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
  Submodule.span ℂ (matrixGenerators D)

theorem theta_mem_finiteMatrixSpan (i j : ℕ) (d : D) :
    theta D i j d ∈ finiteMatrixSpan D :=
  Submodule.subset_span ⟨i, j, d, rfl⟩

theorem finiteMatrixSpan_mul {a b : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (ha : a ∈ finiteMatrixSpan D) (hb : b ∈ finiteMatrixSpan D) :
    a * b ∈ finiteMatrixSpan D := by
  change a ∈ Submodule.span ℂ (matrixGenerators D) at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, j, d, rfl⟩ := ha
    change b ∈ Submodule.span ℂ (matrixGenerators D) at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, l, e, rfl⟩ := hb
      rw [theta_mul]
      split_ifs
      · exact theta_mem_finiteMatrixSpan D i l (d * e)
      · exact (finiteMatrixSpan D).zero_mem
    | zero => simpa only [mul_zero] using (finiteMatrixSpan D).zero_mem
    | add b c hb hc ihb ihc =>
      simpa only [mul_add] using (finiteMatrixSpan D).add_mem ihb ihc
    | smul c b hb ih =>
      simpa only [mul_smul_comm] using (finiteMatrixSpan D).smul_mem c ih
  | zero => simpa only [zero_mul] using (finiteMatrixSpan D).zero_mem
  | add a c ha hc iha ihc =>
    simpa only [add_mul] using (finiteMatrixSpan D).add_mem iha ihc
  | smul c a ha ih =>
    simpa only [smul_mul_assoc] using (finiteMatrixSpan D).smul_mem c ih

/-- The paper's J_D, using the operator-norm closure of finite matrices. -/
def matrixClosure : Submodule ℂ (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
  (finiteMatrixSpan D).topologicalClosure

instance matrixClosure_isClosed :
    IsClosed (matrixClosure D : Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) :=
  Submodule.isClosed_topologicalClosure _

theorem theta_mem_matrixClosure (i j : ℕ) (d : D) : theta D i j d ∈ matrixClosure D :=
  (finiteMatrixSpan D).le_topologicalClosure (theta_mem_finiteMatrixSpan D i j d)

theorem matrixClosure_mul {a b : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (ha : a ∈ matrixClosure D) (hb : b ∈ matrixClosure D) :
    a * b ∈ matrixClosure D := by
  have hleft : ∀ c ∈ finiteMatrixSpan D, c * b ∈ matrixClosure D := by
    intro c hc
    have hmap : Set.MapsTo (fun t : CoefficientSpace D →L[ℂ] CoefficientSpace D => c * t)
        (finiteMatrixSpan D) (finiteMatrixSpan D) :=
      fun t ht => finiteMatrixSpan_mul D hc ht
    have hcont : Continuous (fun t : CoefficientSpace D →L[ℂ] CoefficientSpace D => c * t) :=
      (ContinuousLinearMap.compL ℂ (CoefficientSpace D) (CoefficientSpace D)
        (CoefficientSpace D) c).continuous
    exact hmap.closure hcont hb
  have hmap : Set.MapsTo (fun t : CoefficientSpace D →L[ℂ] CoefficientSpace D => t * b)
      (finiteMatrixSpan D) (matrixClosure D) := hleft
  have hcont : Continuous (fun t : CoefficientSpace D →L[ℂ] CoefficientSpace D => t * b) :=
    ((ContinuousLinearMap.compL ℂ (CoefficientSpace D) (CoefficientSpace D)
      (CoefficientSpace D)).flip b).continuous
  have h := hmap.closure hcont ha
  simpa only [(matrixClosure_isClosed D).closure_eq] using h

end NonCalkinAlgebra
