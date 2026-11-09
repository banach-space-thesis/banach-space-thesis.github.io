import NonCalkinAlgebra.MatrixEntries
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

/-- Coordinate entries separate the operators in the paper's matrix closure.
The restriction to J_D matters when D is not one-dimensional. -/
theorem matrixClosure_eq_zero_of_entries_eq_zero
    {T : CoefficientSpace D →L[ℂ] CoefficientSpace D} (hT : T ∈ matrixClosure D)
    (hentry : ∀ i j : ℕ, matrixEntry D i j T = 0) : T = 0 := by
  have hsingle : ∀ j : ℕ, ∀ d : D, T (lp.single 1 j d) = 0 := by
    intro j d
    ext i
    have hcorner := matrixClosure_corner_formula D hT i j
    rw [hentry i j, theta_zero] at hcorner
    have h := congrArg (fun S : CoefficientSpace D →L[ℂ] CoefficientSpace D =>
      S (lp.single 1 j d) i) hcorner
    simpa [ContinuousLinearMap.mul_apply, scalarMatrixUnit, theta_apply,
      lp.single_apply] using h
  apply ContinuousLinearMap.ext
  intro x
  have hs := (lp.hasSum_single (show (1 : ENNReal) ≠ ⊤ by simp) x).mapL T
  have hfun : (fun j : ℕ => T (lp.single 1 j (x j))) = fun _ => 0 := by
    funext j
    exact hsingle j (x j)
  rw [hfun] at hs
  exact hs.unique hasSum_zero

theorem matrixClosure_has_nonzero_entry
    {T : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (hT : T ∈ matrixClosure D) (hne : T ≠ 0) :
    ∃ i j : ℕ, matrixEntry D i j T ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  exact hne (matrixClosure_eq_zero_of_entries_eq_zero D hT h)

end NonCalkinAlgebra
