import NonCalkinAlgebra.MatrixIdeal
import NonCalkinAlgebra.MatrixEntries

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

theorem matrixEntry_one (i j : ℕ) :
    matrixEntry D i j 1 = if i = j then 1 else 0 := by
  classical
  simp [matrixEntry_apply, lp.single_apply, Pi.single_apply, eq_comm]

theorem diagonal_matrixAlgebra_corner_formula
    {T : CoefficientSpace D →L[ℂ] CoefficientSpace D} (hT : T ∈ matrixAlgebra D)
    (i : ℕ) :
    scalarMatrixUnit D i i * T * scalarMatrixUnit D i i =
      theta D i i (matrixEntry D i i T) := by
  obtain ⟨c, J, hJ, rfl⟩ := (mem_unitizedMatrixSubspace D T).mp hT
  rw [map_add, map_smul, matrixEntry_one, if_pos rfl, theta_add, theta_smul]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [matrixClosure_corner_formula D hJ i i]
  have hmul : scalarMatrixUnit D i i * scalarMatrixUnit D i i = scalarMatrixUnit D i i := by
    simp only [scalarMatrixUnit, theta_mul, if_true, one_mul]
  rw [hmul]
  rfl

/-- The diagonal corner is literally θ_ii(D), with the inherited operator norm. -/
theorem diagonal_corner_eq_theta_range (i : ℕ) :
    {S : CoefficientSpace D →L[ℂ] CoefficientSpace D |
      ∃ T ∈ matrixAlgebra D, S = scalarMatrixUnit D i i * T * scalarMatrixUnit D i i} =
      Set.range (theta D i i) := by
  apply Set.ext
  intro S
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨matrixEntry D i i T, (diagonal_matrixAlgebra_corner_formula D hT i).symm⟩
  · rintro ⟨d, rfl⟩
    refine ⟨theta D i i d, theta_mem_matrixAlgebra D i i d, ?_⟩
    simp only [scalarMatrixUnit, theta_mul, if_true, one_mul, mul_one]

theorem theta_injective (i j : ℕ) : Function.Injective (theta D i j) := by
  intro d e h
  have hv := congrArg (matrixEntry D i j) h
  simpa only [matrixEntry_theta, and_self, if_pos rfl] using hv

/-- The normed linear part of the corner isomorphism from Proposition 5.1.
Multiplicativity is the already proved `theta_mul` with all indices equal. -/
def diagonalCornerIsometry (i : ℕ) :
    D ≃ₗᵢ[ℂ] LinearMap.range (thetaCoefficientMap D i i).toLinearMap where
  toLinearEquiv := LinearEquiv.ofInjective (thetaCoefficientMap D i i).toLinearMap
    (theta_injective D i i)
  norm_map' d := norm_theta D i i d

end NonCalkinAlgebra
