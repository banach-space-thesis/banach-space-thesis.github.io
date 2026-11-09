import NonCalkinAlgebra.MatrixIdealStructure

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

/-- The paper's concrete unital Banach algebra, with its inherited operator norm. -/
def matrixBanachAlgebra [CompleteSpace D] [Nontrivial D] :
    SurveyStatements.P2.ComplexBanachAlgebra where
  Carrier := matrixAlgebra D

def canonicalMatrixUnit (i j : ℕ) : matrixAlgebra D := matrixTheta D i j 1

@[simp] theorem coe_canonicalMatrixUnit (i j : ℕ) :
    (canonicalMatrixUnit D i j : CoefficientSpace D →L[ℂ] CoefficientSpace D) =
      scalarMatrixUnit D i j := rfl

theorem canonicalMatrixUnit_mul (i j k l : ℕ) :
    canonicalMatrixUnit D i j * canonicalMatrixUnit D k l =
      if j = k then canonicalMatrixUnit D i l else 0 := by
  classical
  apply Subtype.ext
  split_ifs with h
  · exact (scalarMatrixUnit_mul D i j k l).trans (if_pos h)
  · exact (scalarMatrixUnit_mul D i j k l).trans (if_neg h)

theorem canonicalMatrixUnit_ne_zero [Nontrivial D] (i j : ℕ) :
    canonicalMatrixUnit D i j ≠ 0 := by
  intro h
  exact scalarMatrixUnit_ne_zero D i j (congrArg Subtype.val h)

variable [NormOneClass D]

@[simp] theorem norm_canonicalMatrixUnit (i j : ℕ) : ‖canonicalMatrixUnit D i j‖ = 1 :=
  norm_scalarMatrixUnit D i j

/-- Lemma 5.2, in A_D itself, including the empty finite row. -/
theorem canonicalMatrixUnit_row_le (F : Finset ℕ) (a : F → ℂ) :
    ‖∑ j : F, a j • canonicalMatrixUnit D 0 j‖ ≤ ‖a‖ := by
  have heq : ((∑ j : F, a j • canonicalMatrixUnit D 0 j : matrixAlgebra D) :
      CoefficientSpace D →L[ℂ] CoefficientSpace D) =
      ∑ j : F, a j • scalarMatrixUnit D 0 j := by
    change (matrixAlgebra D).val (∑ j : F, a j • canonicalMatrixUnit D 0 j) = _
    simp only [map_sum, map_smul, Subalgebra.val_apply, coe_canonicalMatrixUnit]
  change ‖((∑ j : F, a j • canonicalMatrixUnit D 0 j : matrixAlgebra D) :
      CoefficientSpace D →L[ℂ] CoefficientSpace D)‖ ≤ ‖a‖
  rw [heq]
  exact norm_scalarMatrixUnit_row_le D 0 F a

end NonCalkinAlgebra
