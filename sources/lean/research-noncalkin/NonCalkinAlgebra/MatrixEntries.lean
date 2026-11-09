import NonCalkinAlgebra.MatrixClosure

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

@[simp] theorem theta_zero (i j : ℕ) : theta D i j 0 = 0 := by
  ext x n
  simp [theta_apply, lp.single_apply]

def thetaCoefficientMap (i j : ℕ) :
    D →L[ℂ] (CoefficientSpace D →L[ℂ] CoefficientSpace D) := by
  let f : D →ₗ[ℂ] (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
    { toFun := theta D i j
      map_add' := theta_add D i j
      map_smul' := theta_smul D i j }
  exact LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := D)
    (F := CoefficientSpace D →L[ℂ] CoefficientSpace D) (σ := RingHom.id ℂ) f 1 (fun d => by
    change ‖theta D i j d‖ ≤ 1 * ‖d‖
    simpa only [one_mul] using norm_theta_le D i j d)

@[simp] theorem thetaCoefficientMap_apply (i j : ℕ) (d : D) :
    thetaCoefficientMap D i j d = theta D i j d := rfl

/-- Recover the (i,j) coefficient by applying the operator to the jth unit
vector and evaluating the ith coordinate. This is continuous in operator norm. -/
def matrixEntry (i j : ℕ) :
    (CoefficientSpace D →L[ℂ] CoefficientSpace D) →L[ℂ] D :=
  (coordinate D i).comp
    (ContinuousLinearMap.apply ℂ (CoefficientSpace D) (lp.single 1 j (1 : D)))

@[simp] theorem matrixEntry_apply (i j : ℕ)
    (T : CoefficientSpace D →L[ℂ] CoefficientSpace D) :
    matrixEntry D i j T = T (lp.single 1 j (1 : D)) i := rfl

theorem matrixEntry_theta (i j k l : ℕ) (d : D) :
    matrixEntry D i j (theta D k l d) = if i = k ∧ j = l then d else 0 := by
  classical
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [matrixEntry_apply, theta_apply, lp.single_apply, hik, hjl, eq_comm]

/-- Equation (12), expressed as an explicit continuous coefficient formula.
This is a statement about J_D, not arbitrary operators on ℓ¹(ℕ,D).
-/
theorem matrixClosure_corner_formula
    {T : CoefficientSpace D →L[ℂ] CoefficientSpace D} (hT : T ∈ matrixClosure D)
    (i j : ℕ) :
    scalarMatrixUnit D i i * T * scalarMatrixUnit D j j =
      theta D i j (matrixEntry D i j T) := by
  classical
  let F := ContinuousLinearMap.mulLeftRight ℂ
    (CoefficientSpace D →L[ℂ] CoefficientSpace D)
    (scalarMatrixUnit D i i) (scalarMatrixUnit D j j)
  let G := (thetaCoefficientMap D i j).comp (matrixEntry D i j)
  let H := F - G
  have hgen : matrixGenerators D ⊆ LinearMap.ker H.toLinearMap := by
    rintro A ⟨k, l, d, rfl⟩
    change F (theta D k l d) - G (theta D k l d) = 0
    apply sub_eq_zero.mpr
    by_cases hik : i = k <;> by_cases hlj : l = j <;>
      simp [F, G, ContinuousLinearMap.mulLeftRight_apply, scalarMatrixUnit,
        theta_mul, matrixEntry_theta, hik, hlj, eq_comm]
  have hspan : finiteMatrixSpan D ≤ LinearMap.ker H.toLinearMap :=
    Submodule.span_le.mpr hgen
  have hclosure : matrixClosure D ≤ LinearMap.ker H.toLinearMap :=
    Submodule.topologicalClosure_minimal (finiteMatrixSpan D) hspan
      (ContinuousLinearMap.isClosed_ker H)
  have h := hclosure hT
  change F T - G T = 0 at h
  have heq := sub_eq_zero.mp h
  simpa only [F, G, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.comp_apply, thetaCoefficientMap_apply] using heq

end NonCalkinAlgebra
