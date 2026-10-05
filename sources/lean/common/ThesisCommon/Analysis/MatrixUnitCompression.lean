import ThesisCommon.Analysis.MatrixBlockAveraging

/-! Matrix units are preserved by the actual rectangular insertion maps. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp] theorem matrixInsert_unit (p : BanachExponent) {n N : ℕ}
    (α τ : Fin n ↪ Fin N) (i j : Fin n) :
    matrixInsert p α τ (matrixUnit (𝕜 := 𝕜) p i j) = matrixUnit p (α i) (τ j) := by
  apply ContinuousLinearMap.ext
  intro x
  change lpExtend (𝕜 := 𝕜) p.val α
    ((lpRestrict (𝕜 := 𝕜) p.val τ x) j • (lp.single p.val i (1 : 𝕜) : FiniteLpSpace 𝕜 p n)) =
    x (τ j) • (lp.single p.val (α i) (1 : 𝕜) : FiniteLpSpace 𝕜 p N)
  rw [map_smul, lpExtend_single_between]
  rfl

theorem matrixEntry_unit_eq (p : BanachExponent) {N : ℕ} (i j k l : Fin N) :
    matrixEntry p k l (matrixUnit (𝕜 := 𝕜) p i j) =
      if k = i ∧ l = j then 1 else 0 := by
  classical
  by_cases hk : k = i <;> by_cases hl : l = j <;>
    simp [matrixEntry_apply, matrixUnit_apply, lp.single_apply, hk, hl]

end ThesisCommon

