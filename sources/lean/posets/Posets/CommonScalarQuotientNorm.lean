import Posets.CommonScalarQuotientMap

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem blockScalarMatrix_id_diagonal {Q : Type*} [PartialOrder Q]
    {V : Q → Type*} [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace 𝕜 (V p)]
    {ι : ∀ s t, V s →L[𝕜] V t} (h : FewOperators 𝕜 V ι) (s : Q) :
    blockScalarMatrix h (ContinuousLinearMap.id 𝕜 (DependentCZeroSum 𝕜 V)) s s = 1 := by
  have hblock : operatorBlock 𝕜 V V (ContinuousLinearMap.id 𝕜 (DependentCZeroSum 𝕜 V)) s s = ι s s := by
    rw [fewOperators_self h s]
    ext x
    simp [operatorBlock, sumProjection, sumInjection]
  simp only [blockScalarMatrix, dif_pos (le_refl s), hblock]
  exact scalarBetween_embedding (h.1 s) (h.2.1 s s le_rfl)
    (fewOperators_scalarDecompositions h le_rfl)

variable {P : Type} [PartialOrder P] [Nonempty P]
  {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) (hcommon : CommonSubspace 𝕜 X ι)
  (hcols : ∀ T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X, ZeroColumnsOn 𝕜 (blockScalarMatrix h T))

/-- Exact norm one, already at the linear stage of the quotient construction. -/
theorem norm_commonScalarQuotientMap : ‖commonScalarQuotientMap h hcommon hcols‖ = 1 := by
  classical
  apply le_antisymm (norm_commonScalarQuotientMap_le h hcommon hcols)
  let p : P := Classical.arbitrary P
  let I := ContinuousLinearMap.id 𝕜 (DependentCZeroSum 𝕜 X)
  have heval : (commonScalarQuotientMap h hcommon hcols I).val (unitVector 𝕜 p) ⟨p⟩ = 1 := by
    change scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols I).val p p = 1
    rw [scalarMatrix_commonScalarQuotientValue]
    exact blockScalarMatrix_id_diagonal h p
  have hu : ‖unitVector 𝕜 p‖ ≤ 1 := by
    simpa using norm_finite_unit_sum_le ({p} : Finset P) (fun _ => (1 : 𝕜))
      zero_le_one (fun _ _ => by simp)
  have hi : ‖I‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [I]
  calc
    1 = ‖(commonScalarQuotientMap h hcommon hcols I).val (unitVector 𝕜 p) ⟨p⟩‖ := by rw [heval, norm_one]
    _ ≤ ‖(commonScalarQuotientMap h hcommon hcols I).val (unitVector 𝕜 p)‖ :=
      ((commonScalarQuotientMap h hcommon hcols I).val (unitVector 𝕜 p)).toBCF.norm_coe_le_norm _
    _ ≤ ‖(commonScalarQuotientMap h hcommon hcols I).val‖ * ‖unitVector 𝕜 p‖ :=
      (commonScalarQuotientMap h hcommon hcols I).val.le_opNorm _
    _ ≤ ‖commonScalarQuotientMap h hcommon hcols I‖ := by
      simpa using mul_le_mul_of_nonneg_left hu (norm_nonneg (commonScalarQuotientMap h hcommon hcols I).val)
    _ ≤ ‖commonScalarQuotientMap h hcommon hcols‖ * ‖I‖ := (commonScalarQuotientMap h hcommon hcols).le_opNorm I
    _ ≤ ‖commonScalarQuotientMap h hcommon hcols‖ := by
      simpa using mul_le_mul_of_nonneg_left hi (norm_nonneg (commonScalarQuotientMap h hcommon hcols))

end Posets
