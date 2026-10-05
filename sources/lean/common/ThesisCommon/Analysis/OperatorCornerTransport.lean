import ThesisCommon.Analysis.OperatorIsometryTransport
import ThesisCommon.Analysis.RealBanachLatticeCoordinates

/-! Exact corner-copy geometry, including its genuine weakly compact
remainder, survives an onto isometry and the intrinsic real-form model. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_orthogonal_cornerCopies_of_isometryEquiv (e : E ≃ₗᵢ[𝕜] F)
    (Q : E →L[𝕜] E) (J P : ℕ → E →L[𝕜] E)
    (hd : ∀ n, (P n).comp (J n) = Q)
    (ho : ∀ n k, n ≠ k → (P n).comp (J k) = 0)
    (hr : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - Q)) :
    ∃ R : F →L[𝕜] F, ∃ U V : ℕ → F →L[𝕜] F,
      (∀ n, (V n).comp (U n) = R) ∧
      (∀ n k, n ≠ k → (V n).comp (U k) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 F - R) := by
  refine ⟨operatorTransport e e Q, fun n => operatorTransport e e (J n),
    fun n => operatorTransport e e (P n), ?_, ?_, ?_⟩
  · intro n
    ext x
    simp only [ContinuousLinearMap.comp_apply, operatorTransport_apply,
      LinearIsometryEquiv.symm_apply_apply]
    exact congrArg e (DFunLike.congr_fun (hd n) (e.symm x))
  · intro n k hnk
    ext x
    simp only [ContinuousLinearMap.comp_apply, operatorTransport_apply,
      LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.zero_apply]
    have h := DFunLike.congr_fun (ho n k hnk) (e.symm x)
    change P n (J k (e.symm x)) = 0 at h
    rw [h, map_zero]
  · have h := (weaklyCompact_operatorTransport_iff e e
      (ContinuousLinearMap.id 𝕜 E - Q)).mpr hr
    have heq : operatorTransport e e (ContinuousLinearMap.id 𝕜 E - Q) =
        ContinuousLinearMap.id 𝕜 F - operatorTransport e e Q := by
      ext x
      simp [operatorTransport_apply]
    rwa [heq] at h

theorem BanachLatticeModel.exists_real_cornerCopies_of_realForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : BanachLatticeModel ℝ E)
    (Q : B.realForm →L[ℝ] B.realForm) (J P : ℕ → B.realForm →L[ℝ] B.realForm)
    (hd : ∀ n, (P n).comp (J n) = Q)
    (ho : ∀ n k, n ≠ k → (P n).comp (J k) = 0)
    (hr : IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ B.realForm - Q)) :
    ∃ R : E →L[ℝ] E, ∃ U V : ℕ → E →L[ℝ] E,
      (∀ n, (V n).comp (U n) = R) ∧
      (∀ n k, n ≠ k → (V n).comp (U k) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ E - R) :=
  exists_orthogonal_cornerCopies_of_isometryEquiv B.realFormLinearIsometryEquiv Q J P hd ho hr

end ThesisCommon
