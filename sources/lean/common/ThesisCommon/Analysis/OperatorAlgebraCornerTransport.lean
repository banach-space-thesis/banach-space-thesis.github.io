import ThesisCommon.Analysis.OperatorAlgebraLpSelfCopies

/-! Orthogonal corner geometry is stable under bounded isomorphisms and
finite products. Finite-dimensional factors have the zero corner. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_orthogonal_cornerCopies_of_equiv (e : E ≃L[𝕜] F)
    (Q : F →L[𝕜] F) (J P : ℕ → F →L[𝕜] F)
    (hd : ∀ n, (P n).comp (J n) = Q)
    (ho : ∀ n m, n ≠ m → (P n).comp (J m) = 0)
    (hr : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 F - Q)) :
    ∃ Q' : E →L[𝕜] E, ∃ J' P' : ℕ → E →L[𝕜] E,
      (∀ n, (P' n).comp (J' n) = Q') ∧
      (∀ n m, n ≠ m → (P' n).comp (J' m) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - Q') := by
  let C (T : F →L[𝕜] F) := e.symm.toContinuousLinearMap.comp (T.comp e.toContinuousLinearMap)
  refine ⟨C Q, fun n => C (J n), fun n => C (P n), ?_, ?_, ?_⟩
  · intro n
    apply ContinuousLinearMap.ext
    intro x
    change e.symm (P n (e (e.symm (J n (e x))))) = e.symm (Q (e x))
    rw [e.apply_symm_apply]
    exact congrArg e.symm (DFunLike.congr_fun (hd n) (e x))
  · intro n m hnm
    apply ContinuousLinearMap.ext
    intro x
    change e.symm (P n (e (e.symm (J m (e x))))) = 0
    rw [e.apply_symm_apply]
    have h := DFunLike.congr_fun (ho n m hnm) (e x)
    change P n (J m (e x)) = 0 at h
    rw [h, map_zero]
  · have h := (hr.comp_right e.toContinuousLinearMap).comp_left e.symm.toContinuousLinearMap
    convert h using 1
    ext x
    change x - e.symm (Q (e x)) = e.symm (e x - Q (e x))
    rw [map_sub, e.symm_apply_apply]

theorem exists_orthogonal_cornerCopies_prod
    (QE : E →L[𝕜] E) (JE PE : ℕ → E →L[𝕜] E)
    (hdE : ∀ n, (PE n).comp (JE n) = QE)
    (hoE : ∀ n m, n ≠ m → (PE n).comp (JE m) = 0)
    (hrE : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - QE))
    (QF : F →L[𝕜] F) (JF PF : ℕ → F →L[𝕜] F)
    (hdF : ∀ n, (PF n).comp (JF n) = QF)
    (hoF : ∀ n m, n ≠ m → (PF n).comp (JF m) = 0)
    (hrF : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 F - QF)) :
    ∃ Q : E × F →L[𝕜] E × F, ∃ J P : ℕ → E × F →L[𝕜] E × F,
      (∀ n, (P n).comp (J n) = Q) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (E × F) - Q) := by
  refine ⟨QE.prodMap QF, fun n => (JE n).prodMap (JF n),
    fun n => (PE n).prodMap (PF n), ?_, ?_, ?_⟩
  · intro n
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · exact DFunLike.congr_fun (hdE n) x.1
    · exact DFunLike.congr_fun (hdF n) x.2
  · intro n m hnm
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · exact DFunLike.congr_fun (hoE n m hnm) x.1
    · exact DFunLike.congr_fun (hoF n m hnm) x.2
  · have h := ((hrE.comp_right (ContinuousLinearMap.fst 𝕜 E F)).comp_left
      (ContinuousLinearMap.inl 𝕜 E F)).add
      ((hrF.comp_right (ContinuousLinearMap.snd 𝕜 E F)).comp_left
        (ContinuousLinearMap.inr 𝕜 E F))
    convert h using 1
    ext x <;> simp

theorem exists_orthogonal_cornerCopies_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    ∃ Q : E →L[𝕜] E, ∃ J P : ℕ → E →L[𝕜] E,
      (∀ n, (P n).comp (J n) = Q) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - Q) := by
  refine ⟨0, fun _ => 0, fun _ => 0, by simp, by simp, ?_⟩
  simpa only [sub_zero] using (weaklyCompact_id_of_finiteDimensional (𝕜 := 𝕜) (E := E))

end ThesisCommon
