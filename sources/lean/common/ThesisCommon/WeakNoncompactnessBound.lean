import ThesisCommon.WeakCompact

/-! The elementary comparison in Acuaviva--Nasseri, Lemma 5.10.
The proof only needs the displayed properties, and works on any normed space.
The paper-specific definition of a normalized measure is kept in PEMS. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Subadditivity and vanishing on weakly compact operators imply invariance
under weakly compact perturbations. This expands an implicit step in Lemma 5.10. -/
theorem weakNoncompactness_sub_eq (α : (E →L[𝕜] E) → ℝ)
    (hadd : ∀ S T, α (S + T) ≤ α S + α T)
    (hzero : ∀ W, IsWeaklyCompactOperator W → α W = 0)
    (T W : E →L[𝕜] E) (hW : IsWeaklyCompactOperator W) :
    α (T - W) = α T := by
  have hnW : IsWeaklyCompactOperator (-W) := by
    simpa using hW.smul (-1 : 𝕜)
  apply le_antisymm
  · simpa [sub_eq_add_neg, hzero (-W) hnW] using hadd T (-W)
  · simpa [hzero W hW] using hadd (T - W) W

/-- A normalized, subadditive operator functional with the left ideal estimate
and vanishing on weakly compact operators is bounded by the weak essential norm.
No AL-space structure or representation theorem is needed for this argument. -/
theorem weakNoncompactness_le_weakEssentialNorm (α : (E →L[𝕜] E) → ℝ)
    (hadd : ∀ S T, α (S + T) ≤ α S + α T)
    (hcomp : ∀ S T : E →L[𝕜] E, α (S.comp T) ≤ ‖S‖ * α T)
    (hzero : ∀ W, IsWeaklyCompactOperator W → α W = 0)
    (hid : α (ContinuousLinearMap.id 𝕜 E) = 1) (T : E →L[𝕜] E) :
    α T ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    calc
      α T = α (T - W) := (weakNoncompactness_sub_eq α hadd hzero T W hW).symm
      _ ≤ ‖T - W‖ * α (ContinuousLinearMap.id 𝕜 E) := by
        simpa using hcomp (T - W) (ContinuousLinearMap.id 𝕜 E)
      _ = ‖T - W‖ := by rw [hid, mul_one]

end ThesisCommon
