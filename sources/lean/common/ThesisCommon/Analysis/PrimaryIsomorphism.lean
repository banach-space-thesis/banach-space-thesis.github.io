import ThesisCommon.Analysis.Factorization

/-! Isomorphic invariance with the distortion tracked explicitly.
Used in both papers for reduction to a representative space. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Change the space whose identity is factored, at cost ‖e‖‖e⁻¹‖. -/
theorem FactorsIdentityWith.target_equiv {T : X →L[𝕜] Y} {C : ℝ}
    (h : FactorsIdentityWith T Z C) (e : Z ≃L[𝕜] W) :
    FactorsIdentityWith T W (C * (‖e.toContinuousLinearMap‖ *
      ‖e.symm.toContinuousLinearMap‖)) := by
  obtain ⟨U, V, heq, hn⟩ := h
  refine ⟨e.toContinuousLinearMap.comp U, V.comp e.symm.toContinuousLinearMap, ?_, ?_⟩
  · ext w
    have hz := congrArg (fun f : Z →L[𝕜] Z => f (e.symm w)) heq
    change U (T (V (e.symm w))) = e.symm w at hz
    change e (U (T (V (e.symm w)))) = w
    rw [hz, e.apply_symm_apply]
  · calc
      ‖e.toContinuousLinearMap.comp U‖ * ‖V.comp e.symm.toContinuousLinearMap‖ ≤
          (‖e.toContinuousLinearMap‖ * ‖U‖) *
          (‖V‖ * ‖e.symm.toContinuousLinearMap‖) := by
        exact mul_le_mul (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖U‖ * ‖V‖) *
          (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) := by ring
      _ ≤ C * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) := by gcongr

/-- UPFP is invariant under bounded linear isomorphisms. Conjugate T,
apply the original dichotomy, then conjugate its two factor maps back.
The constant max(1,C(‖e‖‖e⁻¹‖)²) also handles the zero space. -/
theorem HasUPFP.of_equiv (h : HasUPFP 𝕜 X) (e : X ≃L[𝕜] Y) : HasUPFP 𝕜 Y := by
  obtain ⟨C, hC, h⟩ := h
  let A := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let d := ‖B‖ * ‖A‖
  refine ⟨max 1 (C * d * d), le_max_left _ _, ?_⟩
  intro T
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 X := by
    ext x
    exact e.symm_apply_apply x
  have liftFactor (S : Y →L[𝕜] Y)
      (hS : FactorsIdentityWith ((A.comp S).comp B) X C) :
      FactorsIdentityWith S Y (max 1 (C * d * d)) := by
    have h' := (hS.of_compression A B).target_equiv e
    have hc : (C * (‖A‖ * ‖B‖)) *
        (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) = C * d * d := by
      dsimp [d, A, B]
      ring
    rw [hc] at h'
    exact h'.mono (le_max_right _ _)
  rcases h ((A.comp T).comp B) with hT | hT
  · exact Or.inl (liftFactor T hT)
  · apply Or.inr
    apply liftFactor (ContinuousLinearMap.id 𝕜 Y - T)
    rwa [compression_complement T A B hAB]

theorem hasUPFP_iff_of_equiv (e : X ≃L[𝕜] Y) :
    HasUPFP 𝕜 X ↔ HasUPFP 𝕜 Y :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

/-- The zero space has UPFP. This covers the Γ = ∅ boundary case omitted
from the manuscript's assertion that finite sums of L₁ are isomorphic to L₁. -/
theorem hasUPFP_of_subsingleton [Subsingleton X] : HasUPFP 𝕜 X := by
  refine ⟨1, le_rfl, fun T => Or.inl ?_⟩
  refine ⟨0, 0, ?_, by simp⟩
  ext x
  exact Subsingleton.elim _ _

end ThesisCommon
