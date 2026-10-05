import ThesisCommon.Analysis.UniformPrimariness
import ThesisCommon.Analysis.ProjectionDecomposition

/-! Turning actual isomorphisms onto projection ranges into factorizations,
with their operator norm bounds. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem projection_factorsIdentityWith_of_range_equiv
    (P : X →L[𝕜] X) (hP : P.comp P = P)
    (e : X ≃L[𝕜] LinearMap.range P.toLinearMap) :
    FactorsIdentityWith P X
      ((‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) * ‖P‖) := by
  let U := e.symm.toContinuousLinearMap.comp P.rangeRestrict
  let V := (LinearMap.range P.toLinearMap).subtypeL.comp e.toContinuousLinearMap
  have hfix (z : LinearMap.range P.toLinearMap) : P z = z := by
    obtain ⟨t, ht⟩ := z.property
    simpa only [← ht] using DFunLike.congr_fun hP t
  have hUr : ‖U‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖P‖ := by
    apply ContinuousLinearMap.opNorm_le_bound U
      (mul_nonneg (norm_nonneg e.symm.toContinuousLinearMap) (norm_nonneg P))
    intro x
    exact (e.symm.toContinuousLinearMap.le_opNorm (P.rangeRestrict x)).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (P.le_opNorm x) (norm_nonneg e.symm.toContinuousLinearMap))
  have hV : ‖V‖ ≤ ‖e.toContinuousLinearMap‖ := by
    apply ContinuousLinearMap.opNorm_le_bound V (norm_nonneg e.toContinuousLinearMap)
    intro x
    exact e.toContinuousLinearMap.le_opNorm x
  refine ⟨U, V, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change e.symm (P.rangeRestrict (P (e x))) = x
    have heq : P.rangeRestrict (P (e x)) = e x := by
      apply Subtype.ext
      change P (P (e x)) = (e x : X)
      rw [hfix, hfix]
    rw [heq, e.symm_apply_apply]
  · calc
      ‖U‖ * ‖V‖ ≤ (‖e.symm.toContinuousLinearMap‖ * ‖P‖) * ‖e.toContinuousLinearMap‖ :=
        mul_le_mul hUr hV (norm_nonneg V)
          (mul_nonneg (norm_nonneg e.symm.toContinuousLinearMap) (norm_nonneg P))
      _ = _ := by ring

theorem IsomorphicWithBound.factorsIdentityWith_projection
    {P : X →L[𝕜] X} {C : ℝ} (hP : P.comp P = P)
    (h : IsomorphicWithBound 𝕜 X (LinearMap.range P.toLinearMap) C) :
    FactorsIdentityWith P X (C * ‖P‖) := by
  obtain ⟨e, he⟩ := h
  exact (projection_factorsIdentityWith_of_range_equiv P hP e).mono
    (mul_le_mul_of_nonneg_right he (norm_nonneg _))

theorem projection_factorsIdentity_of_range_equiv
    (P : X →L[𝕜] X) (hP : P.comp P = P)
    (h : Nonempty (X ≃L[𝕜] LinearMap.range P.toLinearMap)) : FactorsIdentity P X := by
  obtain ⟨e⟩ := h
  exact (projection_factorsIdentityWith_of_range_equiv P hP e).forget_bound

theorem IsPrimary.projection_factor_dichotomy (h : IsPrimary 𝕜 X)
    (P : X →L[𝕜] X) (hP : P.comp P = P) :
    FactorsIdentity P X ∨ FactorsIdentity (ContinuousLinearMap.id 𝕜 X - P) X := by
  exact (h P hP).imp (projection_factorsIdentity_of_range_equiv P hP)
    (projection_factorsIdentity_of_range_equiv _ (complementary_projection hP))

end ThesisCommon
