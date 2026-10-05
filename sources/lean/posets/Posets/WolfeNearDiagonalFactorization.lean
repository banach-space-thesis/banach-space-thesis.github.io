import Posets.WolfeNearDiagonalFactorizationInverse

/-! An actual restriction–operator–extension compression with a uniformly
dominant atomic diagonal supplies explicit factors of the identity. The
argument needs no separability or complemented-subcopy principle. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 L E F : Type*} [RCLike 𝕜] [TopologicalSpace L] [CompactSpace L]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem wolfe_nearDiagonal_compression_factors
    (M : JLMS.AtomicDualModel 𝕜 L)
    (T : E →L[𝕜] F) (J : JLMS.CZero 𝕜 L →L[𝕜] E) (Q : F →L[𝕜] JLMS.CZero 𝕜 L)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M (Q.comp (T.comp J)) x x‖)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp (Q.comp (T.comp J)))‖ ≤ ε) :
    ∃ R : F →L[𝕜] JLMS.CZero 𝕜 L,
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L) ∧
        ‖R‖ ≤ ‖Q‖ / (d - 3 * ε) := by
  obtain ⟨B, hB, hnorm⟩ := wolfe_nearDiagonal_exists_left_inverse M (Q.comp (T.comp J))
    hε hgap hdiag hoff
  refine ⟨B.comp Q, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using hB
  · calc
      ‖B.comp Q‖ ≤ ‖B‖ * ‖Q‖ := B.opNorm_comp_le Q
      _ ≤ (1 / (d - 3 * ε)) * ‖Q‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg Q)
      _ = ‖Q‖ / (d - 3 * ε) := by ring

theorem wolfe_nearDiagonal_compression_factors_with_bounds
    (M : JLMS.AtomicDualModel 𝕜 L)
    (T : E →L[𝕜] F) (J : JLMS.CZero 𝕜 L →L[𝕜] E) (Q : F →L[𝕜] JLMS.CZero 𝕜 L)
    {d ε C D : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d) (hJ : ‖J‖ ≤ C) (hQ : ‖Q‖ ≤ D)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M (Q.comp (T.comp J)) x x‖)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp (Q.comp (T.comp J)))‖ ≤ ε) :
    ∃ V : JLMS.CZero 𝕜 L →L[𝕜] E, ∃ R : F →L[𝕜] JLMS.CZero 𝕜 L,
      R.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L) ∧
        ‖V‖ ≤ C ∧ ‖R‖ ≤ D / (d - 3 * ε) := by
  obtain ⟨R, hR, hn⟩ := wolfe_nearDiagonal_compression_factors M T J Q hε hgap hdiag hoff
  exact ⟨J, R, hR, hJ, hn.trans (div_le_div_of_nonneg_right hQ (sub_pos.mpr hgap).le)⟩

end Posets
