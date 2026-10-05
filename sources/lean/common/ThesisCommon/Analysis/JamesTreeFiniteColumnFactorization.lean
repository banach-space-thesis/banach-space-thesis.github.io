import ThesisCommon.Analysis.JamesTreeFiniteColumnApproximation
import ThesisCommon.Analysis.SharpFactorization

/-! The final perturbation from finite-column operators to arbitrary operators
on the actual tree completion. This bridge is explicitly conditional on the
finite-column factorisation dichotomy; the recursive selection must prove that
input before either original James-tree theorem can be counted complete. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTree_hasCPFP_twelve_of_finite_column_dichotomy
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hfactor : ∀ (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
      (N : DyadicTreeNode → ℕ),
      (∀ t, t.length ≤ N t) →
      (∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t))
        (T (jamesTreeUnit t)) = T (jamesTreeUnit t)) →
      (∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t))
        ((ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) (jamesTreeUnit t)) =
          (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) (jamesTreeUnit t)) →
      FactorsIdentityWith T (SegmentJamesTreeSpace 𝕜 p S) 6 ∨
        FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T)
          (SegmentJamesTreeSpace 𝕜 p S) 6) :
    HasCPFP 𝕜 (SegmentJamesTreeSpace 𝕜 p S) 12 := by
  intro T
  obtain ⟨T', N, hnear, hN, _, hT', hcompl⟩ :=
    exists_jamesTree_finite_column_perturbation hL T (by norm_num : (0 : ℝ) < 1/12)
  have hsmall : 6 * ‖T' - T‖ ≤ (1/2 : ℝ) := by linarith
  rcases hfactor T' N hN hT' hcompl with h | h
  · left
    have hs : 6 * ‖T - T'‖ ≤ (1/2 : ℝ) := by
      simpa only [norm_sub_rev] using hsmall
    simpa only [show (6 : ℝ) / (1 - (1/2)) = 12 by norm_num] using
      h.perturb_fraction (by norm_num : (1/2 : ℝ) < 1) hs
  · right
    have hs : 6 * ‖(ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) -
        (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T')‖ ≤ (1/2 : ℝ) := by
      have heq : (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) -
          (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T') = T' - T := by abel
      simpa only [heq] using hsmall
    simpa only [show (6 : ℝ) / (1 - (1/2)) = 12 by norm_num] using
      h.perturb_fraction (by norm_num : (1/2 : ℝ) < 1) hs

end ThesisCommon
