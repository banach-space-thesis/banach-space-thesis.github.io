import ThesisCommon.Analysis.JamesTreeReciprocalMultipliers
import ThesisCommon.Analysis.JamesTreeSelectedBranchCoefficients

/-! The actual operator dichotomy produces coefficient multipliers with
uniformly bounded reciprocals after every later strong subtree selection.
This is the quantitative branch-inversion input, not a claim that the full
operator compression has already become diagonal. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem exists_jamesTree_uniform_branch_inverse (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (hchain : JamesTreeSegmentsAreChains S)
    (B : DyadicTreeNode → Set DyadicTreeNode)
    (hB : ∀ t, JamesTreeChainClosed S (B t)) (ht : ∀ t, t ∈ B t)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S) :
    ∃ Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S,
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 _ - T) ∧
      ∃ e : DyadicSubtreeEmbedding, ∀ g : DyadicSubtreeEmbedding,
        ∃ D R : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S,
          (∀ x t, jamesTreeCoordinate t (D x) =
            jamesTreeBranchCoefficient B hB Q ((e.comp g) t) * jamesTreeCoordinate t x) ∧
          (∀ x t, jamesTreeCoordinate t (R x) =
            (jamesTreeBranchCoefficient B hB Q ((e.comp g) t))⁻¹ * jamesTreeCoordinate t x) ∧
          R.comp D = ContinuousLinearMap.id 𝕜 _ ∧ ‖D‖ ≤ ‖Q‖+1/4 ∧ ‖R‖ ≤ 3 := by
  let δ (n : ℕ) : ℝ := (1/8) * (1/2 : ℝ)^n
  have hδ (n) : 0 < δ n := by dsimp [δ]; positivity
  have hanti : Antitone δ := antitone_nat_of_succ_le (fun n => by
    dsimp [δ]
    rw [pow_succ]
    have hn : 0 ≤ (1/2 : ℝ)^n := by positivity
    nlinarith)
  have hg : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable δ := hg.mul_left _
  have htotal : (∑' n, δ n) = 1/4 := by
    rw [show δ = (fun n => (1/8 : ℝ)*(1/2 : ℝ)^n) from rfl, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)]
    norm_num
  let Q (c : Bool) := if c then T else ContinuousLinearMap.id 𝕜 _ - T
  obtain ⟨c,e,hlower,hosc⟩ := exists_dyadic_scalar_descendant_choice
    (fun c => jamesTreeBranchCoefficient B hB (Q c)) (fun c => ‖Q c‖)
    (fun c t => norm_jamesTreeBranchCoefficient_le B hB (Q c) t) (1/2)
    (fun t => jamesTreeChainFunctional_half_dichotomy (B t) (hB t) t (ht t) T) δ hδ
  refine ⟨Q c, ?_, e, ?_⟩
  · cases c <;> simp [Q]
  · intro g
    obtain ⟨D,R,hD,hR,heq,hnD,hnR⟩ := exists_jamesTree_selected_reciprocal_multipliers hp hS hchain
      (jamesTreeBranchCoefficient B hB (Q c)) e g (by norm_num : (0 : ℝ)<1/2)
      hlower (norm_jamesTreeBranchCoefficient_le B hB (Q c)) δ (fun n => (hδ n).le) hanti hsum hosc
    refine ⟨D,R,hD,hR,heq,?_,?_⟩
    · simpa only [htotal] using hnD
    · norm_num [htotal] at hnR ⊢
      exact hnR

theorem exists_literalJamesTree_uniform_branch_inverse (hp : 0 < p.val.toReal)
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p) :
    ∃ Q : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p,
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 _ - T) ∧
      ∃ e : DyadicSubtreeEmbedding, ∀ g : DyadicSubtreeEmbedding,
        ∃ D R : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p,
          (∀ x t, jamesTreeCoordinate t (D x) =
            literalJamesTreeBranchCoefficient Q ((e.comp g) t) * jamesTreeCoordinate t x) ∧
          (∀ x t, jamesTreeCoordinate t (R x) =
            (literalJamesTreeBranchCoefficient Q ((e.comp g) t))⁻¹ * jamesTreeCoordinate t x) ∧
          R.comp D = ContinuousLinearMap.id 𝕜 _ ∧ ‖D‖ ≤ ‖Q‖+1/4 ∧ ‖R‖ ≤ 3 :=
  exists_jamesTree_uniform_branch_inverse hp (fun A _ => literalJamesTreeMaskClosed_any A)
    literalJamesTreeSegmentsAreChains dyadicFalseRay _ dyadicFalseRay_contains T

theorem exists_consecutiveJamesTree_uniform_branch_inverse (hp : 0 < p.val.toReal)
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p) :
    ∃ Q : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p,
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 _ - T) ∧
      ∃ e : DyadicSubtreeEmbedding, ∀ g : DyadicSubtreeEmbedding,
        ∃ D R : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p,
          (∀ x t, jamesTreeCoordinate t (D x) =
            consecutiveJamesTreeBranchCoefficient Q ((e.comp g) t) * jamesTreeCoordinate t x) ∧
          (∀ x t, jamesTreeCoordinate t (R x) =
            (consecutiveJamesTreeBranchCoefficient Q ((e.comp g) t))⁻¹ * jamesTreeCoordinate t x) ∧
          R.comp D = ContinuousLinearMap.id 𝕜 _ ∧ ‖D‖ ≤ ‖Q‖+1/4 ∧ ‖R‖ ≤ 3 :=
  exists_jamesTree_uniform_branch_inverse hp (fun _ => consecutiveJamesTreeMaskClosed_segment)
    consecutiveJamesTreeSegmentsAreChains dyadicFalseRay _ dyadicFalseRay_contains T

end ThesisCommon
