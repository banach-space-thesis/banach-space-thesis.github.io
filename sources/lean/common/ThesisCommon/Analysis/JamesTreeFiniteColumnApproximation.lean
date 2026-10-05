import ThesisCommon.Analysis.JamesTreeColumnCorrections
import ThesisCommon.Analysis.JamesTreeLevelDecomposition
import Mathlib.Analysis.SpecificLimits.Basic

/-! Every actual bounded tree-space operator can be perturbed by arbitrarily
small norm so that each unit column has finite level support. The same cut
also supports the corresponding column of the complementary operator. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

set_option maxHeartbeats 800000 in
theorem exists_jamesTree_finite_column_perturbation
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T' : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
      (N : DyadicTreeNode → ℕ),
      ‖T' - T‖ < ε ∧ (∀ t, t.length ≤ N t) ∧
      (∀ t, T' (jamesTreeUnit t) =
        jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t)) (T (jamesTreeUnit t))) ∧
      (∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t))
        (T' (jamesTreeUnit t)) = T' (jamesTreeUnit t)) ∧
      (∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t))
        ((ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T') (jamesTreeUnit t)) =
        (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T') (jamesTreeUnit t)) := by
  classical
  let δ : DyadicTreeNode → ℝ := fun t => (ε / 4) * (1 / 2 : ℝ) ^ Encodable.encode t
  have hδ : ∀ t, 0 < δ t := fun t => by dsimp [δ]; positivity
  have hδs : Summable δ := summable_geometric_two_encode.mul_left (ε / 4)
  have hδsum : (∑' t, δ t) ≤ ε / 2 := by
    calc
      _ ≤ ∑' n : ℕ, (ε / 4) * (1 / 2 : ℝ) ^ n :=
        Summable.tsum_le_tsum_of_inj Encodable.encode Encodable.encode_injective
          (fun _ _ => by positivity) (fun _ => le_rfl) hδs
          (summable_geometric_two.mul_left (ε / 4))
      _ = ε / 2 := by rw [tsum_mul_left,tsum_geometric_two]; ring
  have hchoice : ∀ t, ∃ N, t.length ≤ N ∧
      ‖T (jamesTreeUnit t) - jamesTreeMask (dyadicInitialLevels N) (hL N)
        (T (jamesTreeUnit t))‖ < δ t := by
    intro t
    have hh : ∀ᶠ N in atTop,
        ‖T (jamesTreeUnit t) - jamesTreeMask (dyadicInitialLevels N) (hL N)
          (T (jamesTreeUnit t))‖ < δ t :=
      (tendsto_order.mp (jamesTreeLevelTail_tendsto hL (T (jamesTreeUnit t))).norm).2
        (δ t) (by simpa only [norm_zero] using hδ t)
    exact ((eventually_ge_atTop t.length).and hh).exists
  choose N hN hsmall using hchoice
  let d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S := fun t =>
    T (jamesTreeUnit t) -
      jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t)) (T (jamesTreeUnit t))
  have hds : Summable (fun t => ‖d t‖) :=
    hδs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => (hsmall t).le)
  let T' := T - jamesTreeColumnCorrection d
  have hc : ∀ t, T' (jamesTreeUnit t) =
      jamesTreeMask (dyadicInitialLevels (N t)) (hL (N t)) (T (jamesTreeUnit t)) := by
    intro t
    simp only [T', ContinuousLinearMap.sub_apply, jamesTreeColumnCorrection_unit d hds, d,
      sub_sub_cancel]
  refine ⟨T',N,?_,hN,hc,?_,?_⟩
  · have he : T' - T = -jamesTreeColumnCorrection d := by dsimp [T']; abel
    rw [he,norm_neg]
    exact ((norm_jamesTreeColumnCorrection_le d hds).trans
      ((hds.tsum_le_tsum (fun t => (hsmall t).le) hδs).trans hδsum)).trans_lt (by linarith)
  · intro t
    rw [hc]
    exact jamesTreeMask_idempotent _ _ _
  · intro t
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hc]
    rw [jamesTreeMask_unit _ _ (hN t), jamesTreeMask_idempotent]

end ThesisCommon

