import ThesisCommon.Analysis.JamesTreeSelectedColumnErrors
import ThesisCommon.Analysis.JamesTreeSupportForkOperators
import ThesisCommon.Analysis.JamesTreeReindexedReciprocalSelection
import ThesisCommon.Analysis.JamesTreeSummableColumnBounds

/-! Andrew's actual finite-column factorization.  The support-delayed
tree, scalar branch selection, recursive finite-frontier pruning, all-vector
readback estimates and Neumann correction are all constructed here. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

set_option maxHeartbeats 1400000 in
theorem jamesTree_finite_column_factor_dichotomy
    (hMask : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (hchain : JamesTreeSegmentsAreChains S)
    (hL : ∀ m, JamesTreeMaskClosed S (dyadicInitialLevels m))
    (hLt : ∀ m, JamesTreeMaskClosed S (dyadicInitialLevels m)ᶜ)
    (hC : ∀ r, JamesTreeMaskClosed S (dyadicDescendantCone r))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    (hbranch : ∀ t, JamesTreeChainClosed S (dyadicFalseRay t))
    (hI : ∀ t, S.allows (dyadicTreeInterval [] t))
    (hclosure : ∀ d, JamesTreeDelayedForkClosure S d)
    (hEnum : ∀ m, JamesTreeMaskClosed S (dyadicEnumerationInitial m : Set DyadicTreeNode))
    (hp : 1<p.val.toReal)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (N : DyadicTreeNode → ℕ) (hN : ∀ t, t.length≤N t)
    (hT : ∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL _)
      (T (jamesTreeUnit t))=T (jamesTreeUnit t))
    (hcompl : ∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL _)
      ((ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S)-T) (jamesTreeUnit t))=
        (ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S)-T) (jamesTreeUnit t)) :
    FactorsIdentityWith T (SegmentJamesTreeSpace 𝕜 p S) 6 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _-T) (SegmentJamesTreeSpace 𝕜 p S) 6 := by
  let d₀ := dyadicSupportFork N
  obtain ⟨Q,hQT,e,hinverse⟩ := exists_jamesTree_reindexed_branch_inverse
    (lt_trans zero_lt_one hp) hMask hchain dyadicFalseRay hbranch dyadicFalseRay_contains d₀.node T
  have hQ : ∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL _)
      (Q (jamesTreeUnit t))=Q (jamesTreeUnit t) := by
    rcases hQT with rfl | rfl
    · exact hT
    · exact hcompl
  let d := d₀.comp e
  have hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (d.fork v).length) (hL _)
      (Q (jamesTreeUnit (d.node v)))=Q (jamesTreeUnit (d.node v)) :=
    jamesTree_supportFork_column_fixed hL N hN Q hQ e
  obtain ⟨a⟩ := exists_jamesTreeColumnFrontierRun d Q hchain hL hLt hC hB hp hfinite
    jamesTreePruningTolerance jamesTreePruningTolerance_pos (DyadicSubtreeEmbedding.cone [])
  obtain ⟨D,R,hD,_,hRD,_,hR⟩ := hinverse a.tree
  let he := hclosure (d.comp a.tree)
  have hf : FactorsIdentityWith Q (SegmentJamesTreeSpace 𝕜 p S) 6 := by
    apply jamesTree_delayed_compression_factors_six hEnum (d.comp a.tree) he Q D R hRD hR
      jamesTreeColumnErrorWeight_summable jamesTreeColumnErrorWeight_tsum.le
    intro s
    rw [jamesTree_diagonal_unit hL D _ hD s]
    have hcoef : jamesTreeBranchCoefficient dyadicFalseRay hbranch Q (d₀.node ((e.comp a.tree) s)) =
        ∑ t∈dyadicTreeInterval [] (d.fork (a.tree s)),
          jamesTreeCoordinate t (Q (jamesTreeUnit (d.node (a.tree s)))) := by
      simpa only [DyadicDelayedFork.comp_node,DyadicDelayedFork.comp_fork,d,d₀,
        DyadicSubtreeEmbedding.comp_apply] using
        jamesTree_supportFork_branch_eq_sum hL hbranch N hN Q hQ (e.comp a.tree) s
    rw [hcoef]
    simpa only [Equiv.apply_symm_apply] using
      a.read_column_error_budget hfinite hI he (dyadicTreeEnumeration.symm s)
  rcases hQT with rfl | rfl
  · exact Or.inl hf
  · exact Or.inr hf

end ThesisCommon
