import SurveyStatements.P5L1VariationArbitraryDensity

/-! The original local L¹ trace conclusion on every finite equal-dyadic
set, for an arbitrary bounded operator on actual mean-zero interval L¹. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem stepSymbol_integrable (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ) :
    Integrable (stepSymbol 𝕜 d n) (volume.restrict (Icc (0 : ℝ) 1)) := by
  exact integrable_finset_sum Finset.univ (fun k hk =>
    (integrable_const (d n k)).indicator measurableSet_Ioc)

theorem levelTrace_blockParent (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (l r : ℕ) (S : Finset (Fin (2 ^ r))) :
    lpHaarLevelTrace d l (lpHaarBlockParent r S) =
      ∑ k ∈ S, lpHaarLevelTrace d l (lpHaarCell r k) := by
  rw [← stepSymbol_setIntegral]
  rw [lpHaarBlockParent, integral_biUnion_finset S
    (fun k hk => (show MeasurableSet (lpHaarCell r k) from measurableSet_Ioc))
    (fun k hk j hj hne => lpHaarLevelCells_disjoint r hne)
    (fun k hk => (stepSymbol_integrable 𝕜 d l).integrableOn)]
  simp_rw [stepSymbol_setIntegral]

theorem arbitrary_operator_full_local_trace_Linfty_density (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    ∃ m : IntervalLinfty 𝕜, ‖m‖ ≤ 2 * ‖R‖ ∧ ∀ i : LpHaarDyadicSetIndex,
      Tendsto (fun n => lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) n
        (lpHaarDyadicSet i)) atTop
          (𝓝 (∫ x in lpHaarDyadicSet i, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨m, hm, hint, htrace⟩ := arbitrary_operator_full_cell_trace_Linfty_density 𝕜 R
  have hmI : Integrable m (volume.restrict (Icc (0 : ℝ) 1)) :=
    (Lp.memLp m).integrable (by simp)
  refine ⟨m, hm, ?_⟩
  rintro ⟨r, S⟩
  change Tendsto (fun n => lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) n
    (lpHaarBlockParent r S)) atTop
      (𝓝 (∫ x in lpHaarBlockParent r S, m x ∂(volume.restrict (Icc (0 : ℝ) 1))))
  simp_rw [levelTrace_blockParent]
  rw [lpHaarBlockParent, integral_biUnion_finset S
    (fun k hk => (show MeasurableSet (lpHaarCell r k) from measurableSet_Ioc))
    (fun k hk j hj hne => lpHaarLevelCells_disjoint r hne)
    (fun k hk => hmI.integrableOn)]
  exact tendsto_finset_sum S (fun k hk => htrace r k)

end SurveyStatements.P5L1Variation
