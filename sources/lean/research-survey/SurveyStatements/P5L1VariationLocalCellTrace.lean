import SurveyStatements.P5L1VariationLocalLimits

/-! The finite local average agrees exactly with the actual integral
trace on its root interval. Hence every such trace has a full limit. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem dyadicCell_real_measure (n : ℕ) (k : Fin (2 ^ n)) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarCell n k) = intervalLpDyadicRadius n := by
  rw [measureReal_def, lpHaarCell_measure n k k.isLt,
    ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]

theorem terminalFiber_card_radius (n r : ℕ) (hr : r ≤ n) (root : Fin (2 ^ r)) :
    ((terminalFiber n r hr root).card : ℝ) * intervalLpDyadicRadius n =
      intervalLpDyadicRadius r := by
  have hm := measureReal_biUnion_finset (μ := volume.restrict (Icc (0 : ℝ) 1))
    (s := terminalFiber n r hr root) (f := fun k => lpHaarCell n k)
    (fun a _ b _ hab => lpHaarLevelCells_disjoint n hab)
    (fun _ _ => measurableSet_Ioc)
  rw [terminalFiber_cells, dyadicCell_real_measure] at hm
  simp_rw [dyadicCell_real_measure] at hm
  simpa only [Finset.sum_const, nsmul_eq_mul] using hm.symm

theorem levelTrace_cell_eq_fiber_sum (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n r : ℕ) (hr : r ≤ n) (root : Fin (2 ^ r)) :
    lpHaarLevelTrace d n (lpHaarCell r root) =
      (intervalLpDyadicRadius n : 𝕜) * ∑ k ∈ terminalFiber n r hr root, d n k := by
  have hterm (k : Fin (2 ^ n)) :
      ((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarCell r root ∩ lpHaarCell n k) : 𝕜) * d n k =
        if prefixIndex n r hr k = root then (intervalLpDyadicRadius n : 𝕜) * d n k else 0 := by
    by_cases hk : prefixIndex n r hr k = root
    · rw [if_pos hk]
      have hs : lpHaarCell n k ⊆ lpHaarCell r root := by
        simpa only [hk] using terminalCell_subset_prefix n r hr k
      rw [inter_eq_right.mpr hs, dyadicCell_real_measure]
    · rw [if_neg hk]
      have hdis : Disjoint (lpHaarCell r root) (lpHaarCell n k) :=
        (lpHaarLevelCells_disjoint r (Ne.symm hk)).mono_right (terminalCell_subset_prefix n r hr k)
      rw [Set.disjoint_iff_inter_eq_empty.mp hdis]
      simp
  rw [lpHaarLevelTrace]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  exact (Finset.mul_sum _ _ _).symm

theorem operator_levelTrace_cell_eq_average (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (n r : ℕ) (hr : r ≤ n) (root : Fin (2 ^ r)) :
    lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) n (lpHaarCell r root) =
      (intervalLpDyadicRadius r : 𝕜) * localLevelAverage 𝕜 R n r hr root := by
  rw [levelTrace_cell_eq_fiber_sum 𝕜 (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R))
    n r hr root, localLevelAverage]
  have hcR := terminalFiber_card_radius n r hr root
  have hc : ((terminalFiber n r hr root).card : 𝕜) ≠ 0 := by
    have hpos : 0 < ((terminalFiber n r hr root).card : ℝ) := by
      nlinarith [intervalLpDyadicRadius_pos n, intervalLpDyadicRadius_pos r]
    exact_mod_cast hpos.ne'
  have hcast : ((terminalFiber n r hr root).card : 𝕜) * (intervalLpDyadicRadius n : 𝕜) =
      (intervalLpDyadicRadius r : 𝕜) := by exact_mod_cast hcR
  rw [← hcast]
  field_simp

theorem arbitrary_operator_local_cell_trace_limit (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    ∃ c : 𝕜, ‖c‖ ≤ 2 * ‖R‖ ∧
      Tendsto (fun j => lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R))
        (r + j) (lpHaarCell r root)) atTop (𝓝 ((intervalLpDyadicRadius r : 𝕜) * c)) := by
  obtain ⟨_, _, c, hc, hlim⟩ := arbitrary_operator_local_average_limit 𝕜 R r root
  refine ⟨c, hc, ?_⟩
  have hformula (j : ℕ) := operator_levelTrace_cell_eq_average 𝕜 R (r + j) r (by omega) root
  simpa only [hformula] using tendsto_const_nhds.mul hlim

end SurveyStatements.P5L1Variation
