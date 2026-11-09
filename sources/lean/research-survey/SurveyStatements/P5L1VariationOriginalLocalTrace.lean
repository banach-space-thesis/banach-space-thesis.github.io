import SurveyStatements.P5L1VariationArbitraryTrace

/-! The paper's normalized averages on finite equal-dyadic sets. The
definition averages the equally sized descendant fibers of each root
interval; its normalization is exactly the reciprocal set measure. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem haarOperatorDiagonal_on_meanZero (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (n : ℕ) (k : Fin (2 ^ n)) :
    haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k =
      lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k (R (meanZeroHaar 𝕜 n k)).val := by
  change lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
    (R (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))).val = _
  rw [meanZeroProjection_haar]

theorem haarOperatorDiagonal_eq_normalized_diagonal (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarNormalizedCoordinate 𝕜 ⟨1, le_rfl⟩ (some ⟨n, k⟩)
      (extendMeanZero 𝕜 R (lpHaarNormalizedVector 𝕜 ⟨1, le_rfl⟩ (some ⟨n, k⟩))) =
        haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k := by
  simpa only [lpHaarRawCoordinate, lpHaarRawVector, haarOperatorDiagonal] using
    lpHaarRawCoordinate_diagonal_normalized 𝕜 ⟨1, le_rfl⟩ (by norm_num)
      (extendMeanZero 𝕜 R) (some ⟨n, k⟩)

theorem terminalFiber_disjoint_roots (n r : ℕ) (hr : r ≤ n)
    (a b : Fin (2 ^ r)) (hab : a ≠ b) :
    Disjoint (terminalFiber n r hr a) (terminalFiber n r hr b) := by
  apply Finset.disjoint_left.mpr
  intro k hka hkb
  have ha : prefixIndex n r hr k = a := by simpa [terminalFiber] using hka
  have hb : prefixIndex n r hr k = b := by simpa [terminalFiber] using hkb
  exact hab (ha.symm.trans hb)

theorem terminalFiber_card_independent_of_root (n r : ℕ) (hr : r ≤ n)
    (a b : Fin (2 ^ r)) :
    (terminalFiber n r hr a).card = (terminalFiber n r hr b).card := by
  have ha := terminalFiber_card_radius n r hr a
  have hb := terminalFiber_card_radius n r hr b
  have hpos := intervalLpDyadicRadius_pos n
  have hcast : ((terminalFiber n r hr a).card : ℝ) = ((terminalFiber n r hr b).card : ℝ) := by
    nlinarith
  exact_mod_cast hcast

def equalDyadicLevelAverage (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ)
    (S : Finset (Fin (2 ^ r))) (j : ℕ) : 𝕜 :=
  (S.card : 𝕜)⁻¹ * ∑ root ∈ S, localLevelAverage 𝕜 R (r + j) r (by omega) root

theorem equalDyadicLevelAverage_eq_descendant_average (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ)
    (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    equalDyadicLevelAverage 𝕜 R r S j =
      (∑ root ∈ S, ((terminalFiber (r + j) r (by omega) root).card : 𝕜))⁻¹ *
        ∑ root ∈ S, ∑ k ∈ terminalFiber (r + j) r (by omega) root,
          haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) (r + j) k := by
  let root₀ : Fin (2 ^ r) := ⟨0, by positivity⟩
  have hcard (root : Fin (2 ^ r)) :
      ((terminalFiber (r + j) r (by omega) root).card : 𝕜) =
        ((terminalFiber (r + j) r (by omega) root₀).card : 𝕜) := by
    rw [terminalFiber_card_independent_of_root (r + j) r (by omega) root root₀]
  rw [equalDyadicLevelAverage]
  simp_rw [localLevelAverage, hcard]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_inv_rev]
  ring

theorem blockParent_real_measure (r : ℕ) (S : Finset (Fin (2 ^ r))) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) =
      (S.card : ℝ) * intervalLpDyadicRadius r := by
  rw [lpHaarBlockParent, measureReal_biUnion_finset
    (fun k hk j hj hne => lpHaarLevelCells_disjoint r hne)
    (fun k hk => (show MeasurableSet (lpHaarCell r k) from measurableSet_Ioc))]
  simp_rw [dyadicCell_real_measure]
  simp only [Finset.sum_const, nsmul_eq_mul]

theorem equalDyadicLevelAverage_eq_normalized_trace (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ)
    (S : Finset (Fin (2 ^ r))) (hS : S.Nonempty) (j : ℕ) :
    equalDyadicLevelAverage 𝕜 R r S j =
      ((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜)⁻¹ *
        lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) (r + j)
          (lpHaarBlockParent r S) := by
  rw [equalDyadicLevelAverage, levelTrace_blockParent]
  simp_rw [operator_levelTrace_cell_eq_average 𝕜 R (r + j) r (by omega)]
  rw [← Finset.mul_sum, blockParent_real_measure]
  push_cast
  have hc : (S.card : 𝕜) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  have hr : (intervalLpDyadicRadius r : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos r).ne'
  field_simp

theorem original_local_L1_trace (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    ∃ m : IntervalLinfty 𝕜, ‖m‖ ≤ 2 * ‖R‖ ∧
      ∀ r : ℕ, ∀ S : Finset (Fin (2 ^ r)), S.Nonempty →
        Tendsto (equalDyadicLevelAverage 𝕜 R r S) atTop
          (𝓝 (((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜)⁻¹ *
            ∫ x in lpHaarBlockParent r S, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨m, hm, htrace⟩ := arbitrary_operator_full_local_trace_Linfty_density 𝕜 R
  refine ⟨m, hm, ?_⟩
  intro r S hS
  have ht := (htrace ⟨r, S⟩).comp (tendsto_add_atTop_nat r)
  have ht' : Tendsto (fun j => lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R))
      (r + j) (lpHaarBlockParent r S)) atTop
      (𝓝 (∫ x in lpHaarBlockParent r S, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
    simpa only [lpHaarDyadicSet, Function.comp_apply, Nat.add_comm] using ht
  have hnorm := ht'.const_mul
    (((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜)⁻¹)
  simpa only [← equalDyadicLevelAverage_eq_normalized_trace 𝕜 R r S hS] using hnorm

end SurveyStatements.P5L1Variation
