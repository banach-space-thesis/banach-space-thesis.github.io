import PEMS.L1WeakNoncompactnessGeneral
import ThesisCommon.Analysis.RCLikeL1CutIdentities

/-! The residual uniform-integrability argument in source Lemma 5.4.
Cutoffs capturing the full localized noncompactness value leave uniformly
integrable remainders. All functions and cutoffs are actual L1 elements. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem extremal_cutoff_residual_unifIntegrable
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hmass : Tendsto (fun n => ν (A n)) atTop (𝓝 0))
    (hconv : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop
      (𝓝 (alphaTheta T univ))) :
    UnifIntegrable (fun n => (lpCut (A n)ᶜ (hA n).compl (T (f n)) : Y → 𝕜)) 1 ν := by
  intro ε hε
  let c := alphaTheta T univ
  obtain ⟨r, ⟨η, hη, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (s := {r : ℝ | ∃ η : ℝ, 0 < η ∧ r = smallSetSup T univ η})
    ⟨_, 1, zero_lt_one, rfl⟩
    (show alphaTheta T univ < c + ε / 3 by dsimp [c]; linarith)
  have hmass' : ∀ᶠ n in atTop, ν (A n) < ENNReal.ofReal (η / 2) :=
    hmass.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hη)))
  have hconv' : ∀ᶠ n in atTop, c - ε / 3 < ‖lpCut (A n) (hA n) (T (f n))‖ :=
    hconv.eventually (lt_mem_nhds (by dsimp [c]; linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmass'.and hconv')
  obtain ⟨δ, hδ, hsmall⟩ := finite_rclike_lOneCut_small_measure (Finset.range N)
    (fun n => lpCut (A n)ᶜ (hA n).compl (T (f n))) hε
  refine ⟨min δ (η / 2), lt_min hδ (half_pos hη), fun n B hB hνB => ?_⟩
  have hnorm : ‖lpCut B hB (lpCut (A n)ᶜ (hA n).compl (T (f n)))‖ ≤ ε := by
    by_cases hn : n < N
    · exact hsmall n (Finset.mem_range.mpr hn) B hB
        (hνB.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    · obtain ⟨hnmass, hncut⟩ := hN n (Nat.le_of_not_lt hn)
      have hνunion : ν (A n ∪ B) < ENNReal.ofReal η := by
        apply (measure_union_le _ _).trans_lt
        calc
          ν (A n) + ν B < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
            ENNReal.add_lt_add_of_lt_of_le (hνB.trans_lt ENNReal.ofReal_lt_top).ne hnmass
              (hνB.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
          _ = ENNReal.ofReal η := by
            rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le, add_halves]
      have hcutop : cutOperatorNorm T (A n ∪ B) ≤ smallSetSup T univ η := by
        simpa only [compl_univ, empty_union] using
          cutOperatorNorm_le_smallSetSup T univ MeasurableSet.univ ((hA n).union hB)
            (subset_univ _) hνunion
      have hcutnorm : ‖lpCut (A n ∪ B) ((hA n).union hB) (T (f n))‖ ≤
          smallSetSup T univ η := by
        have hh := ((lpCutL (A n ∪ B) ((hA n).union hB)).comp T).le_opNorm (f n)
        apply le_trans hh
        apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (hf n))
        simpa only [cutOperatorNorm_eq _ _ ((hA n).union hB)] using hcutop
      rw [norm_rclike_lOneCut_union (A n) B (hA n) hB] at hcutnorm
      linarith
  apply (ENNReal.toReal_le_toReal
    ((Lp.memLp (lpCut (A n)ᶜ (hA n).compl (T (f n)))).indicator hB).2.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε.le]
  simpa only [lpCut, Lp.norm_toLp] using hnorm

theorem extremal_cutoff_residual_uniformIntegrable
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hmass : Tendsto (fun n => ν (A n)) atTop (𝓝 0))
    (hconv : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop
      (𝓝 (alphaTheta T univ))) :
    UniformIntegrable (fun n => (lpCut (A n)ᶜ (hA n).compl (T (f n)) : Y → 𝕜)) 1 ν := by
  refine ⟨fun n => Lp.aestronglyMeasurable _,
    extremal_cutoff_residual_unifIntegrable T f hf A hA hmass hconv, ‖T‖₊, fun n => ?_⟩
  rw [← Lp.enorm_def, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  exact (norm_lpCut_le _ _ _).trans ((T.le_opNorm (f n)).trans
    (mul_le_of_le_one_right (norm_nonneg T) (hf n)))

theorem disjoint_extremal_cutoff_residual_uniformIntegrable [IsFiniteMeasure ν]
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Disjoint on A))
    (hconv : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop
      (𝓝 (localizedWeakNoncompactness T))) :
    UniformIntegrable (fun n => (lpCut (A n)ᶜ (hA n).compl (T (f n)) : Y → 𝕜)) 1 ν := by
  apply extremal_cutoff_residual_uniformIntegrable T f hf A hA
  · have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint (μ := ν)
      (fun n => (hA n).nullMeasurableSet) hdisj
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => bot_le) (fun n => measure_mono ?_)
    exact subset_iUnion₂_of_subset n le_rfl Subset.rfl
  · simpa only [localizedWeakNoncompactness_eq_alphaTheta_univ] using hconv

end PEMS
