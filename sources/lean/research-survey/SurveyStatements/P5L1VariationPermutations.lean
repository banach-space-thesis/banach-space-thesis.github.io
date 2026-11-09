import SurveyStatements.P5L1VariationFinite
import SurveyStatements.P5Support.LpPartitionTransfer

/-! Genuine finite dyadic permutation transfers. They are norm-one maps on
interval L¹. Their identity is the actual terminal conditional expectation,
and their products are exactly the products of the leaf permutations. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

def terminalPermutation (𝕜 : Type*) [RCLike 𝕜] (M : ℕ)
    (σ : Equiv.Perm (Fin (2 ^ M))) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 :=
  lpHaarPartitionTransfer (by norm_num)
    (fun i : Fin (2 ^ M) => lpHaarCell M i)
    (fun i : Fin (2 ^ M) => lpHaarCell M (σ i))
    (fun _ => measurableSet_Ioc)

theorem terminalPermutation_norm_le (𝕜 : Type*) [RCLike 𝕜] (M : ℕ)
    (σ : Equiv.Perm (Fin (2 ^ M))) : ‖terminalPermutation 𝕜 M σ‖ ≤ 1 := by
  apply lpHaarPartitionTransfer_norm_le (by norm_num)
    (fun i : Fin (2 ^ M) => lpHaarCell M i)
    (fun i : Fin (2 ^ M) => lpHaarCell M (σ i))
    (fun _ => measurableSet_Ioc) (fun _ => measurableSet_Ioc)
    (lpHaarLevelCells_disjoint M)
  · intro i j hij
    exact lpHaarLevelCells_disjoint M (fun h => hij (σ.injective h))
  · exact lpHaarLevelCells_cover M
  · filter_upwards [lpHaarLevelCells_cover M] with x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨σ.symm i, by simpa using hi⟩
  · exact lpHaarLevelCells_nonzero M
  · intro i
    rw [lpHaarCell_measure M i i.isLt, lpHaarCell_measure M (σ i) (σ i).isLt]

theorem terminalPermutation_indicator (𝕜 : Type*) [RCLike 𝕜] (M : ℕ)
    (σ : Equiv.Perm (Fin (2 ^ M))) (i : Fin (2 ^ M)) (a : 𝕜) :
    terminalPermutation 𝕜 M σ
      (indicatorConstLp (1 : ℝ≥0∞)
        (show MeasurableSet (lpHaarCell M i) from measurableSet_Ioc)
        (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) a) =
      indicatorConstLp (1 : ℝ≥0∞)
        (show MeasurableSet (lpHaarCell M (σ i)) from measurableSet_Ioc)
        (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) a := by
  exact lpHaarPartitionTransfer_indicator (by norm_num)
    (fun i : Fin (2 ^ M) => lpHaarCell M i)
    (fun i : Fin (2 ^ M) => lpHaarCell M (σ i))
    (fun _ => measurableSet_Ioc) (fun _ => measurableSet_Ioc)
    (lpHaarLevelCells_disjoint M) (lpHaarLevelCells_nonzero M) i a

theorem terminalPermutation_apply (𝕜 : Type*) [RCLike 𝕜] (M : ℕ)
    (σ : Equiv.Perm (Fin (2 ^ M))) (f : IntervalL1 𝕜) :
    terminalPermutation 𝕜 M σ f = ∑ i : Fin (2 ^ M),
      indicatorConstLp (1 : ℝ≥0∞)
        (show MeasurableSet (lpHaarCell M (σ i)) from measurableSet_Ioc)
        (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _)
        (lpHaarPartitionAverage (by norm_num) (lpHaarCell M i) f) := by
  exact lpHaarPartitionTransfer_apply (by norm_num)
    (fun i : Fin (2 ^ M) => lpHaarCell M i)
    (fun i : Fin (2 ^ M) => lpHaarCell M (σ i))
    (fun _ => measurableSet_Ioc) f

theorem terminalPermutation_mul (𝕜 : Type*) [RCLike 𝕜] (M : ℕ)
    (σ τ : Equiv.Perm (Fin (2 ^ M))) :
    (terminalPermutation 𝕜 M σ).comp (terminalPermutation 𝕜 M τ) =
      terminalPermutation 𝕜 M (σ * τ) := by
  apply ContinuousLinearMap.ext
  intro f
  change terminalPermutation 𝕜 M σ (terminalPermutation 𝕜 M τ f) = _
  rw [terminalPermutation_apply 𝕜 M τ f, map_sum]
  simp_rw [terminalPermutation_indicator]
  exact (terminalPermutation_apply 𝕜 M (σ * τ) f).symm

theorem terminalPermutation_one (𝕜 : Type*) [RCLike 𝕜] (M : ℕ) :
    terminalPermutation 𝕜 M (1 : Equiv.Perm (Fin (2 ^ M))) =
      lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) M := by
  apply ContinuousLinearMap.ext
  intro f
  rw [terminalPermutation_apply]
  change lpHaarPartitionStep (fun i : Fin (2 ^ M) => lpHaarCell M i)
    (fun _ => measurableSet_Ioc)
    (fun i => lpHaarPartitionAverage (by norm_num) (lpHaarCell M i) f) = _
  exact (lpHaarPartitionMean_eq_step (by norm_num)
    (fun i : Fin (2 ^ M) => lpHaarCell M i)
    (fun _ => measurableSet_Ioc) (lpHaarLevelCells_disjoint M)
    (lpHaarLevelCells_cover M) (lpHaarLevelCells_nonzero M) f).symm

theorem terminalPermutation_inverse (𝕜 : Type*) [RCLike 𝕜] (M : ℕ)
    (σ : Equiv.Perm (Fin (2 ^ M))) :
    (terminalPermutation 𝕜 M σ⁻¹).comp (terminalPermutation 𝕜 M σ) =
      lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) M := by
  rw [terminalPermutation_mul, inv_mul_cancel, terminalPermutation_one]

end SurveyStatements.P5L1Variation

