import SurveyStatements.P5L1VariationChildFlips
import SurveyStatements.P5L1VariationLocalOutside

/-! Off-diagonal cancellation for the actual finite local Reynolds average.
Every cancellation uses one of the constructed child flips. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem localFiniteReynolds_coordinate_zero (𝕜 : Type*) [RCLike 𝕜]
    (M n m r : ℕ) (hn : n + 1 ≤ M) (hm : m + 1 ≤ M) (hr : r ≤ n)
    (root : Fin (2 ^ r)) (k : Fin (2 ^ n)) (hk : prefixIndex n r hr k = root)
    (j : Fin (2 ^ m)) (hne : (⟨m, j⟩ : Σ l : ℕ, Fin (2 ^ l)) ≠ ⟨n, k⟩)
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ m j
      (localFiniteReynolds 𝕜 M r (by omega) root R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)) = 0 := by
  let ρ := localDyadicTreeLeafAction M r (by omega) root
  let R' := extendMeanZero 𝕜 R
  let q := lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ m j
  by_cases hmn : m ≤ n
  · let a : LocalDyadicTreePerm M r (by omega) root :=
      ⟨childFlip M n hn k, childFlip_mem_local M n r hn hr root k hk⟩
    apply terminalReynolds_coordinate_zero_of_input_flip M ρ R' a
      (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) q
    · exact childFlip_haar_neg 𝕜 M n hn k
    · have hv : terminalPermutation 𝕜 M a.val.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m j) =
          lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m j := by
        by_cases heq : m = n
        · subst m
          have hj : j ≠ k := by intro h; subst j; exact hne rfl
          exact childFlip_other_haar 𝕜 M n hn k j hj
        · exact childFlip_earlier_haar 𝕜 M n m hn (by omega) k j
      intro y
      have hc := terminalPermutation_coordinate_of_fixed_haar 𝕜 M m hm a.val j 1
        (childFlip_coarse_node M n m hn hmn k j) (by simpa using hv) y
      simpa only [one_mul] using hc
  · have hnm : n < m := by omega
    have hrm : r ≤ m := by omega
    by_cases hj : prefixIndex m r hrm j = root
    · let a : LocalDyadicTreePerm M r (by omega) root :=
        ⟨childFlip M m hm j, childFlip_mem_local M m r hm hrm root j hj⟩
      apply terminalReynolds_coordinate_zero_of_output_flip M ρ R' a
        (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) q
      · exact childFlip_earlier_haar 𝕜 M m n hm hnm j k
      · intro y
        have hc := terminalPermutation_coordinate_of_fixed_haar 𝕜 M m hm a.val j (-1)
          (childFlip_coarse_node M m m hm le_rfl j j)
          (by simpa using childFlip_haar_neg 𝕜 M m hm j) y
        simpa only [neg_one_mul] using hc
    · let a : LocalDyadicTreePerm M r (by omega) root :=
        ⟨childFlip M n hn k, childFlip_mem_local M n r hn hr root k hk⟩
      apply terminalReynolds_coordinate_zero_of_input_flip M ρ R' a
        (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) q
      · exact childFlip_haar_neg 𝕜 M n hn k
      · intro y
        have hc := terminalPermutation_coordinate_of_fixed_haar 𝕜 M m hm a.val j 1
          (localNodeAction_outside_fixed M m r (by omega) hrm root a j hj)
          (by simpa using localTerminalPermutation_haar_outside 𝕜 M m r hm hrm root a j hj) y
        simpa only [one_mul] using hc

theorem terminalReynolds_terminal_range {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Fintype G]
    (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (f : IntervalL1 𝕜) :
    lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) M (terminalReynolds M ρ R f) =
      terminalReynolds M ρ R f := by
  rw [terminalReynolds_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  have h := congrArg (fun L : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 =>
    L (R (terminalPermutation 𝕜 M (ρ g) f)))
    (terminalPermutation_mul 𝕜 M 1 (ρ g⁻¹))
  simpa only [ContinuousLinearMap.comp_apply, one_mul, terminalPermutation_one] using h

theorem localFiniteReynolds_integral_zero (𝕜 : Type*) [RCLike 𝕜]
    (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (f : IntervalL1 𝕜) :
    lpHaarIntegral (localFiniteReynolds 𝕜 M r hr root R f) = 0 := by
  rw [localFiniteReynolds, terminalReynolds_apply, map_smul, map_sum]
  have hz (g : LocalDyadicTreePerm M r hr root) : lpHaarIntegral
      (terminalPermutation 𝕜 M (localDyadicTreeLeafAction M r hr root g⁻¹)
        (extendMeanZero 𝕜 R (terminalPermutation 𝕜 M (localDyadicTreeLeafAction M r hr root g) f))) = 0 := by
    rw [show localDyadicTreeLeafAction M r hr root g⁻¹ = (g⁻¹).val.val from rfl,
      terminalPermutation_integral]
    exact (R (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩
      (terminalPermutation 𝕜 M (localDyadicTreeLeafAction M r hr root g) f))).property
  simp_rw [hz]
  simp

theorem localFiniteReynolds_haar_eigen (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n) (root : Fin (2 ^ r))
    (k : Fin (2 ^ n)) (hk : prefixIndex n r hr k = root)
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    localFiniteReynolds 𝕜 M r (by omega) root R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
        (localFiniteReynolds 𝕜 M r (by omega) root R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)) •
          lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  let y := localFiniteReynolds 𝕜 M r (by omega) root R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
  have hy : lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) M y = y :=
    terminalReynolds_terminal_range M (localDyadicTreeLeafAction M r (by omega) root)
      (extendMeanZero 𝕜 R) _
  have hi : lpHaarIntegral y = 0 := localFiniteReynolds_integral_zero 𝕜 M r (by omega) root R _
  change y = _
  trans lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) M y
  · exact hy.symm
  rw [lpHaarDyadicMean_eq_partialSum, lpHaarDyadicMean_root]
  change lpHaarIntegral y • lpHaarRawVector 𝕜 ⟨1, le_rfl⟩ none +
    (∑ m ∈ Finset.range M, lpHaarLevelProjection 𝕜 ⟨1, le_rfl⟩ m y) = _
  rw [hi, zero_smul, zero_add]
  rw [Finset.sum_eq_single n]
  · rw [lpHaarLevelProjection_apply, Finset.sum_eq_single k]
    · intro j hj hne
      have hz := localFiniteReynolds_coordinate_zero 𝕜 M n n r hn hn hr root k hk j
        (by intro h; exact hne (by simpa using h)) R
      rw [hz, zero_smul]
    · simp
  · intro m hm hne
    rw [lpHaarLevelProjection_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hz := localFiniteReynolds_coordinate_zero 𝕜 M n m r hn
      (by have hlt := Finset.mem_range.mp hm; omega) hr root k hk j
      (by intro h; exact hne (congrArg Sigma.fst h)) R
    rw [hz, zero_smul]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

end SurveyStatements.P5L1Variation
