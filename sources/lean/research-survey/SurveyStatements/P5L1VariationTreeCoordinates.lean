import SurveyStatements.P5L1VariationTreeHaar
import SurveyStatements.P5Support.LpHaarBiorthogonal

/-! The dual coordinates of the actual finite dyadic permutation maps.
The identities are proved on the dense Haar span, including the constant
and the Haar levels killed by the terminal conditional expectation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem terminalPermutation_root (𝕜 : Type*) [RCLike 𝕜]
    (M : ℕ) (σ : DyadicTreePerm M) :
    terminalPermutation 𝕜 M σ.val (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ 0 0) =
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ 0 0 := by
  rw [terminalPermutation_cell 𝕜 M 0 (by omega) σ ⟨0, by simp⟩]
  have heq : nodeAction σ 0 (by omega) ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
    apply Fin.ext
    have hlt := (nodeAction σ 0 (by omega) ⟨0, by simp⟩).isLt
    simp only [pow_zero] at hlt
    omega
  rw [heq]

theorem terminalPermutation_kill_later_haar (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : M ≤ n) (σ : Equiv.Perm (Fin (2 ^ M))) (k : Fin (2 ^ n)) :
    terminalPermutation 𝕜 M σ (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = 0 := by
  have h := congrArg (fun L : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 =>
    L (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))
    (terminalPermutation_mul 𝕜 M σ 1)
  simp only [ContinuousLinearMap.comp_apply, mul_one] at h
  rw [terminalPermutation_one,
    lpHaarDyadicMean_kill_later_haar 𝕜 ⟨1, le_rfl⟩ (by norm_num) n M k k.isLt hn,
    map_zero] at h
  exact h.symm

theorem terminalPermutation_integral (𝕜 : Type*) [RCLike 𝕜]
    (M : ℕ) (σ : DyadicTreePerm M) (f : IntervalL1 𝕜) :
    lpHaarIntegral (terminalPermutation 𝕜 M σ.val f) = lpHaarIntegral f := by
  have heq : lpHaarIntegral.comp (terminalPermutation 𝕜 M σ.val) =
      (lpHaarIntegral : IntervalL1 𝕜 →L[𝕜] 𝕜) := by
    apply ContinuousLinearMap.ext_on (lpHaarSystem_dense_span 𝕜 ⟨1, le_rfl⟩ (by norm_num))
    intro v hv
    change lpHaarIntegral (terminalPermutation 𝕜 M σ.val v) = lpHaarIntegral v
    rcases hv with rfl | ⟨⟨n, k⟩, rfl⟩
    · rw [terminalPermutation_root]
    · by_cases hn : n + 1 ≤ M
      · rcases terminalPermutation_haar_signed 𝕜 M n hn σ k with h | h
        · rw [h, lpHaarIntegral_apply, lpHaarIntegral_apply,
            lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n _ (nodeAction σ n (by omega) k).isLt,
            lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n k k.isLt]
        · rw [h, map_neg]
          rw [lpHaarIntegral_apply, lpHaarIntegral_apply,
            lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n _ (nodeAction σ n (by omega) k).isLt,
            lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n k k.isLt, neg_zero]
      · rw [terminalPermutation_kill_later_haar 𝕜 M n (by omega), map_zero,
          lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n k k.isLt]
  exact congrArg (fun L : IntervalL1 𝕜 →L[𝕜] 𝕜 => L f) heq

theorem terminalPermutation_coordinate_of_signed_haar (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (σ : DyadicTreePerm M)
    (k : Fin (2 ^ n)) (ε : 𝕜)
    (hv : terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      ε • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)) (f : IntervalL1 𝕜) :
    lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)
        (terminalPermutation 𝕜 M σ.val f) =
      ε * lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f := by
  let q := lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
  let q' := lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)
  have heq : q'.comp (terminalPermutation 𝕜 M σ.val) = ε • q := by
    apply ContinuousLinearMap.ext_on (lpHaarSystem_dense_span 𝕜 ⟨1, le_rfl⟩ (by norm_num))
    intro v hv'
    change q' (terminalPermutation 𝕜 M σ.val v) = ε * q v
    rcases hv' with rfl | ⟨⟨m, j⟩, rfl⟩
    · rw [terminalPermutation_root, lpHaarCellVector_root_eq_const]
      change lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)
        (Lp.const 1 (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) =
          ε * lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
            (Lp.const 1 (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜))
      rw [lpHaarDyadicCoefficient_const 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k) 1,
        lpHaarDyadicCoefficient_const 𝕜 ⟨1, le_rfl⟩ n k 1, mul_zero]
    · by_cases hmn : m = n
      · subst m
        by_cases hj : j = k
        · subst j
          rw [hv, map_smul, smul_eq_mul]
          simp [q, q', lpHaarDyadicCoefficient_apply_level]
        · have hj' : nodeAction σ n (by omega) k ≠ nodeAction σ n (by omega) j := by
            intro h
            exact hj ((nodeAction_injective σ n (by omega)) h).symm
          rcases terminalPermutation_haar_signed 𝕜 M n hn σ j with h | h
          · rw [h]
            simp [q, q', lpHaarDyadicCoefficient_apply_level, hj', Ne.symm hj]
          · rw [h, map_neg]
            simp [q, q', lpHaarDyadicCoefficient_apply_level, hj', Ne.symm hj]
      · have hq : q (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m j) = 0 :=
          lpHaarDyadicCoefficient_other_level 𝕜 ⟨1, le_rfl⟩ (by norm_num) m n j k (Ne.symm hmn)
        rw [hq, mul_zero]
        by_cases hm : m + 1 ≤ M
        · rcases terminalPermutation_haar_signed 𝕜 M m hm σ j with h | h
          · rw [h]
            exact lpHaarDyadicCoefficient_other_level 𝕜 ⟨1, le_rfl⟩ (by norm_num)
              m n _ (nodeAction σ n (by omega) k) (Ne.symm hmn)
          · rw [h, map_neg]
            rw [show q' (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m (nodeAction σ m (by omega) j)) = 0 from
              lpHaarDyadicCoefficient_other_level 𝕜 ⟨1, le_rfl⟩ (by norm_num)
                m n _ (nodeAction σ n (by omega) k) (Ne.symm hmn), neg_zero]
        · rw [terminalPermutation_kill_later_haar 𝕜 M m (by omega), map_zero]
  exact congrArg (fun L : IntervalL1 𝕜 →L[𝕜] 𝕜 => L f) heq

theorem terminalPermutation_coordinate_of_fixed_haar (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (σ : DyadicTreePerm M)
    (k : Fin (2 ^ n)) (ε : 𝕜)
    (hnode : nodeAction σ n (by omega) k = k)
    (hv : terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      ε • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) (f : IntervalL1 𝕜) :
    lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k (terminalPermutation 𝕜 M σ.val f) =
      ε * lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f := by
  simpa only [hnode] using terminalPermutation_coordinate_of_signed_haar 𝕜 M n hn σ k ε
    (by simpa only [hnode] using hv) f

end SurveyStatements.P5L1Variation
