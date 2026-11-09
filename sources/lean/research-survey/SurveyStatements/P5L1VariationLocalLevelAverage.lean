import SurveyStatements.P5L1VariationConjugateDiagonal
import SurveyStatements.P5L1VariationLocalDiagonal

/-! Identification of the genuine local Reynolds eigenvalues with the
finite average of the original operator's Haar diagonal over each level. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

def localLevelAverage (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (n r : ℕ) (hr : r ≤ n) (root : Fin (2 ^ r)) : 𝕜 :=
  ((terminalFiber n r hr root).card : 𝕜)⁻¹ *
    ∑ k ∈ terminalFiber n r hr root, haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k

theorem localFiniteReynolds_diagonal_constant (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (k j : Fin (2 ^ n))
    (hk : prefixIndex n r hr k = root) (hj : prefixIndex n r hr j = root) :
    haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n j =
      haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n k := by
  have hnr : n ≤ M := by omega
  have hrM : r ≤ M := hr.trans hnr
  obtain ⟨a, ha⟩ := localDyadicTree_transitive M n r hnr hr root k j hk hj
  rw [localFiniteReynolds_diagonal_apply 𝕜 M n r hn hrM root R j,
    localFiniteReynolds_diagonal_apply 𝕜 M n r hn hrM root R k]
  congr 1
  have hterm (g : LocalDyadicTreePerm M r hrM root) :
      haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n (nodeAction g.val n hnr j) =
        haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n (nodeAction (g * a).val n hnr k) := by
    rw [← ha]
    change haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n (nodeAction g.val n hnr (nodeAction a.val n hnr k)) =
      haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n (nodeAction (g.val * a.val) n hnr k)
    exact congrArg (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n)
      (nodeAction_mul g.val a.val n hnr k).symm
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun _ => rfl)

theorem localFiniteReynolds_level_diagonal_sum (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    (∑ k ∈ terminalFiber n r hr root,
      haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n k) =
        ∑ k ∈ terminalFiber n r hr root, haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k := by
  simp_rw [localFiniteReynolds_diagonal_apply 𝕜 M n r hn (by omega) root R]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs (g : LocalDyadicTreePerm M r (by omega) root) :
      (∑ k ∈ terminalFiber n r hr root,
        haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n (nodeAction g.val n (by omega) k)) =
          ∑ k ∈ terminalFiber n r hr root, haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k := by
    apply Finset.sum_bijective (nodePermutation g.val n (by omega))
      (nodePermutation g.val n (by omega)).bijective
    · intro k
      simp only [terminalFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (localNodeAction_preserves_root M n r (by omega) hr root g k).symm
    · intro k hk
      rfl
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (LocalDyadicTreePerm M r (by omega) root) : 𝕜) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem localFiniteReynolds_diagonal_eq_average (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (k : Fin (2 ^ n))
    (hk : prefixIndex n r hr k = root) :
    haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n k =
      localLevelAverage 𝕜 R n r hr root := by
  have hkmem : k ∈ terminalFiber n r hr root := by simp [terminalFiber, hk]
  have hc : ((terminalFiber n r hr root).card : 𝕜) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨k, hkmem⟩).ne'
  have hs := localFiniteReynolds_level_diagonal_sum 𝕜 M n r hn hr root R
  have hconst (j : Fin (2 ^ n)) (hj : j ∈ terminalFiber n r hr root) :
      haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n j =
        haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n k :=
    localFiniteReynolds_diagonal_constant 𝕜 M n r hn hr root R k j hk
      (by simpa [terminalFiber] using hj)
  rw [Finset.sum_congr rfl hconst] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  rw [localLevelAverage, ← hs, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem localFiniteReynolds_haar_average (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (k : Fin (2 ^ n))
    (hk : prefixIndex n r hr k = root) :
    localFiniteReynolds 𝕜 M r (by omega) root R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      localLevelAverage 𝕜 R n r hr root • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  rw [localFiniteReynolds_haar_eigen 𝕜 M n r hn hr root k hk R]
  change haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r (by omega) root R) n k • _ = _
  rw [localFiniteReynolds_diagonal_eq_average 𝕜 M n r hn hr root R k hk]

end SurveyStatements.P5L1Variation
