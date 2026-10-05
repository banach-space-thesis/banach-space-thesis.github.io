import Posets.OrdinalBlockApproximation

/-! The genuine diagonal part of an operator on an arbitrary dependent c₀
sum, with an all-vector formula and an operator-norm estimate for the
off-diagonal remainder. -/
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace Posets
universe u v
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type u} {E : I → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
open JLMS
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem norm_cZeroOperatorBlock_le (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) (i j : I) :
    ‖cZeroOperatorBlock T i j‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖T (CZeroSum.single j x) i‖ ≤ ‖T‖ * ‖x‖
  exact ((T (CZeroSum.single j x)).norm_apply_le_norm i).trans
    (by simpa only [CZeroSum.norm_single] using T.le_opNorm (CZeroSum.single j x))

def cZeroOperatorDiagonal (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) :
    CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E :=
  CZeroSum.mapCLM (fun i => cZeroOperatorBlock T i i) (norm_nonneg T)
    (fun i => norm_cZeroOperatorBlock_le T i i)

@[simp] theorem cZeroOperatorDiagonal_apply
    (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) (x : CZeroSum 𝕜 E) (i : I) :
    cZeroOperatorDiagonal T x i = cZeroOperatorBlock T i i (x i) := rfl

theorem norm_cZeroOperatorDiagonal_le (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) :
    ‖cZeroOperatorDiagonal T‖ ≤ ‖T‖ :=
  CZeroSum.norm_mapCLM_le _ _ _

@[simp] theorem cZeroOperatorBlock_diagonal_self
    (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) (i : I) :
    cZeroOperatorBlock (cZeroOperatorDiagonal T) i i = cZeroOperatorBlock T i i := by
  apply ContinuousLinearMap.ext
  intro x
  change cZeroOperatorBlock T i i (CZeroSum.single i x i) = _
  rw [CZeroSum.single_apply_self]

theorem cZeroOperatorBlock_diagonal_ne
    (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) {i j : I} (hij : i ≠ j) :
    cZeroOperatorBlock (cZeroOperatorDiagonal T) i j = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change cZeroOperatorBlock T i i (CZeroSum.single j x i) = 0
  rw [CZeroSum.single_apply_ne j x hij, map_zero]

theorem norm_sub_cZeroOperatorDiagonal_le
    (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E) {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ i (s : Finset I), ∑ j ∈ s.erase i, ‖cZeroOperatorBlock T i j‖ ≤ ε) :
    ‖T - cZeroOperatorDiagonal T‖ ≤ ε := by
  classical
  apply cZeroSum_opNorm_le_of_block_sums _ hε
  intro i s
  have hzero : ‖cZeroOperatorBlock (T - cZeroOperatorDiagonal T) i i‖ = 0 := by
    rw [cZeroOperatorBlock_sub, cZeroOperatorBlock_diagonal_self, sub_self, norm_zero]
  calc
    (∑ j ∈ s, ‖cZeroOperatorBlock (T - cZeroOperatorDiagonal T) i j‖) =
        ∑ j ∈ s.erase i, ‖cZeroOperatorBlock (T - cZeroOperatorDiagonal T) i j‖ := by
      symm
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro j hjs hjn
      have hj : j = i := by
        by_contra h
        exact hjn (Finset.mem_erase.mpr ⟨h, hjs⟩)
      subst j
      exact hzero
    _ = ∑ j ∈ s.erase i, ‖cZeroOperatorBlock T i j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [cZeroOperatorBlock_sub, cZeroOperatorBlock_diagonal_ne T
        (Finset.ne_of_mem_erase hj).symm, sub_zero]
    _ ≤ ε := hrow i s

end Posets
