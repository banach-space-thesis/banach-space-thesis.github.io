import JLMS.CZeroSumFinite
import JLMS.CZeroSumOperators
import ThesisCommon.Analysis.Factorization

/-! Operator-norm estimates from finite sums of actual c₀-block norms.
These estimates make the mixed-block requirement in ordinal preservation
explicit, and give bounded identity factors once that requirement holds. -/

noncomputable section
open Set Filter Topology
namespace Posets
attribute [local instance] Classical.typeDecidableEq
universe u v w
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type u} {E : I → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000

local instance ordinalApproximationSumGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) :=
  inferInstance
local instance ordinalApproximationSumSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) :=
  inferInstance

def cZeroOperatorBlock (T : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E)
    (i j : I) : E j →L[𝕜] E i :=
  (JLMS.CZeroSum.evalCLM i).comp (T.comp (JLMS.CZeroSum.singleIsometry j).toContinuousLinearMap)

@[simp] theorem cZeroOperatorBlock_apply
    (T : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E) (i j : I) (x : E j) :
    cZeroOperatorBlock T i j x = T (JLMS.CZeroSum.single j x) i := rfl

theorem cZeroSum_opNorm_le_of_block_sums
    (T : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E) {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ i (s : Finset I), ∑ j ∈ s, ‖cZeroOperatorBlock T i j‖ ≤ ε) :
    ‖T‖ ≤ ε := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound T hε
  intro x
  have hfinite (s : Finset I) : ‖T (JLMS.CZeroSum.truncate s x)‖ ≤ ε * ‖x‖ := by
    apply JLMS.CZeroSum.norm_le (mul_nonneg hε (norm_nonneg x))
    intro i
    have heq : T (JLMS.CZeroSum.truncate s x) i =
        ∑ j ∈ s, cZeroOperatorBlock T i j (x j) := by
      rw [JLMS.CZeroSum.truncate_eq_sum_single]
      change ((JLMS.CZeroSum.evalCLM i).comp T) (∑ j ∈ s, JLMS.CZeroSum.single j (x j)) = _
      rw [map_sum]
      rfl
    rw [heq]
    calc
      ‖∑ j ∈ s, cZeroOperatorBlock T i j (x j)‖ ≤
          ∑ j ∈ s, ‖cZeroOperatorBlock T i j (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, ‖cZeroOperatorBlock T i j‖ * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact ((cZeroOperatorBlock T i j).le_opNorm (x j)).trans
          (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm j) (norm_nonneg _))
      _ = (∑ j ∈ s, ‖cZeroOperatorBlock T i j‖) * ‖x‖ := (Finset.sum_mul ..).symm
      _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right (hrow i s) (norm_nonneg x)
  exact le_of_tendsto ((T.continuous.tendsto x).comp (JLMS.CZeroSum.tendsto_truncate x)).norm
    (Eventually.of_forall hfinite)

theorem cZeroOperatorBlock_sub
    (T S : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E) (i j : I) :
    cZeroOperatorBlock (T - S) i j = cZeroOperatorBlock T i j - cZeroOperatorBlock S i j := by
  ext x
  rfl

@[simp] theorem cZeroOperatorBlock_id (i : I) :
    cZeroOperatorBlock (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)) i i =
      ContinuousLinearMap.id 𝕜 (E i) := by
  ext x
  exact JLMS.CZeroSum.single_apply_self (𝕜 := 𝕜) (E := E) i x

theorem cZeroOperatorBlock_id_of_ne {i j : I} (hij : i ≠ j) :
    cZeroOperatorBlock (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)) i j = 0 := by
  ext x
  exact JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := E) j x hij

theorem cZeroSum_norm_sub_id_le_of_offDiagonal
    (T : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E) {ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i, cZeroOperatorBlock T i i = ContinuousLinearMap.id 𝕜 (E i))
    (hrow : ∀ i (s : Finset I), ∑ j ∈ s.erase i, ‖cZeroOperatorBlock T i j‖ ≤ ε) :
    ‖T - ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)‖ ≤ ε := by
  classical
  apply cZeroSum_opNorm_le_of_block_sums _ hε
  intro i s
  have hzero : ‖cZeroOperatorBlock (T - ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)) i i‖ = 0 := by
    rw [cZeroOperatorBlock_sub, hdiag i, cZeroOperatorBlock_id, sub_self, norm_zero]
  calc
    (∑ j ∈ s, ‖cZeroOperatorBlock (T - ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)) i j‖) =
        ∑ j ∈ s.erase i, ‖cZeroOperatorBlock (T - ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)) i j‖ := by
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
      rw [cZeroOperatorBlock_sub, cZeroOperatorBlock_id_of_ne (Finset.ne_of_mem_erase hj).symm,
        sub_zero]
    _ ≤ ε := hrow i s

theorem cZeroSum_factorsIdentityWith_of_offDiagonal [∀ i, CompleteSpace (E i)]
    (T : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε < 1 / 2)
    (hdiag : ∀ i, cZeroOperatorBlock T i i = ContinuousLinearMap.id 𝕜 (E i))
    (hrow : ∀ i (s : Finset I), ∑ j ∈ s.erase i, ‖cZeroOperatorBlock T i j‖ ≤ ε) :
    ThesisCommon.FactorsIdentityWith T (JLMS.CZeroSum 𝕜 E) 2 := by
  let D := ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E)
  have hid : ThesisCommon.FactorsIdentityWith D (JLMS.CZeroSum 𝕜 E) 1 := by
    refine ⟨D, D, ?_, ?_⟩
    · ext x
      rfl
    · calc
        ‖D‖ * ‖D‖ ≤ (1 : ℝ) * 1 :=
          mul_le_mul ContinuousLinearMap.norm_id_le ContinuousLinearMap.norm_id_le
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
  have hn : ‖T - D‖ < 1 / 2 :=
    (cZeroSum_norm_sub_id_le_of_offDiagonal T hε hdiag hrow).trans_lt hsmall
  simpa only [mul_one] using hid.perturb (by simpa only [one_mul] using hn)

end Posets
