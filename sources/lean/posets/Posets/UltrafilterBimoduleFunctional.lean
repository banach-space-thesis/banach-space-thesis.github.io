import Posets.UltrafilterBimoduleRelations
import Posets.UltrafilterBimoduleExtension
import Mathlib.Analysis.SpecificLimits.Basic

/-! The discontinuous bimodule functional in Lemma 8.2. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets

set_option maxHeartbeats 800000 in
/-- Lemma 8.2. The algebraic extension assigns F_n's separating vectors the
unbounded values n, and vanishes on every relation annihilated by all F_n. -/
theorem lemma_8_2_proof (𝕜 : Type) [RCLike 𝕜]
    (U : Ultrafilter RowDomain) (V : Ultrafilter ColumnDomain) : Lemma_8_2 𝕜 U V := by
  letI : NormedAddCommGroup (OffDiagonal 𝕜) := inferInstance
  letI : NormedSpace 𝕜 (OffDiagonal 𝕜) := inferInstance
  intro h
  obtain ⟨L, hvalues, hzero⟩ := exists_linearMap_of_biorthogonal
    (fun n => (ultrafilterMatrixFunctional (𝕜 := 𝕜) U n).toLinearMap)
    (selectorPullbackOperator (𝕜 := 𝕜))
    (by
      intro n m
      by_cases hmn : m = n <;>
        simpa only [hmn, if_true, if_false] using
          ultrafilterMatrixFunctional_selectorPullback (𝕜 := 𝕜) U V h n m)
    (fun n : ℕ => (n : 𝕜))
  refine ⟨L, ?_, ?_, ?_⟩
  · intro hcont
    let small (n : ℕ) : OffDiagonal 𝕜 :=
      ((n + 1 : ℕ) : 𝕜)⁻¹ • selectorPullbackOperator (𝕜 := 𝕜) (n + 1)
    have hbound (n : ℕ) : ‖small n‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
      calc
        _ = ‖((n + 1 : ℕ) : 𝕜)⁻¹‖ * ‖selectorPullbackOperator (𝕜 := 𝕜) (n + 1)‖ :=
          norm_smul _ _
        _ ≤ ‖((n + 1 : ℕ) : 𝕜)⁻¹‖ * 1 := mul_le_mul_of_nonneg_left
          (selectorPullbackOperator_norm_le (𝕜 := 𝕜) (n + 1)) (norm_nonneg _)
        _ = ((n + 1 : ℕ) : ℝ)⁻¹ := by rw [mul_one, norm_inv, RCLike.norm_natCast]
    have hsmall : Tendsto small atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero (fun n => norm_nonneg (small n)) hbound
        (tendsto_inverse_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    have himage (n : ℕ) : L (small n) = 1 := by
      dsimp only [small]
      rw [map_smul, hvalues, smul_eq_mul]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    have hlim := (hcont.tendsto (0 : OffDiagonal 𝕜)).comp hsmall
    rw [map_zero] at hlim
    have heq : (0 : 𝕜) = 1 := tendsto_nhds_unique hlim (by
      simpa only [Function.comp_def, himage] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 1)))
    exact zero_ne_one heq
  · intro a T
    have hz := hzero ((multiplicationOperator a).comp T - ultrafilterEvaluation U a • T)
      (fun n => by
        change ultrafilterMatrixFunctional (𝕜 := 𝕜) U n
          ((multiplicationOperator a).comp T - ultrafilterEvaluation U a • T) = 0
        rw [map_sub, map_smul, ultrafilterMatrixFunctional_left, smul_eq_mul, sub_self])
    rw [map_sub, map_smul, smul_eq_mul] at hz
    exact sub_eq_zero.mp hz
  · intro b T
    have hz := hzero (T.comp (multiplicationOperator b) - ultrafilterEvaluation V b • T)
      (fun n => by
        change ultrafilterMatrixFunctional (𝕜 := 𝕜) U n
          (T.comp (multiplicationOperator b) - ultrafilterEvaluation V b • T) = 0
        rw [map_sub, map_smul, ultrafilterMatrixFunctional_right U V h, smul_eq_mul]
        exact sub_eq_zero.mpr (mul_comm _ _))
    rw [map_sub, map_smul, smul_eq_mul] at hz
    exact (sub_eq_zero.mp hz).trans (mul_comm _ _)

end Posets
