import Posets.MatrixExtraction
import Posets.MatrixNorm
import Posets.SeparableBlocks
import PosetsCommon.CZeroSumFinite

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type*} [PartialOrder P]
  {X : P → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  (hZ : ¬ TopologicalSpace.SeparableSpace Z) (j : ∀ p, Z →ₗᵢ[𝕜] X p)
  (hj : ∀ s t, s ≤ t → ∀ z, ι s t (j s z) = j t z)

include hZ j hj in
/-- Finite row estimate from the paper's common nonseparable subspace. -/
theorem blockScalarMatrix_finite_row_bound
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (s : P) (F : Finset P) :
    ∑ t ∈ F, ‖blockScalarMatrix h T s t‖ ≤ ‖T‖ := by
  let a : ℝ := ∑ t ∈ F, ‖blockScalarMatrix h T s t‖
  let c : P → 𝕜 := fun t => normingPhase (blockScalarMatrix h T s t)
  let U : Z →L[𝕜] X s := ∑ t ∈ F, c t •
    (operatorBlock 𝕜 X X T s t).comp (j t).toContinuousLinearMap
  let R : Z →L[𝕜] X s := ∑ t ∈ F, c t •
    (operatorBlock 𝕜 X X T s t - blockScalarMatrix h T s t • ι t s).comp
      (j t).toContinuousLinearMap
  have hR : HasSeparableRange 𝕜 Z (X s) R :=
    hasSeparableRange_sum F _ (fun t _ =>
      ((blockScalarMatrix_remainder h T s t).comp_right (j t).toContinuousLinearMap).smul (c t))
  have hterm (t : P) : (operatorBlock 𝕜 X X T s t).comp (j t).toContinuousLinearMap =
      blockScalarMatrix h T s t • (j s).toContinuousLinearMap +
      (operatorBlock 𝕜 X X T s t - blockScalarMatrix h T s t • ι t s).comp
        (j t).toContinuousLinearMap := by
    ext z
    by_cases hts : t ≤ s
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        LinearIsometry.coe_toContinuousLinearMap, hj t s hts]
      abel
    · simp [blockScalarMatrix_zero_off_order h T hts]
  have hc : ∀ t, c t * blockScalarMatrix h T s t = (‖blockScalarMatrix h T s t‖ : 𝕜) :=
    fun t => by rw [mul_comm]; exact mul_normingPhase _
  have hU : U = (a : 𝕜) • (j s).toContinuousLinearMap + R := by
    change (∑ t ∈ F, c t • _) = _
    simp_rw [hterm, smul_add, smul_smul]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    simp [hc, a, R]
  have hUnorm : ‖U‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro z
    have heq : U z = sumProjection 𝕜 X s
        (T (finiteLift F c (fun t => (j t).toContinuousLinearMap) z)) := by
      simp [U, finiteLift, operatorBlock, map_sum, map_smul]
    rw [heq]
    exact (sumProjection_norm_le _ s).trans ((T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left
        (finiteLift_bound F c j (fun t _ => norm_normingPhase_le _) z) (norm_nonneg T)))
  have hscalar := scalar_norm_le_between hZ (j s).toContinuousLinearMap (j s).isometry hR hU
  have ha : 0 ≤ a := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs : a ≤ ‖U‖ := by simpa only [RCLike.norm_ofReal, abs_of_nonneg ha] using hscalar
  exact hs.trans hUnorm

theorem blockScalarMatrix_boundedRows (hcommon : CommonSubspace 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    BoundedRowsOn 𝕜 (blockScalarMatrix h T) ∧
      ∀ s, (∑' t, ‖blockScalarMatrix h T s t‖) ≤ ‖T‖ := by
  obtain ⟨Z, _, _, hZ, j, hj⟩ := hcommon
  have hfinite := blockScalarMatrix_finite_row_bound h hZ j hj T
  have hs : ∀ s, Summable (fun t => ‖blockScalarMatrix h T s t‖) :=
    fun s => summable_of_sum_le (fun _ => norm_nonneg _) (hfinite s)
  have hbound : ∀ s, (∑' t, ‖blockScalarMatrix h T s t‖) ≤ ‖T‖ :=
    fun s => (hs s).tsum_le_of_sum_le (hfinite s)
  exact ⟨⟨hs, ‖T‖, hbound⟩, hbound⟩

end Posets
