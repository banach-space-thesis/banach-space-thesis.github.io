import JLMS.CZeroSumCoordinateAbsorption

/-! Uniform bounds when a single coordinate absorbs the head summand. -/
noncomputable section
namespace Posets
universe u v
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type u} (E : I → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

local instance omegaBlockNormsSumGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance omegaBlockNormsSumSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalOmegaBlock_absorbsAt_norm_le (i : I) (e : (F × E i) ≃L[𝕜] E i)
    {C : ℝ} (hC : 1 ≤ C) (he : ∀ x, ‖e x‖ ≤ C * ‖x‖)
    (x : F × JLMS.CZeroSum 𝕜 E) :
    ‖JLMS.cZeroSumAbsorbsAt E i e x‖ ≤ C * ‖x‖ := by
  let d := JLMS.cZeroSumCoordinateHeadIsometry (𝕜 := 𝕜) E i
  have hd1 : ‖(d x.2).1‖ ≤ ‖x.2‖ := by
    simpa only [d.norm_map] using norm_fst_le (d x.2)
  have hd2 : ‖(d x.2).2‖ ≤ ‖x.2‖ := by
    simpa only [d.norm_map] using norm_snd_le (d x.2)
  have hp : ‖(x.1, (d x.2).1)‖ ≤ ‖x‖ := by
    rw [Prod.norm_def]
    exact max_le (norm_fst_le x) (hd1.trans (norm_snd_le x))
  change ‖d.symm (e (x.1, (d x.2).1), (d x.2).2)‖ ≤ _
  rw [d.symm.norm_map, Prod.norm_def]
  exact max_le ((he _).trans (mul_le_mul_of_nonneg_left hp (zero_le_one.trans hC)))
    ((hd2.trans (norm_snd_le x)).trans (le_mul_of_one_le_left (norm_nonneg _) hC))

theorem ordinalOmegaBlock_absorbsAt_symm_norm_le (i : I) (e : (F × E i) ≃L[𝕜] E i)
    {C : ℝ} (hC : 1 ≤ C) (he : ∀ x, ‖e.symm x‖ ≤ C * ‖x‖)
    (x : JLMS.CZeroSum 𝕜 E) :
    ‖(JLMS.cZeroSumAbsorbsAt E i e).symm x‖ ≤ C * ‖x‖ := by
  let d := JLMS.cZeroSumCoordinateHeadIsometry (𝕜 := 𝕜) E i
  have hd1 : ‖(d x).1‖ ≤ ‖x‖ := by
    simpa only [d.norm_map] using norm_fst_le (d x)
  have hd2 : ‖(d x).2‖ ≤ ‖x‖ := by
    simpa only [d.norm_map] using norm_snd_le (d x)
  have hp : ‖e.symm (d x).1‖ ≤ C * ‖x‖ :=
    (he _).trans (mul_le_mul_of_nonneg_left hd1 (zero_le_one.trans hC))
  change ‖((e.symm (d x).1).1, d.symm ((e.symm (d x).1).2, (d x).2))‖ ≤ _
  rw [Prod.norm_def, d.symm.norm_map, Prod.norm_def]
  exact max_le ((norm_fst_le (e.symm (d x).1)).trans hp)
    (max_le ((norm_snd_le (e.symm (d x).1)).trans hp)
      (hd2.trans (le_mul_of_one_le_left (norm_nonneg _) hC)))

end Posets
