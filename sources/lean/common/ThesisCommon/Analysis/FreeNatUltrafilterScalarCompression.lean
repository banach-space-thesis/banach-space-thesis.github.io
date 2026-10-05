import ThesisCommon.Analysis.InfinityQuotientContinuousFunctions
import ThesisCommon.Analysis.InfinityQuotientCountableCompression
import ThesisCommon.Analysis.FreeNatUltrafilterTensorDensity

/-! Countable scalar compression on the actual continuous-function space
C(ω*), transported through the proved quotient equivalence. -/
noncomputable section
open Set
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinityQuotientContinuous_mask (A : Set ℕ)
    (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientContinuousEquiv (𝕜 := 𝕜) (infinityQuotientMask (𝕜 := 𝕜) A x) =
      continuousFunctionMask (𝕜 := 𝕜) (FreeNatUltrafilter.basic A)
        (FreeNatUltrafilter.isClopen_basic A) (infinityQuotientContinuousEquiv (𝕜 := 𝕜) x) := by
  ext U
  simp only [infinityQuotientContinuousEquiv_apply, infinityQuotientEval_mask,
    continuousFunctionMask_apply, FreeNatUltrafilter.basic, Set.mem_setOf_eq]

theorem exists_freeNatUltrafilter_countable_scalar_compression
    (T : ℕ → C(FreeNatUltrafilter, 𝕜) →L[𝕜] C(FreeNatUltrafilter, 𝕜))
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ c : ℕ → 𝕜, ∀ n
      (f : C(FreeNatUltrafilter, 𝕜)),
      (∀ U, U ∉ FreeNatUltrafilter.basic B → f U = 0) →
      ∀ U ∈ FreeNatUltrafilter.basic B, T n f U = c n * f U := by
  let e := infinityQuotientContinuousEquiv (𝕜 := 𝕜)
  let S (n : ℕ) := e.symm.toContinuousLinearMap.comp ((T n).comp e.toContinuousLinearMap)
  obtain ⟨B, hB, hBA, c, hc⟩ := exists_infinityQuotient_countable_scalar_compression S hA
  refine ⟨B, hB, hBA, c, ?_⟩
  intro n f hf U hU
  let x := e.symm f
  have hx : infinityQuotientMask (𝕜 := 𝕜) B x = x := by
    apply e.injective
    rw [infinityQuotientContinuous_mask]
    change continuousFunctionMask (𝕜 := 𝕜) (FreeNatUltrafilter.basic B)
      (FreeNatUltrafilter.isClopen_basic B) (e x) = e x
    have hex : e x = f := e.apply_symm_apply f
    rw [hex]
    ext V
    simp only [continuousFunctionMask_apply]
    split_ifs with hV
    · rfl
    · exact (hf V hV).symm
  have h := congrArg (fun q => infinityQuotientEval (𝕜 := 𝕜) U q) (hc n x)
  rw [hx] at h
  change infinityQuotientEval (𝕜 := 𝕜) U (infinityQuotientMask (𝕜 := 𝕜) B (S n x)) =
    infinityQuotientEval (𝕜 := 𝕜) U (c n • x) at h
  rw [infinityQuotientEval_mask, if_pos (show B ∈ U from hU), map_smul] at h
  have hl : infinityQuotientEval (𝕜 := 𝕜) U (S n x) = T n f U := by
    change e (S n x) U = T n f U
    change e (e.symm (T n (e (e.symm f)))) U = T n f U
    rw [e.apply_symm_apply, e.apply_symm_apply]
  have hr : infinityQuotientEval (𝕜 := 𝕜) U x = f U := by
    change e (e.symm f) U = f U
    rw [e.apply_symm_apply]
  simpa only [hl, hr, smul_eq_mul] using h

end ThesisCommon
