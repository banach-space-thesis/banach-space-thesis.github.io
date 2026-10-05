import Posets.WolfePreservationBlockFunctions
import JLMS.AtomicDual

/-! An actual atomic kernel which is uniformly nearly diagonal is close
to multiplication by the continuous function A1. No continuity of its
individual diagonal atomic coefficients is assumed. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 L : Type*} [RCLike 𝕜] [TopologicalSpace L]

local instance wolfeNearDiagonalEstimatesDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfeNearDiagonalEstimatesDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

theorem wolfe_atomicRestriction_singleton_apply (M : JLMS.AtomicDualModel 𝕜 L)
    (φ : JLMS.CZero 𝕜 L →L[𝕜] 𝕜) (x : L) (f : JLMS.CZero 𝕜 L) :
    JLMS.atomicRestriction M {x} φ f = M.representation φ x * f x := by
  classical
  rw [← (JLMS.atomicDual_apply_hasSum M (JLMS.atomicRestriction M {x} φ) f).tsum_eq]
  rw [tsum_eq_single x]
  · simp [JLMS.atomicRestriction_coordinates, JLMS.restrictionL1_apply, JLMS.restrictL1_apply]
  · intro y hy
    simp [JLMS.atomicRestriction_coordinates, JLMS.restrictionL1_apply, JLMS.restrictL1_apply, hy]

theorem wolfe_nearDiagonal_apply_error (M : JLMS.AtomicDualModel 𝕜 L)
    (A : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L) {ε : ℝ}
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp A)‖ ≤ ε) (f : JLMS.CZero 𝕜 L) (x : L) :
    ‖A f x - wolfeAtomicCrossRow M A x x * f x‖ ≤ ε * ‖f‖ := by
  have he := DFunLike.congr_fun
    (JLMS.atomicRestriction_compl M {x} ((JLMS.evaluation x).comp A)) f
  rw [ContinuousLinearMap.sub_apply, wolfe_atomicRestriction_singleton_apply] at he
  change A f x - wolfeAtomicCrossRow M A x x * f x = _ at he
  rw [he]
  exact ((JLMS.atomicRestriction M {x}ᶜ ((JLMS.evaluation x).comp A)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hoff x) (norm_nonneg f))

variable [CompactSpace L]

def wolfeNearDiagonalTotal (A : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L) : JLMS.CZero 𝕜 L :=
  A (wolfeSourceBlock univ isClopen_univ)

theorem wolfeNearDiagonalTotal_sub_atom_le (M : JLMS.AtomicDualModel 𝕜 L)
    (A : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L) {ε : ℝ} (hε : 0 ≤ ε)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp A)‖ ≤ ε) (x : L) :
    ‖wolfeNearDiagonalTotal A x - wolfeAtomicCrossRow M A x x‖ ≤ ε := by
  have h := wolfe_nearDiagonal_apply_error M A hoff (wolfeSourceBlock univ isClopen_univ) x
  have hb := mul_le_mul_of_nonneg_left
    (wolfeSourceBlock_norm_le (𝕜 := 𝕜) (univ : Set L) isClopen_univ) hε
  simpa [wolfeNearDiagonalTotal] using h.trans (by simpa only [mul_one] using hb)

theorem wolfeNearDiagonalTotal_norm_lower (M : JLMS.AtomicDualModel 𝕜 L)
    (A : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L) {d ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M A x x‖)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp A)‖ ≤ ε) (x : L) :
    d - ε ≤ ‖wolfeNearDiagonalTotal A x‖ := by
  have he := wolfeNearDiagonalTotal_sub_atom_le M A hε hoff x
  have hn := norm_sub_norm_le (wolfeAtomicCrossRow M A x x) (wolfeNearDiagonalTotal A x)
  rw [norm_sub_rev] at hn
  linarith [hdiag x]

theorem wolfe_nearDiagonal_multiplier_error (M : JLMS.AtomicDualModel 𝕜 L)
    (A : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L) {ε : ℝ} (hε : 0 ≤ ε)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp A)‖ ≤ ε) :
    ‖A - ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 L) (wolfeNearDiagonalTotal A)‖ ≤ 2 * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖A f x - wolfeNearDiagonalTotal A x * f x‖ ≤ _
  have he : A f x - wolfeNearDiagonalTotal A x * f x =
      (A f x - wolfeAtomicCrossRow M A x x * f x) +
        (wolfeAtomicCrossRow M A x x - wolfeNearDiagonalTotal A x) * f x := by ring
  rw [he]
  have ht := norm_add_le (A f x - wolfeAtomicCrossRow M A x x * f x)
    ((wolfeAtomicCrossRow M A x x - wolfeNearDiagonalTotal A x) * f x)
  have hfirst := wolfe_nearDiagonal_apply_error M A hoff f x
  have hsecond := wolfeNearDiagonalTotal_sub_atom_le M A hε hoff x
  rw [norm_sub_rev] at hsecond
  have hm := mul_le_mul hsecond (JLMS.norm_CZero_apply_le f x) (norm_nonneg _) hε
  rw [← norm_mul] at hm
  linarith

end Posets
