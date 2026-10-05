import ThesisCommon.Analysis.CZeroDualEllOne
import ThesisCommon.Analysis.InfinityWeakStarPairing
import ThesisCommon.Analysis.BanachAdjointAlgebra

/-! The canonical embedding of ℓ∞ into c₀**, built from the genuine ℓ₁
coefficient representation of c₀ functionals, and norm-preserving extension
of c₀ operators into a contractively retracted bidual. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

local instance cZeroInfinityBidualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 (CZeroSum 𝕜))) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 (CZeroSum 𝕜))
    (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)
local instance cZeroInfinityBidualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (CZeroSum 𝕜))) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 (CZeroSum 𝕜))
    (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

def infinityToCZeroBidual : EllInfinitySum 𝕜 →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (CZeroSum 𝕜)) :=
  (banachAdjoint (cZeroDualToEllOne (𝕜 := 𝕜))).comp
    infinityWeakStarDualIsometry.toContinuousLinearMap

theorem norm_infinityToCZeroBidual_le : ‖infinityToCZeroBidual (𝕜 := 𝕜)‖ ≤ 1 := by
  let S := banachAdjoint (cZeroDualToEllOne (𝕜 := 𝕜))
  let I := (infinityWeakStarDualIsometry (𝕜 := 𝕜) (Γ := ℕ)).toContinuousLinearMap
  have hS : ‖S‖ ≤ 1 := by
    dsimp [S]
    rw [norm_banachAdjoint]
    exact norm_cZeroDualToEllOne_le
  have hI : ‖I‖ ≤ 1 :=
    (infinityWeakStarDualIsometry (𝕜 := 𝕜) (Γ := ℕ)).norm_toContinuousLinearMap_le
  exact (S.opNorm_comp_le I).trans
    ((mul_le_mul hS hI (norm_nonneg I) zero_le_one).trans_eq (one_mul 1))

theorem infinityToCZeroBidual_single (n : ℕ) :
    infinityToCZeroBidual (𝕜 := 𝕜) (lp.single ∞ n (1 : 𝕜)) =
      NormedSpace.inclusionInDoubleDual 𝕜 (CZeroSum 𝕜) (cZeroSingle n 1) := by
  classical
  apply ContinuousLinearMap.ext
  intro φ
  change infinityWeakStarPair (lp.single ∞ n (1 : 𝕜)) (cZeroDualToEllOne (𝕜 := 𝕜) φ) = φ (cZeroSingle n 1)
  rw [infinityWeakStarPair_apply, tsum_eq_single n]
  · simp
  · intro i hi
    rw [lp.single_apply_ne ∞ n 1 hi, mul_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance operatorInfinityBidualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance operatorInfinityBidualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

def cZeroOperatorBidualExtension (V : CZeroSum 𝕜 →L[𝕜] E) :
    EllInfinitySum 𝕜 →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  (bidualMap V).comp infinityToCZeroBidual

theorem norm_cZeroOperatorBidualExtension_le (V : CZeroSum 𝕜 →L[𝕜] E) :
    ‖cZeroOperatorBidualExtension V‖ ≤ ‖V‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [norm_bidualMap]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left norm_infinityToCZeroBidual_le (norm_nonneg V)

theorem cZeroOperatorBidualExtension_single (V : CZeroSum 𝕜 →L[𝕜] E) (n : ℕ) :
    cZeroOperatorBidualExtension V (lp.single ∞ n 1) =
      NormedSpace.inclusionInDoubleDual 𝕜 E (V (cZeroSingle n 1)) := by
  change bidualMap V (infinityToCZeroBidual (𝕜 := 𝕜) (lp.single ∞ n 1)) = _
  rw [infinityToCZeroBidual_single]
  apply ContinuousLinearMap.ext
  intro φ
  rfl

theorem exists_infinity_extension_of_bidual_retraction
    (P : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] E) (hP : ‖P‖ ≤ 1)
    (hPJ : ∀ x, P (NormedSpace.inclusionInDoubleDual 𝕜 E x) = x)
    (V : CZeroSum 𝕜 →L[𝕜] E) :
    ∃ W : EllInfinitySum 𝕜 →L[𝕜] E, ‖W‖ ≤ ‖V‖ ∧
      ∀ n, W (lp.single ∞ n 1) = V (cZeroSingle n 1) := by
  refine ⟨P.comp (cZeroOperatorBidualExtension V), ?_, ?_⟩
  · exact (P.opNorm_comp_le _).trans
      ((mul_le_mul hP (norm_cZeroOperatorBidualExtension_le V)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul ‖V‖))
  · intro n
    rw [ContinuousLinearMap.comp_apply, cZeroOperatorBidualExtension_single, hPJ]

end ThesisCommon

