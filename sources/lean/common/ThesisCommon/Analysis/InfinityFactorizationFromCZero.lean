import ThesisCommon.Analysis.CZeroBidualInfinityExtension
import ThesisCommon.Analysis.InfinityRetractionOfCZeroExtension
import ThesisCommon.Analysis.ExtremallyDisconnectedCKRetraction

/-! Sharp ℓ∞ identity factorizations from a fixed c₀ copy when the input
is contractively retracted from its bidual. The extension and infinite
support are actual constructions, including for extremally disconnected
C(K), whose retraction is itself constructed. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance infinityFactorBidualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance infinityFactorBidualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem exists_infinity_factorization_of_cZero_bidual_retraction
    (P : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] E) (hP : ‖P‖ ≤ 1)
    (hPJ : ∀ x, P (NormedSpace.inclusionInDoubleDual 𝕜 E x) = x)
    (T : E →L[𝕜] F) (V : CZeroSum 𝕜 →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖T (V x)‖) :
    ∃ U : F →L[𝕜] EllInfinitySum 𝕜, ∃ W : EllInfinitySum 𝕜 →L[𝕜] E,
      U.comp (T.comp W) = ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜) ∧
      ‖U‖ ≤ 1/c ∧ ‖W‖ ≤ ‖V‖ := by
  obtain ⟨W, hW, hext⟩ := exists_infinity_extension_of_bidual_retraction P hP hPJ V
  obtain ⟨U, A, heq, hU, hA⟩ := exists_infinity_retraction_of_cZero_extension
    (T.comp V) (T.comp W) hc hlower (fun n => by
      change T (W (lp.single ∞ n 1)) = T (V (cZeroSingle n 1))
      rw [hext])
  refine ⟨U, W.comp A, ?_, hU, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using heq
  · exact (W.opNorm_comp_le A).trans
      ((mul_le_mul hW hA (norm_nonneg A) (norm_nonneg V)).trans_eq (mul_one ‖V‖))

end ThesisCommon

namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
variable {K F : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable [ExtremallyDisconnected K] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_infinity_factorization_of_cZero_extremallyDisconnected
    (T : C(K, 𝕜) →L[𝕜] F) (V : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜))
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖T (V x)‖) :
    ∃ U : F →L[𝕜] EllInfinitySum 𝕜, ∃ W : EllInfinitySum 𝕜 →L[𝕜] C(K, 𝕜),
      U.comp (T.comp W) = ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜) ∧
      ‖U‖ ≤ 1/c ∧ ‖W‖ ≤ ‖V‖ := by
  obtain ⟨P, hP, hPJ⟩ := exists_continuousMap_bidual_retraction (𝕜 := 𝕜) (K := K)
  exact exists_infinity_factorization_of_cZero_bidual_retraction P hP hPJ T V hc hlower

end ThesisCommon
