import ThesisCommon.Analysis.WeakCompactClosed
import ThesisCommon.Analysis.ClosedSubmoduleDual

/-! Gantmacher duality for Banach adjoints. The reverse implication uses
completeness only in the original range space. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem IsWeaklyCompactOperator.banachAdjoint {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) : IsWeaklyCompactOperator (banachAdjoint T) := by
  apply weaklyCompact_of_bidual_mem_image
  intro η
  let f : StrongDual 𝕜 F := η.comp (NormedSpace.inclusionInDoubleDual 𝕜 F)
  refine ⟨ThesisCommon.banachAdjoint T f, ?_⟩
  apply ContinuousLinearMap.ext
  intro ξ
  obtain ⟨y, hy⟩ := hT.bidual_mem_image ξ
  change (bidualMap T ξ) f = η (bidualMap T ξ)
  rw [← hy]
  rfl

theorem weaklyCompact_of_banachAdjoint [CompleteSpace F] {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator (banachAdjoint T)) : IsWeaklyCompactOperator T := by
  apply weaklyCompact_of_bidual_mem_image
  intro ξ
  apply (mem_closedSubmodule_iff_dual (𝕜 := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 F)) (bidualImage 𝕜 F)
    (isClosed_bidualImage (𝕜 := 𝕜) (F := F)) _).mpr
  intro η hη
  obtain ⟨f, hf⟩ := hT.bidual_mem_image η
  have hfzero : f = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have he := congrArg (fun ζ : StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) =>
      ζ (NormedSpace.inclusionInDoubleDual 𝕜 E x)) hf
    change f x = η (NormedSpace.inclusionInDoubleDual 𝕜 F (T x)) at he
    exact he.trans (hη _ ⟨T x, rfl⟩)
  have he := congrArg (fun ζ : StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) => ζ ξ) hf
  change ξ f = η (bidualMap T ξ) at he
  simpa only [hfzero, map_zero] using he.symm

theorem weaklyCompact_banachAdjoint_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    IsWeaklyCompactOperator (banachAdjoint T) ↔ IsWeaklyCompactOperator T :=
  ⟨weaklyCompact_of_banachAdjoint, IsWeaklyCompactOperator.banachAdjoint⟩

end ThesisCommon
