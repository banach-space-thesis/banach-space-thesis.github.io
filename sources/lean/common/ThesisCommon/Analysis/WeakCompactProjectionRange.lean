import ThesisCommon.Analysis.Gantmacher
import ThesisCommon.Analysis.BanachAdjointAlgebra

/-! A weakly compact projection has a reflexive range. Reflexivity here is
the actual surjectivity of the canonical isometric embedding into the
continuous bidual, including the zero range. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem weaklyCompact_split_projection_canonical_surjective
    (J : Y →L[𝕜] X) (R : X →L[𝕜] Y)
    (hRJ : R.comp J = ContinuousLinearMap.id 𝕜 Y)
    (hW : IsWeaklyCompactOperator (J.comp R)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 Y) := by
  intro ξ
  have hI : (J.comp R).comp J = J := by
    rw [ContinuousLinearMap.comp_assoc, hRJ, ContinuousLinearMap.comp_id]
  obtain ⟨x, hx⟩ := hW.bidual_mem_image (bidualMap J ξ)
  have hfix : bidualMap (J.comp R) (bidualMap J ξ) = bidualMap J ξ := by
    rw [← ContinuousLinearMap.comp_apply, ← bidualMap_comp, hI]
  rw [hfix] at hx
  refine ⟨R x, ?_⟩
  have he := congrArg (bidualMap R) hx
  change NormedSpace.inclusionInDoubleDual 𝕜 Y (R x) =
    bidualMap R (bidualMap J ξ) at he
  rw [← ContinuousLinearMap.comp_apply (bidualMap R) (bidualMap J) ξ,
    ← bidualMap_comp, hRJ] at he
  exact he

theorem weaklyCompact_projection_range_canonical_surjective
    (P : X →L[𝕜] X) (hP : P.comp P = P) (hW : IsWeaklyCompactOperator P) :
    Function.Surjective
      (NormedSpace.inclusionInDoubleDual 𝕜 (LinearMap.range P.toLinearMap)) := by
  let J := (LinearMap.range P.toLinearMap).subtypeL
  let R := P.rangeRestrict
  have hRJ : R.comp J = ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) := by
    ext x
    obtain ⟨y, hy⟩ := x.property
    change P y = x.val at hy
    change P x.val = x.val
    rw [← hy]
    exact DFunLike.congr_fun hP y
  exact weaklyCompact_split_projection_canonical_surjective J R hRJ hW

/-- A bounded operator through a space with surjective canonical bidual
embedding is weakly compact. No splitting hypothesis is needed here. -/
theorem weaklyCompact_of_reflexive_factorization
    (J : Y →L[𝕜] X) (R : X →L[𝕜] Y)
    (hY : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 Y)) :
    IsWeaklyCompactOperator (J.comp R) := by
  apply weaklyCompact_of_bidual_mem_image
  intro ξ
  obtain ⟨y, hy⟩ := hY (bidualMap R ξ)
  refine ⟨J y, ?_⟩
  rw [bidualMap_comp, ContinuousLinearMap.comp_apply, ← hy]
  rfl

theorem weaklyCompact_projection_iff_range_canonical_surjective
    (P : X →L[𝕜] X) (hP : P.comp P = P) :
    IsWeaklyCompactOperator P ↔ Function.Surjective
      (NormedSpace.inclusionInDoubleDual 𝕜 (LinearMap.range P.toLinearMap)) := by
  refine ⟨weaklyCompact_projection_range_canonical_surjective P hP, fun h => ?_⟩
  exact weaklyCompact_of_reflexive_factorization
    (LinearMap.range P.toLinearMap).subtypeL P.rangeRestrict h

end ThesisCommon
