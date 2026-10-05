import ThesisCommon.Analysis.Goldstine
import ThesisCommon.Analysis.BidualWeakTopology

/-! Gantmacher's criterion for the genuine weakly compact operator ideal,
proved from Goldstine and Banach--Alaoglu. -/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 1024
open Set Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem IsWeaklyCompactOperator.bidual_mem_image {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) (ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    bidualMap T ξ ∈ bidualImage 𝕜 F := by
  obtain ⟨K, hK, hTK⟩ := hT
  have hunit : ∀ η : StrongDual 𝕜 (StrongDual 𝕜 E), ‖η‖ ≤ 1 →
      bidualMap T η ∈ bidualImage 𝕜 F := by
    intro η hη
    have hc : IsClosed ((weakStarBidualMap T) ⁻¹'
        ((weakBidualInclusion (𝕜 := 𝕜) (E := F)) '' K)) :=
      (hK.image (weakBidualInclusion (𝕜 := 𝕜) (E := F)).continuous).isClosed.preimage
        (weakStarBidualMap T).continuous
    have hsub : (weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' Metric.closedBall 0 1 ⊆
        (weakStarBidualMap T) ⁻¹' (weakBidualInclusion '' K) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨toWeakSpace 𝕜 F (T x), hTK x (by simpa using hx), rfl⟩
    obtain ⟨y, _, hy⟩ := closure_minimal hsub hc (goldstine_unitBall η hη)
    refine ⟨(toWeakSpace 𝕜 F).symm y, ?_⟩
    exact StrongDual.toWeakDual.injective hy
  let r : ℝ := ‖ξ‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a : 𝕜 := r
  have ha : a ≠ 0 := by simpa [a] using hr.ne'
  have hna : ‖a‖ = r := by simp [a, abs_of_pos hr]
  letI : NormSMulClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    NormedSpace.toNormSMulClass (𝕜 := 𝕜) (E := StrongDual 𝕜 (StrongDual 𝕜 E))
  have hη : ‖a⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hna, ← div_eq_inv_mul]
    apply (div_le_one hr).mpr
    dsimp [r]
    linarith
  have hm := (bidualImage 𝕜 F).smul_mem a (hunit (a⁻¹ • ξ) hη)
  simpa only [map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul] using hm

theorem weaklyCompact_of_bidual_mem_image (T : E →L[𝕜] F)
    (hT : ∀ ξ, bidualMap T ξ ∈ bidualImage 𝕜 F) : IsWeaklyCompactOperator T := by
  let B : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
  let C := (weakStarBidualMap T) '' B
  let J := weakBidualInclusion (𝕜 := 𝕜) (E := F)
  have hC : IsCompact C :=
    (WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1).image
      (weakStarBidualMap T).continuous
  have hCJ : C ⊆ range J := by
    rintro _ ⟨ξ, _, rfl⟩
    obtain ⟨y, hy⟩ := hT (WeakDual.toStrongDual ξ)
    refine ⟨toWeakSpace 𝕜 F y, ?_⟩
    exact congrArg StrongDual.toWeakDual hy
  have hK : IsCompact (J ⁻¹' C) := by
    apply (isEmbedding_weakBidualInclusion (𝕜 := 𝕜) (E := F)).isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset hCJ]
  refine ⟨J ⁻¹' C, hK, ?_⟩
  intro x hx
  refine ⟨weakBidualInclusion (toWeakSpace 𝕜 E x), ?_, rfl⟩
  change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 x - 0‖ ≤ 1
  have hz : NormedSpace.inclusionInDoubleDualLi 𝕜 x - 0 =
      NormedSpace.inclusionInDoubleDualLi 𝕜 x := by
    ext f
    simp
  rw [hz, (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).norm_map]
  exact hx

theorem gantmacher_iff_bidual_mem_image (T : E →L[𝕜] F) :
    IsWeaklyCompactOperator T ↔ ∀ ξ, bidualMap T ξ ∈ bidualImage 𝕜 F :=
  ⟨fun h => h.bidual_mem_image, weaklyCompact_of_bidual_mem_image T⟩

end ThesisCommon
