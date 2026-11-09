import SurveyStatements.P4Goldstine
import SurveyStatements.P4Bidual

/-! Gantmacher's criterion for the genuine weakly compact operator ideal,
proved from Goldstine and Banach--Alaoglu. -/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 1024
open Set Topology
namespace SurveyStatements.P4
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem IsWeaklyCompactOperator.bidual_mem_image {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator 𝕜 T) (ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    bidualMap T ξ ∈ bidualImage 𝕜 F := by
  obtain ⟨K, hK, hTK⟩ := (weaklyCompact_iff_compact_cover T).mp hT
  have hunit : ∀ η : StrongDual 𝕜 (StrongDual 𝕜 E), ‖η‖ ≤ 1 →
      bidualMap T η ∈ bidualImage 𝕜 F := by
    intro η hη
    have hc : IsClosed ((weakStarBidualMap T) ⁻¹'
        ((weakBidualInclusion (𝕜 := 𝕜) (F := F)) '' K)) :=
      (hK.image (weakBidualInclusion (𝕜 := 𝕜) (F := F)).continuous).isClosed.preimage
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
    (hT : ∀ ξ, bidualMap T ξ ∈ bidualImage 𝕜 F) : IsWeaklyCompactOperator 𝕜 T := by
  let B : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
  let C := (weakStarBidualMap T) '' B
  let J := weakBidualInclusion (𝕜 := 𝕜) (F := F)
  have hC : IsCompact C :=
    (WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1).image
      (weakStarBidualMap T).continuous
  have hCJ : C ⊆ range J := by
    rintro _ ⟨ξ, _, rfl⟩
    obtain ⟨y, hy⟩ := hT (WeakDual.toStrongDual ξ)
    refine ⟨toWeakSpace 𝕜 F y, ?_⟩
    exact congrArg StrongDual.toWeakDual hy
  have hK : IsCompact (J ⁻¹' C) := by
    apply (isEmbedding_weakBidualInclusion (𝕜 := 𝕜) (F := F)).isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset hCJ]
  apply (weaklyCompact_iff_compact_cover T).mpr
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
    IsWeaklyCompactOperator 𝕜 T ↔ ∀ ξ, bidualMap T ξ ∈ bidualImage 𝕜 F :=
  ⟨fun h => h.bidual_mem_image, weaklyCompact_of_bidual_mem_image T⟩

/-- Reflexivity as surjectivity of the normed bidual embedding is equivalent
to weak compactness of the closed unit ball. -/
theorem reflexive_iff_weaklyCompact_id :
    IsReflexiveNormedSpace 𝕜 E ↔
      IsWeaklyCompactOperator 𝕜 (ContinuousLinearMap.id 𝕜 E) := by
  rw [gantmacher_iff_bidual_mem_image]
  simp only [bidualMap_id, ContinuousLinearMap.id_apply]
  rfl

/-- The adjoint of a weakly compact operator is weakly compact. -/
theorem IsWeaklyCompactOperator.banachAdjoint {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator 𝕜 T) :
    IsWeaklyCompactOperator 𝕜 (banachAdjoint T) := by
  apply weaklyCompact_of_bidual_mem_image
  intro η
  let f : StrongDual 𝕜 F := η.comp (NormedSpace.inclusionInDoubleDual 𝕜 F)
  refine ⟨SurveyStatements.P4.banachAdjoint T f, ?_⟩
  apply ContinuousLinearMap.ext
  intro ξ
  obtain ⟨y, hy⟩ := hT.bidual_mem_image ξ
  change (bidualMap T ξ) f = η (bidualMap T ξ)
  rw [← hy]
  rfl

/-- The canonical bidual image of a complete space is norm closed. -/
theorem isClosed_bidualImage [CompleteSpace F] :
    IsClosed (bidualImage 𝕜 F : Set (StrongDual 𝕜 (StrongDual 𝕜 F))) := by
  have hJ : Topology.IsClosedEmbedding (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)) :=
    Isometry.isClosedEmbedding (α := F) (γ := StrongDual 𝕜 (StrongDual 𝕜 F))
      (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)).isometry
  exact hJ.isClosed_range

/-- The operator ideal of weakly compact maps is norm closed when the target
is complete. Its closure proof uses the actual bidual criterion. -/
theorem isClosed_setOf_isWeaklyCompactOperator [CompleteSpace F] :
    IsClosed {T : E →L[𝕜] F | IsWeaklyCompactOperator 𝕜 T} := by
  have heq : {T : E →L[𝕜] F | IsWeaklyCompactOperator 𝕜 T} =
      ⋂ ξ : StrongDual 𝕜 (StrongDual 𝕜 E), {T | bidualMap T ξ ∈ bidualImage 𝕜 F} := by
    ext T
    simpa only [Set.mem_iInter, Set.mem_setOf_eq] using gantmacher_iff_bidual_mem_image T
  rw [heq]
  apply isClosed_iInter
  intro ξ
  apply (isClosed_bidualImage (𝕜 := 𝕜) (F := F)).preimage
  exact (((ContinuousLinearMap.compL 𝕜 (StrongDual 𝕜 F) (StrongDual 𝕜 E) 𝕜) ξ).comp
    (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip).continuous

end SurveyStatements.P4

