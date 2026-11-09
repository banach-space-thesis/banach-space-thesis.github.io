import SurveyStatements.P4DFJPGauge
import SurveyStatements.P4Gantmacher
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Weak-star compact covers of the DFJP neighborhoods

The small norm-ball remainder is moved into the bidual, where its weak-star
compactness is supplied by Banach--Alaoglu. This is the first step toward the
reflexivity argument, rather than an assumption of weak compactness.
-/

noncomputable section

set_option autoImplicit false

open Set Metric Topology
open scoped Pointwise

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The genuine weak-star compact padded cover in the bidual. -/
def weakStarPadded (K : Set E) (a b : ℝ) : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
  (a : 𝕜) • ((weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' K) +
    (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) b)

lemma isCompact_weakStarPadded {K : Set E}
    (hK : IsCompact ((toWeakSpace 𝕜 E) '' K)) (a b : ℝ) :
    IsCompact (weakStarPadded (𝕜 := 𝕜) K a b) := by
  have himage : (weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' K =
      weakBidualInclusion '' ((toWeakSpace 𝕜 E) '' K) := by
    rw [image_image]
    rfl
  have hleft : IsCompact ((weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' K) := by
    rw [himage]
    exact hK.image weakBidualInclusion.continuous
  exact (hleft.smul (a : 𝕜)).add
    (WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) b)

lemma image_paddedNeighborhood_subset_weakStarPadded {K : Set E} (a : ℝ)
    {b : ℝ} (hb : 0 ≤ b) :
    (weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' paddedNeighborhood K a b ⊆
      weakStarPadded (𝕜 := 𝕜) K a b := by
  rintro _ ⟨x, ⟨y, ⟨k, hk, rfl⟩, z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
  rw [map_add]
  refine add_mem_add ?_ ?_
  · refine ⟨weakStarBidualInclusion k, ⟨k, hk, rfl⟩, ?_⟩
    change (a : 𝕜) • weakStarBidualInclusion k = weakStarBidualInclusion (a • k)
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact ((weakStarBidualInclusion (𝕜 := 𝕜) (E := E)).map_smul (a : 𝕜) k).symm
  · change NormedSpace.inclusionInDoubleDual 𝕜 E (b • w) ∈ closedBall 0 b
    rw [mem_closedBall, dist_zero_right
      (NormedSpace.inclusionInDoubleDual 𝕜 E (b • w))]
    change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (b • w)‖ ≤ b
    rw [(NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).norm_map,
      norm_smul, Real.norm_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hw) hb).trans_eq
      (mul_one b)

lemma image_closure_paddedNeighborhood_subset_weakStarPadded {K : Set E}
    (hK : IsCompact ((toWeakSpace 𝕜 E) '' K)) (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    (weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' closure (paddedNeighborhood K a b) ⊆
      weakStarPadded (𝕜 := 𝕜) K a b :=
  (image_closure_subset_closure_image weakStarBidualInclusion.continuous).trans
    (closure_minimal (image_paddedNeighborhood_subset_weakStarPadded a hb)
      (isCompact_weakStarPadded hK a b).isClosed)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Goldstine moves a compact padded cover of the original unit-ball image
to a cover of the entire bidual unit-ball image. -/
lemma bidual_unitBall_mem_weakStarPadded (T : F →L[𝕜] E) {K : Set E}
    (hK : IsCompact ((toWeakSpace 𝕜 E) '' K)) (a : ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hT : ∀ x : F, ‖x‖ ≤ 1 → T x ∈ closure (paddedNeighborhood K a b))
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 F)) (hξ : ‖ξ‖ ≤ 1) :
    StrongDual.toWeakDual (bidualMap T ξ) ∈ weakStarPadded (𝕜 := 𝕜) K a b := by
  have hclosed : IsClosed ((weakStarBidualMap T) ⁻¹'
      weakStarPadded (𝕜 := 𝕜) K a b) :=
    (isCompact_weakStarPadded hK a b).isClosed.preimage (weakStarBidualMap T).continuous
  have hsub : (weakStarBidualInclusion (𝕜 := 𝕜) (E := F)) '' closedBall 0 1 ⊆
      (weakStarBidualMap T) ⁻¹' weakStarPadded (𝕜 := 𝕜) K a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact image_closure_paddedNeighborhood_subset_weakStarPadded hK a hb
      ⟨T x, hT x (by simpa using hx), rfl⟩
  exact closure_minimal hsub hclosed (goldstine_unitBall ξ hξ)

/-- Arbitrarily small norm-ball errors around weakly compact sets force
the bidual image back into the canonical image of a complete ambient space. -/
lemma bidual_unitBall_mem_image_of_smallRemainders [CompleteSpace E]
    (T : F →L[𝕜] E)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ K : Set E, ∃ a : ℝ,
      IsCompact ((toWeakSpace 𝕜 E) '' K) ∧
      ∀ x : F, ‖x‖ ≤ 1 → T x ∈ closure (paddedNeighborhood K a ε))
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 F)) (hξ : ‖ξ‖ ≤ 1) :
    bidualMap T ξ ∈ bidualImage 𝕜 E := by
  apply (isClosed_bidualImage (𝕜 := 𝕜) (F := E)).closure_subset
  apply (Metric.mem_closure_iff (s := (bidualImage 𝕜 E : Set
    (StrongDual 𝕜 (StrongDual 𝕜 E)))) (a := bidualMap T ξ)).mpr
  intro ε hε
  obtain ⟨K, a, hK, hTx⟩ := hT (ε / 2) (by positivity)
  obtain ⟨y, ⟨z, ⟨k, hk, rfl⟩, rfl⟩, w, hw, hyw⟩ :=
    bidual_unitBall_mem_weakStarPadded T hK a (by positivity) hTx ξ hξ
  let k' : E := (a : 𝕜) • k
  refine ⟨NormedSpace.inclusionInDoubleDual 𝕜 E k', ?_, ?_⟩
  · exact ⟨k', rfl⟩
  have heq : NormedSpace.inclusionInDoubleDual 𝕜 E k' + WeakDual.toStrongDual w =
      bidualMap T ξ := by
    change (NormedSpace.inclusionInDoubleDual 𝕜 E) ((a : 𝕜) • k) +
      WeakDual.toStrongDual w = bidualMap T ξ
    rw [map_smul]
    exact hyw
  have hw' : ‖WeakDual.toStrongDual w‖ ≤ ε / 2 := by
    exact (mem_closedBall_zero_iff (a := WeakDual.toStrongDual w)).mp hw
  have hd : dist (bidualMap T ξ) (NormedSpace.inclusionInDoubleDual 𝕜 E k') =
      ‖WeakDual.toStrongDual w‖ := by
    rw [dist_eq_norm (bidualMap T ξ) (NormedSpace.inclusionInDoubleDual 𝕜 E k'), ← heq]
    exact congrArg norm (add_sub_cancel_left
      (NormedSpace.inclusionInDoubleDual 𝕜 E k') (WeakDual.toStrongDual w))
  rw [hd]
  exact hw'.trans_lt (by linarith)

end SurveyStatements.P4
