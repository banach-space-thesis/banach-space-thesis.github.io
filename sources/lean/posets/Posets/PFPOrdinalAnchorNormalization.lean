import Posets.OrdinalAnchoredBlockReadback
import JLMS.OrdinalSpaceRetractionBounded
import ThesisCommon.Analysis.Factorization

/-! Actual ceiling-projection normalization for transfinite block selection.
The anchored reader kills the projection, so both normalized branches have
exactly the same compression as the original complementary operators. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000

variable (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β))
  (hg : StrictMono g)
  (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)

def pfpOrdinalAnchorProjection : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β :=
  (JLMS.ordinalSpaceCeilingExtension g hg htop).comp (JLMS.ordinalSpaceRestriction g)

@[simp] theorem pfpOrdinalAnchorProjection_apply (f : JLMS.OrdinalC 𝕜 β)
    (x : JLMS.OrdinalInterval β) :
    pfpOrdinalAnchorProjection g hg htop f x = f (g (JLMS.ordinalEmbeddingCeiling g x)) := rfl

theorem norm_pfpOrdinalAnchorProjection_le :
    ‖pfpOrdinalAnchorProjection (𝕜 := 𝕜) g hg htop‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact f.norm_coe_le_norm _

theorem pfpOrdinalAnchorProjection_idempotent :
    (pfpOrdinalAnchorProjection (𝕜 := 𝕜) g hg htop).comp
      (pfpOrdinalAnchorProjection g hg htop) = pfpOrdinalAnchorProjection g hg htop := by
  apply ContinuousLinearMap.ext
  intro f
  ext x
  simp only [ContinuousLinearMap.comp_apply, pfpOrdinalAnchorProjection_apply,
    JLMS.ordinalEmbeddingCeiling_apply_image g hg htop]

def pfpOrdinalAnchorNormalize
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β :=
  (ContinuousLinearMap.id 𝕜 _ - pfpOrdinalAnchorProjection g hg htop).comp T

@[simp] theorem pfpOrdinalAnchorNormalize_apply
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (f : JLMS.OrdinalC 𝕜 β) (x : JLMS.OrdinalInterval β) :
    pfpOrdinalAnchorNormalize g hg htop T f x =
      T f x - T f (g (JLMS.ordinalEmbeddingCeiling g x)) := rfl

theorem norm_pfpOrdinalAnchorNormalize_le
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    ‖pfpOrdinalAnchorNormalize g hg htop T‖ ≤ 2 * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  rw [pfpOrdinalAnchorNormalize_apply]
  calc
    _ ≤ ‖T f x‖ + ‖T f (g (JLMS.ordinalEmbeddingCeiling g x))‖ := norm_sub_le _ _
    _ ≤ ‖T f‖ + ‖T f‖ := add_le_add ((T f).norm_coe_le_norm _) ((T f).norm_coe_le_norm _)
    _ ≤ (2 * ‖T‖) * ‖f‖ := by nlinarith [T.le_opNorm f]

theorem pfpOrdinalAnchorNormalize_boundary_zero
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (f : JLMS.OrdinalC 𝕜 β) (x : JLMS.OrdinalInterval γ) :
    pfpOrdinalAnchorNormalize g hg htop T f (g x) = 0 := by
  simp only [pfpOrdinalAnchorNormalize_apply,
    JLMS.ordinalEmbeddingCeiling_apply_image g hg htop, sub_self]

theorem pfpOrdinalAnchorNormalize_complement_boundary_zero
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (f : JLMS.OrdinalC 𝕜 β) (hf : ∀ x, f (g x) = 0)
    (x : JLMS.OrdinalInterval γ) :
    (ContinuousLinearMap.id 𝕜 (JLMS.OrdinalC 𝕜 β) -
      pfpOrdinalAnchorNormalize g hg htop T) f (g x) = 0 := by
  change f (g x) - pfpOrdinalAnchorNormalize g hg htop T f (g x) = 0
  rw [hf, pfpOrdinalAnchorNormalize_boundary_zero, sub_zero]

theorem pfpOrdinalAnchorNormalize_budget
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    ‖pfpOrdinalAnchorNormalize g hg htop T‖ +
      ‖ContinuousLinearMap.id 𝕜 _ - pfpOrdinalAnchorNormalize g hg htop T‖ ≤
        1 + 4 * ‖T‖ := by
  have h := norm_pfpOrdinalAnchorNormalize_le g hg htop T
  have hs := norm_sub_le (ContinuousLinearMap.id 𝕜 (JLMS.OrdinalC 𝕜 β))
    (pfpOrdinalAnchorNormalize g hg htop T)
  have hi := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := JLMS.OrdinalC 𝕜 β)
  linarith

variable {I : Type*} {D : I → Type*}
  [∀ i, TopologicalSpace (D i)] [∀ i, CompactSpace (D i)]
variable (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
  (k : I → Iio γ) (hk : Function.Injective k)
  (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
  (hq : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (k i))

theorem pfpOrdinalAnchoredRead_projection_eq_zero :
    (ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero k hk q hq).comp
      (pfpOrdinalAnchorProjection g hg htop) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply JLMS.CZeroSum.ext
  intro i
  ext x
  change pfpOrdinalAnchorProjection g hg htop f (q i x) -
    pfpOrdinalAnchorProjection g hg htop f
      (g ⟨succ (k i).val, Ordinal.zero_le _, succ_le_of_lt (k i).property⟩) = 0
  simp only [pfpOrdinalAnchorProjection_apply,
    ordinalEmbeddingCeiling_eq_block_right g hg htop (k i) (q i x) (hq i x),
    JLMS.ordinalEmbeddingCeiling_apply_image g hg htop, sub_self]

theorem pfpOrdinalAnchoredRead_normalize
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    (ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero k hk q hq).comp
      (pfpOrdinalAnchorNormalize g hg htop T) =
        (ordinalAnchoredBlockReadback g hg htop hzero k hk q hq).comp T := by
  unfold pfpOrdinalAnchorNormalize
  rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_id, pfpOrdinalAnchoredRead_projection_eq_zero,
    sub_zero]

theorem pfpOrdinalAnchoredRead_complement_normalize
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    (ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero k hk q hq).comp
      (ContinuousLinearMap.id 𝕜 _ - pfpOrdinalAnchorNormalize g hg htop T) =
        (ordinalAnchoredBlockReadback g hg htop hzero k hk q hq).comp
          (ContinuousLinearMap.id 𝕜 _ - T) := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub,
    pfpOrdinalAnchoredRead_normalize]

theorem pfpOrdinalAnchoredRead_branch_normalize
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) (b : Bool) :
    (ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero k hk q hq).comp
      (if b then pfpOrdinalAnchorNormalize g hg htop T
       else ContinuousLinearMap.id 𝕜 _ - pfpOrdinalAnchorNormalize g hg htop T) =
        (ordinalAnchoredBlockReadback g hg htop hzero k hk q hq).comp
          (if b then T else ContinuousLinearMap.id 𝕜 _ - T) := by
  cases b
  · exact pfpOrdinalAnchoredRead_complement_normalize g hg htop hzero k hk q hq T
  · exact pfpOrdinalAnchoredRead_normalize g hg htop hzero k hk q hq T

theorem pfpOrdinalAnchoredRead_factor_transfer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) (b : Bool)
    (J : E →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (V : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜] E)
    {K : ℝ} (hK : 0 ≤ K) (hJ : ‖J‖ ≤ 1) (hV : ‖V‖ ≤ K)
    (hf : V.comp ((ordinalAnchoredBlockReadback g hg htop hzero k hk q hq).comp
      ((if b then pfpOrdinalAnchorNormalize g hg htop T
        else ContinuousLinearMap.id 𝕜 _ - pfpOrdinalAnchorNormalize g hg htop T).comp J)) =
          ContinuousLinearMap.id 𝕜 E) :
    ThesisCommon.FactorsIdentityWith
      (if b then T else ContinuousLinearMap.id 𝕜 _ - T) E (2 * K) := by
  let Q := ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero k hk q hq
  refine ⟨V.comp Q, J, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_assoc
      (ordinalAnchoredBlockReadback g hg htop hzero k hk q hq) _ J,
      pfpOrdinalAnchoredRead_branch_normalize g hg htop hzero k hk q hq T b] at hf
    simpa only [Q, ContinuousLinearMap.comp_assoc] using hf
  · have hQ : ‖Q‖ ≤ 2 := ordinalAnchoredBlockReadback_norm_le g hg htop hzero k hk q hq
    calc
      ‖V.comp Q‖ * ‖J‖ ≤ (‖V‖ * ‖Q‖) * ‖J‖ :=
        mul_le_mul_of_nonneg_right (V.opNorm_comp_le Q) (norm_nonneg J)
      _ ≤ (K * 2) * 1 := mul_le_mul
        (mul_le_mul hV hQ (norm_nonneg Q) hK) hJ (norm_nonneg J) (by positivity)
      _ = 2 * K := by ring

end Posets
