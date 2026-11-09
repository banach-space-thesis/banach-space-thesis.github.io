import LindenstraussRetraction.BidualMap
import LindenstraussRetraction.RadialRetraction

/-!
# Transfer to complemented subspaces and equivalent norms

A uniformly continuous retraction of bidual unit balls transfers through
bounded linear maps U and V with V ∘ U = id. Scaling U before taking
its second adjoint gives a contractive map between the bidual unit balls.
-/

noncomputable section

namespace LindenstraussRetraction

universe u v w

variable (𝕜 : Type w) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

set_option synthInstance.maxSize 512

local instance : NormedAddCommGroup (Bidual 𝕜 E) := inferInstance
local instance : NormedAddCommGroup (Bidual 𝕜 Z) := inferInstance
local instance : NormedSpace 𝕜 (Bidual 𝕜 E) := inferInstance
local instance : NormedSpace 𝕜 (Bidual 𝕜 Z) := inferInstance

def complementScale (U : E →L[𝕜] Z) : ℝ := max 1 ‖U‖

theorem complementScale_pos (U : E →L[𝕜] Z) : 0 < complementScale 𝕜 U :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

def scaledComplementEmbedding (U : E →L[𝕜] Z) : E →L[𝕜] Z :=
  (((complementScale 𝕜 U)⁻¹ : ℝ) : 𝕜) • U

theorem norm_scaledComplementEmbedding_le (U : E →L[𝕜] Z) :
    ‖scaledComplementEmbedding 𝕜 U‖ ≤ 1 := by
  have ha := complementScale_pos 𝕜 U
  rw [scaledComplementEmbedding, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (inv_nonneg.mpr ha.le)]
  exact (inv_mul_le_one₀ ha).mpr (le_max_right _ _)

def scaledComplementBallEmbedding (U : E →L[𝕜] Z) (x : UnitBall E) : UnitBall Z :=
  ⟨scaledComplementEmbedding 𝕜 U x.val, by
    have hb : ‖scaledComplementEmbedding 𝕜 U x.val‖ ≤ ‖x.val‖ := by
      simpa only [one_mul] using (scaledComplementEmbedding 𝕜 U).le_of_opNorm_le
        (norm_scaledComplementEmbedding_le 𝕜 U) x.val
    exact hb.trans x.property⟩

def scaledComplementBidualBallEmbedding (U : E →L[𝕜] Z)
    (z : UnitBall (Bidual 𝕜 E)) : UnitBall (Bidual 𝕜 Z) :=
  ⟨bidualMap (scaledComplementEmbedding 𝕜 U) z.val, by
    calc
      _ ≤ ‖scaledComplementEmbedding 𝕜 U‖ * ‖z.val‖ :=
        norm_bidualMap_apply_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_scaledComplementEmbedding_le 𝕜 U)
        z.property z.val.opNorm_nonneg zero_le_one
      _ = 1 := one_mul _⟩

theorem scaledComplementBidualBallEmbedding_lipschitz (U : E →L[𝕜] Z) :
    LipschitzWith 1 (scaledComplementBidualBallEmbedding 𝕜 U) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (bidualMap (scaledComplementEmbedding 𝕜 U) x.val)
    (bidualMap (scaledComplementEmbedding 𝕜 U) y.val) ≤ (1 : ℝ) * dist x.val y.val
  simp only [dist_eq_norm, ← map_sub]
  exact (norm_bidualMap_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_scaledComplementEmbedding_le 𝕜 U)
      (x.val - y.val).opNorm_nonneg)

theorem scaledComplementBidualBallEmbedding_uniformContinuous (U : E →L[𝕜] Z) :
    UniformContinuous (scaledComplementBidualBallEmbedding 𝕜 U) :=
  (scaledComplementBidualBallEmbedding_lipschitz 𝕜 U).uniformContinuous

theorem scaledComplementBidualBallEmbedding_embedding (U : E →L[𝕜] Z) (x : UnitBall E) :
    scaledComplementBidualBallEmbedding 𝕜 U (unitBallBidualEmbedding 𝕜 E x) =
      unitBallBidualEmbedding 𝕜 Z (scaledComplementBallEmbedding 𝕜 U x) := by
  apply Subtype.ext
  exact bidualMap_embedding _ _

theorem scaledComplement_recover (U : E →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hUV : Function.LeftInverse V U) (x : UnitBall E) :
    (complementScale 𝕜 U : 𝕜) • V (scaledComplementBallEmbedding 𝕜 U x).val = x.val := by
  change (complementScale 𝕜 U : 𝕜) •
    V ((((complementScale 𝕜 U)⁻¹ : ℝ) : 𝕜) • U x.val) = x.val
  rw [map_smul, smul_smul, ← RCLike.ofReal_mul,
    mul_inv_cancel₀ (complementScale_pos 𝕜 U).ne', RCLike.ofReal_one, one_smul]
  exact hUV x.val

theorem hasUniformUnitBallBidualRetraction_of_complemented
    (hcomp : IsComplementedIn 𝕜 E Z)
    (h : HasUniformUnitBallBidualRetraction 𝕜 Z) :
    HasUniformUnitBallBidualRetraction 𝕜 E := by
  obtain ⟨U, V, hUV⟩ := hcomp
  obtain ⟨r, hr, hri⟩ := h
  let S : Z →L[𝕜] E := (complementScale 𝕜 U : 𝕜) • V
  refine ⟨fun z => radialRetraction 𝕜
      (S (r (scaledComplementBidualBallEmbedding 𝕜 U z)).val),
    (radialRetraction_uniformContinuous 𝕜).comp
      (S.uniformContinuous.comp (uniformContinuous_subtype_val.comp
        (hr.comp (scaledComplementBidualBallEmbedding_uniformContinuous 𝕜 U)))), ?_⟩
  intro x
  change radialRetraction 𝕜 (S (r (scaledComplementBidualBallEmbedding 𝕜 U
    (unitBallBidualEmbedding 𝕜 E x))).val) = x
  rw [scaledComplementBidualBallEmbedding_embedding, hri]
  have hS : S (scaledComplementBallEmbedding 𝕜 U x).val = x.val :=
    scaledComplement_recover 𝕜 U V hUV x
  rw [hS]
  exact radialRetraction_coe 𝕜 x

theorem hasUniformUnitBallBidualRetraction_iff_of_continuousLinearEquiv
    (e : E ≃L[𝕜] Z) :
    HasUniformUnitBallBidualRetraction 𝕜 E ↔
      HasUniformUnitBallBidualRetraction 𝕜 Z := by
  constructor
  · apply hasUniformUnitBallBidualRetraction_of_complemented 𝕜
    exact ⟨e.symm.toContinuousLinearMap, e.toContinuousLinearMap, e.apply_symm_apply⟩
  · apply hasUniformUnitBallBidualRetraction_of_complemented 𝕜
    exact ⟨e.toContinuousLinearMap, e.symm.toContinuousLinearMap, e.symm_apply_apply⟩

end LindenstraussRetraction
