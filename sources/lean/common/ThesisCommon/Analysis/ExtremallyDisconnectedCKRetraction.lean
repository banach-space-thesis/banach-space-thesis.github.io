import ThesisCommon.Analysis.WeakDualUnitBallLift
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.ContinuousMap.Compact

/-! Contractive retractions onto C(K) for extremally disconnected compact
Hausdorff K. Projectivity of K continuously lifts point evaluations through
the Hahn–Banach restriction map of compact weak-star dual balls. Evaluating
that lift constructs the retraction; no linear injectivity is assumed. -/
noncomputable section
set_option synthInstance.maxSize 1024
universe u
open Set Topology Function
namespace ThesisCommon
variable (𝕜 : Type) [RCLike 𝕜]
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

def continuousMapEvalUnitBall (x : K) : weakDualUnitBall 𝕜 C(K, 𝕜) :=
  ⟨StrongDual.toWeakDual (ContinuousMap.evalCLM 𝕜 x), by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa only [one_mul] using f.norm_coe_le_norm x⟩

theorem continuousMapEvalUnitBall_continuous :
    Continuous (continuousMapEvalUnitBall (K := K) 𝕜) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact f.continuous

variable {𝕜}
variable [T2Space K] [ExtremallyDisconnected K]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_contractively_retract_continuousMap (i : C(K, 𝕜) →ₗᵢ[𝕜] E) :
    ∃ P : E →L[𝕜] C(K, 𝕜), ‖P‖ ≤ 1 ∧ ∀ f, P (i f) = f := by
  obtain ⟨s, hs, hext⟩ := CompactT2.ExtremallyDisconnected.projective
    (continuousMapEvalUnitBall_continuous (K := K) 𝕜)
    (weakDualUnitBallRestrict_continuous i) (weakDualUnitBallRestrict_surjective i)
  let L : E →ₗ[𝕜] C(K, 𝕜) :=
    { toFun := fun z => ⟨fun x => (s x).1 z,
        (WeakDual.eval_continuous z).comp (continuous_subtype_val.comp hs)⟩
      map_add' := by intro z w; ext x; exact map_add (WeakDual.toStrongDual (s x).1) z w
      map_smul' := by intro a z; ext x; exact map_smul (WeakDual.toStrongDual (s x).1) a z }
  have hL : ∀ z, ‖L z‖ ≤ 1 * ‖z‖ := by
    intro z
    apply (ContinuousMap.norm_le _ (mul_nonneg zero_le_one (norm_nonneg z))).mpr
    intro x
    exact ((WeakDual.toStrongDual (s x).1).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (s x).2 (norm_nonneg z))
  refine ⟨L.mkContinuous 1 hL, L.mkContinuous_norm_le zero_le_one hL, ?_⟩
  intro f
  ext x
  have hx := congrFun hext x
  have hx' := congrArg (fun φ : weakDualUnitBall 𝕜 C(K, 𝕜) => φ.1 f) hx
  exact hx'

local instance continuousMapBidualRetractionNormedAddCommGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜))) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 C(K, 𝕜)) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance continuousMapBidualRetractionNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜))) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 C(K, 𝕜)) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem exists_continuousMap_bidual_retraction :
    ∃ P : StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜)) →L[𝕜] C(K, 𝕜),
      ‖P‖ ≤ 1 ∧ ∀ f, P (NormedSpace.inclusionInDoubleDual 𝕜 C(K, 𝕜) f) = f :=
  exists_contractively_retract_continuousMap (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := C(K, 𝕜)))

end ThesisCommon
