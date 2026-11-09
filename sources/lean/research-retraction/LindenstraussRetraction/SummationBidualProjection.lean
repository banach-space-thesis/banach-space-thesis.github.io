import LindenstraussRetraction.BlockDecomposition
import LindenstraussRetraction.BidualMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A contractive projection from the bidual of the finite-block ℓ₁ sum. -/

noncomputable section
open scoped BigOperators ENNReal

namespace LindenstraussRetraction

universe v u
variable {𝕜 : Type v} [RCLike 𝕜]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

local instance projectionBidualNormedGroup (X : Type u)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : NormedAddCommGroup (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

theorem strongDual_finrank_eq (E : Type u) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    Module.finrank 𝕜 (StrongDual 𝕜 E) = Module.finrank 𝕜 E := by
  calc
    Module.finrank 𝕜 (StrongDual 𝕜 E) = Module.finrank 𝕜 (Module.Dual 𝕜 E) :=
      (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] (E →L[𝕜] 𝕜)).symm.finrank_eq
    _ = Module.finrank 𝕜 E := Subspace.dual_finrank_eq

/-- Finite-dimensional reflexivity, with the actual canonical embedding. -/
def finiteBidualEquiv (E : Type u) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : E ≃ₗᵢ[𝕜] Bidual 𝕜 E :=
  (bidualEmbedding 𝕜 E).toLinearIsometryEquiv (by
    rw [strongDual_finrank_eq (𝕜 := 𝕜) (StrongDual 𝕜 E), strongDual_finrank_eq (𝕜 := 𝕜) E])

@[simp] theorem finiteBidualEquiv_apply (E : Type u) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (x : E) :
    finiteBidualEquiv (𝕜 := 𝕜) E x = bidualEmbedding 𝕜 E x := rfl

variable (𝕜)

/-- The original ℓ₁ block coordinates of a bidual element, using finite reflexivity. -/
def summationBidualCoordinate (m : ℕ) :
    Bidual 𝕜 (SummationSpace 𝕜) →L[𝕜] FiniteCoordinateSpace 𝕜 m :=
  (finiteBidualEquiv (𝕜 := 𝕜) (FiniteCoordinateSpace 𝕜 m)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (bidualMap (summationBlockEvaluation 𝕜 m))

theorem summationBidualCoordinate_embedding (m : ℕ) (y : SummationSpace 𝕜) :
    summationBidualCoordinate 𝕜 m (bidualEmbedding 𝕜 (SummationSpace 𝕜) y) = y m := by
  change (finiteBidualEquiv (𝕜 := 𝕜) (FiniteCoordinateSpace 𝕜 m)).symm
    (bidualMap (summationBlockEvaluation 𝕜 m) (bidualEmbedding 𝕜 (SummationSpace 𝕜) y)) = _
  rw [bidualMap_embedding, ← finiteBidualEquiv_apply]
  exact (finiteBidualEquiv (𝕜 := 𝕜) (FiniteCoordinateSpace 𝕜 m)).symm_apply_apply _

theorem summationBidualCoordinate_dual (z : Bidual 𝕜 (SummationSpace 𝕜))
    (m : ℕ) (f : StrongDual 𝕜 (FiniteCoordinateSpace 𝕜 m)) :
    f (summationBidualCoordinate 𝕜 m z) = z (f.comp (summationBlockEvaluation 𝕜 m)) := by
  have h := (finiteBidualEquiv (𝕜 := 𝕜) (FiniteCoordinateSpace 𝕜 m)).apply_symm_apply
    (bidualMap (summationBlockEvaluation 𝕜 m) z)
  have he := congrArg (fun w : Bidual 𝕜 (FiniteCoordinateSpace 𝕜 m) => w f) h
  exact he

theorem summationBidualCoordinate_sum_le (z : Bidual 𝕜 (SummationSpace 𝕜)) (s : Finset ℕ) :
    ∑ m ∈ s, ‖summationBidualCoordinate 𝕜 m z‖ ≤ ‖z‖ := by
  classical
  choose f hfNorm hfEval using fun m =>
    exists_dual_vector'' 𝕜 (summationBidualCoordinate 𝕜 m z)
  let g : StrongDual 𝕜 (SummationSpace 𝕜) :=
    ∑ m ∈ s, (f m).comp (summationBlockEvaluation 𝕜 m)
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro y
    calc
      ‖g y‖ ≤ ∑ m ∈ s, ‖f m (y m)‖ := by
        simp only [g, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
          summationBlockEvaluation_apply]
        exact norm_sum_le _ _
      _ ≤ ∑ m ∈ s, ‖y m‖ := by
        apply Finset.sum_le_sum
        intro m _hm
        apply ((f m).le_opNorm (y m)).trans
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hfNorm m) (norm_nonneg (y m))
      _ ≤ ‖y‖ := by
        rw [← (summationSpace_hasSum_norm 𝕜 y).tsum_eq]
        exact (summationSpace_hasSum_norm 𝕜 y).summable.sum_le_tsum s (fun _ _ => norm_nonneg _)
      _ = 1 * ‖y‖ := (one_mul _).symm
  have he : z g = ((∑ m ∈ s, ‖summationBidualCoordinate 𝕜 m z‖ : ℝ) : 𝕜) := by
    simp only [g, map_sum, ← summationBidualCoordinate_dual, hfEval]
  calc
    ∑ m ∈ s, ‖summationBidualCoordinate 𝕜 m z‖ = ‖z g‖ := by
      rw [he, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    _ ≤ ‖z‖ * ‖g‖ := z.le_opNorm g
    _ ≤ ‖z‖ := by simpa using mul_le_mul_of_nonneg_left hg (norm_nonneg z)

def summationBidualProjectionValue (z : Bidual 𝕜 (SummationSpace 𝕜)) : SummationSpace 𝕜 :=
  ⟨fun m => summationBidualCoordinate 𝕜 m z,
    memℓp_gen' (p := (1 : ℝ≥0∞)) (by
      intro s
      simpa only [ENNReal.toReal_one, Real.rpow_one] using summationBidualCoordinate_sum_le 𝕜 z s)⟩

theorem norm_summationBidualProjectionValue_le (z : Bidual 𝕜 (SummationSpace 𝕜)) :
    ‖summationBidualProjectionValue 𝕜 z‖ ≤ ‖z‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (norm_nonneg z)
  intro s
  simpa only [ENNReal.toReal_one, Real.rpow_one] using summationBidualCoordinate_sum_le 𝕜 z s

/-- The canonical contractive projection of the finite-block ℓ₁ sum's bidual. -/
def summationBidualProjection : Bidual 𝕜 (SummationSpace 𝕜) →L[𝕜] SummationSpace 𝕜 :=
  ({ toFun := summationBidualProjectionValue 𝕜
     map_add' := fun z w => by
       apply lp.ext
       funext m
       exact (summationBidualCoordinate 𝕜 m).map_add z w
     map_smul' := fun c z => by
       apply lp.ext
       funext m
       exact (summationBidualCoordinate 𝕜 m).map_smul c z } : _ →ₗ[𝕜] _).mkContinuous 1 (by
         intro z
         simpa only [one_mul] using norm_summationBidualProjectionValue_le 𝕜 z)

theorem norm_summationBidualProjection_le (z : Bidual 𝕜 (SummationSpace 𝕜)) :
    ‖summationBidualProjection 𝕜 z‖ ≤ ‖z‖ := norm_summationBidualProjectionValue_le 𝕜 z

@[simp] theorem summationBidualProjection_embedding (y : SummationSpace 𝕜) :
    summationBidualProjection 𝕜 (bidualEmbedding 𝕜 (SummationSpace 𝕜) y) = y := by
  apply lp.ext
  funext m
  exact summationBidualCoordinate_embedding 𝕜 m y

end LindenstraussRetraction
