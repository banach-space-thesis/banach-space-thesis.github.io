import Posets.UltrafilterSynchronization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

/-! Bounded scalar limits along ultrafilters, used in Lemma 8.2. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 P : Type*} [RCLike 𝕜]

theorem tendsto_ultrafilter_bounded (U : Ultrafilter P) (f : P → 𝕜)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto f (U : Filter P) (𝓝 (limUnder (U : Filter P) f)) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  apply tendsto_nhds_limUnder
  obtain ⟨a, _, ha⟩ := (isCompact_closedBall (0 : 𝕜) C).ultrafilter_le_nhds'
    (Ultrafilter.map f U) (show Metric.closedBall 0 C ∈ Ultrafilter.map f U from by
      change ∀ᶠ x in (U : Filter P), f x ∈ Metric.closedBall 0 C
      apply Filter.Eventually.of_forall
      intro x
      simpa only [Metric.mem_closedBall, dist_zero_right] using hC x)
  exact ⟨a, ha⟩

theorem norm_ultrafilter_bounded_le (U : Ultrafilter P) (f : P → 𝕜)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : ‖limUnder (U : Filter P) f‖ ≤ C :=
  le_of_tendsto (tendsto_ultrafilter_bounded U f hC).norm (Filter.Eventually.of_forall hC)

theorem tendsto_ultrafilter_evaluation (U : Ultrafilter P) (a : Discrete P →ᵇ 𝕜) :
    Tendsto (fun x => a ⟨x⟩) (U : Filter P)
      (𝓝 (limUnder (U : Filter P) (fun x => a ⟨x⟩))) :=
  tendsto_ultrafilter_bounded U _ (fun x => a.norm_coe_le_norm ⟨x⟩)

/-- Evaluation at an ultrafilter is a bounded scalar linear functional. -/
def ultrafilterEvaluation (U : Ultrafilter P) : (Discrete P →ᵇ 𝕜) →L[𝕜] 𝕜 :=
  ({toFun := fun a => limUnder (U : Filter P) (fun x => a ⟨x⟩)
    map_add' := fun a b =>
      ((tendsto_ultrafilter_evaluation U a).add (tendsto_ultrafilter_evaluation U b)).limUnder_eq
    map_smul' := fun c a =>
      ((tendsto_ultrafilter_evaluation U a).const_smul c).limUnder_eq} :
    (Discrete P →ᵇ 𝕜) →ₗ[𝕜] 𝕜).mkContinuous 1 (fun a => by
      simpa only [one_mul] using norm_ultrafilter_bounded_le U
        (fun x => a ⟨x⟩) (fun x => a.norm_coe_le_norm ⟨x⟩))

@[simp] theorem ultrafilterEvaluation_apply (U : Ultrafilter P) (a : Discrete P →ᵇ 𝕜) :
    ultrafilterEvaluation U a = limUnder (U : Filter P) (fun x => a ⟨x⟩) := rfl

theorem ultrafilterEvaluation_mul (U : Ultrafilter P) (a b : Discrete P →ᵇ 𝕜) :
    ultrafilterEvaluation U (a * b) = ultrafilterEvaluation U a * ultrafilterEvaluation U b :=
  ((tendsto_ultrafilter_evaluation U a).mul (tendsto_ultrafilter_evaluation U b)).limUnder_eq

theorem ultrafilterEvaluation_one (U : Ultrafilter P) :
    ultrafilterEvaluation (𝕜 := 𝕜) U 1 = 1 := tendsto_const_nhds.limUnder_eq

end Posets
