import SurveyStatements.P1BasicSequences
import SurveyStatements.P4BaireAdjoint
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences

/-! Bounded dual evaluations on a weakly null sequence have an actual
coordinatewise convergent subsequence with a limit vanishing at infinity.
The ambient space need not be separable: restriction to the countably
generated closed span supplies the compact metrizable dual ball. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology TopologicalSpace

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem sequenceClosedSpan_isSeparable (e : ℕ → X) :
    IsSeparable (sequenceClosedSpan e : Set X) := by
  simpa only [sequenceClosedSpan, Submodule.topologicalClosure_coe] using
    ((Set.countable_range e).isSeparable.span (R := ℂ)).closure

theorem weakNull_boundedDual_coordinate_cluster (e : ℕ → X)
    (he : ∀ f : StrongDual ℂ X, Tendsto (fun i => f (e i)) atTop (𝓝 0))
    (b : ℕ → StrongDual ℂ X) (hb : ∀ n, ‖b n‖ ≤ 1) :
    ∃ g : ℕ → ℂ, Tendsto g atTop (𝓝 0) ∧ ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ i : ℕ, Tendsto (fun n => b (ν n) (e i)) atTop (𝓝 (g i)) := by
  classical
  let S : Submodule ℂ X := sequenceClosedSpan e
  letI : SeparableSpace S := (sequenceClosedSpan_isSeparable e).separableSpace
  let eS : ℕ → S := fun i => ⟨e i,
    (Submodule.span ℂ (range e)).le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)⟩
  let r : ℕ → StrongDual ℂ S := fun n => (b n).comp S.subtypeL
  have hr (n : ℕ) : ‖r n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖b n (x : X)‖ ≤ 1 * ‖x‖
    exact ((b n).le_opNorm (x : X)).trans
      (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg (x : X)))
  let K : Set (WeakDual ℂ S) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ S) 1
  have hK : IsCompact K := WeakDual.isCompact_closedBall ℂ (0 : StrongDual ℂ S) 1
  let s : ℕ → K := fun n => ⟨StrongDual.toWeakDual (r n), by
    change dist (r n) 0 ≤ 1
    rw [dist_zero_right (r n)]
    exact hr n⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MetrizableSpace K := SurveyStatements.P4.weakStarCompact_metrizable hK
  obtain ⟨φ, ν, hν, hlim⟩ := CompactSpace.tendsto_subseq s
  let g : ℕ → ℂ := fun i => φ.val (eS i)
  obtain ⟨f, hf, _⟩ := exists_extension_norm_eq S (WeakDual.toStrongDual φ.val)
  have hg : g = fun i => f (e i) := by
    funext i
    exact (hf (eS i)).symm
  have hgn : Tendsto g atTop (𝓝 0) := by
    rw [hg]
    exact he f
  refine ⟨g, hgn, ν, hν, ?_⟩
  intro i
  have ht := (((WeakDual.eval_continuous (eS i)).comp continuous_subtype_val).tendsto φ).comp hlim
  change Tendsto (fun n => b (ν n) (e i)) atTop (𝓝 (g i)) at ht
  exact ht

end SurveyStatements.P1
