import BanachIsometric.MetricBallGauge
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! A compatible translation-invariant metric induces the canonical additive
uniformity. Thus completeness of the Frechet group uniformity is exactly
completeness for the chosen original metric, not an extra metric assumption. -/

namespace BanachIsometric.MetricGeometry

open Filter
open scoped Topology

variable {X : Type*} [AddCommGroup X] [MetricSpace X]

theorem dist_neg_neg_of_translationInvariant (hTI : TranslationInvariant (X := X)) (x y : X) :
    dist (-x) (-y) = dist x y := by
  rw [dist_eq_dist_sub_zero hTI (-x) (-y), neg_sub_neg]
  rw [← dist_eq_dist_sub_zero hTI y x, dist_comm]

theorem dist_sub_sub_le_of_translationInvariant (hTI : TranslationInvariant (X := X))
    (x₁ x₂ y₁ y₂ : X) :
    dist (x₁ - x₂) (y₁ - y₂) ≤ dist x₁ y₁ + dist x₂ y₂ := by
  have h₁ : dist (x₁ - x₂) (y₁ - x₂) = dist x₁ y₁ := by
    simpa only [sub_eq_add_neg] using hTI x₁ y₁ (-x₂)
  have h₂ : dist (y₁ - x₂) (y₁ - y₂) = dist x₂ y₂ := by
    rw [sub_eq_add_neg, sub_eq_add_neg, add_comm y₁ (-x₂), add_comm y₁ (-y₂), hTI]
    exact dist_neg_neg_of_translationInvariant hTI x₂ y₂
  exact (dist_triangle (x₁ - x₂) (y₁ - x₂) (y₁ - y₂)).trans_eq (by rw [h₁, h₂])

def isUniformAddGroupOfTranslationInvariant (hTI : TranslationInvariant (X := X)) : IsUniformAddGroup X where
  uniformContinuous_sub := by
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro p q hpq
    have h₁ : dist p.1 q.1 < ε / 2 := (show dist p.1 q.1 ≤ dist p q from le_max_left _ _).trans_lt hpq
    have h₂ : dist p.2 q.2 < ε / 2 := (show dist p.2 q.2 ≤ dist p q from le_max_right _ _).trans_lt hpq
    exact (dist_sub_sub_le_of_translationInvariant hTI _ _ _ _).trans_lt (by linarith)

variable [IsTopologicalAddGroup X]

theorem canonicalUniformSpace_eq_metric (hTI : TranslationInvariant (X := X)) :
    IsTopologicalAddGroup.toUniformSpace X = (inferInstance : UniformSpace X) := by
  letI : IsUniformAddGroup X := isUniformAddGroupOfTranslationInvariant hTI
  exact IsUniformAddGroup.toUniformSpace_eq

theorem completeSpace_metric_iff_canonical (hTI : TranslationInvariant (X := X)) :
    CompleteSpace X ↔ @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X) := by
  rw [canonicalUniformSpace_eq_metric hTI]

end BanachIsometric.MetricGeometry

