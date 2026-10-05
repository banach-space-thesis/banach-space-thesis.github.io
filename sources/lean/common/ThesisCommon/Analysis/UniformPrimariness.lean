import ThesisCommon.Analysis.Primary
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Linarith

/-! Quantitative primariness and WCG, with their actual bounded isomorphisms
and weak topology. For the zero projection we use C(max(1, ||P||)), the
convention explicitly selected by the user on 1 October 2026. -/
noncomputable section
namespace ThesisCommon

/-- The approved max convention agrees with ||P|| on every nonzero projection. -/
theorem projection_max_one_norm {𝕜 : Type*} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (P : X →L[𝕜] X) (hP : P.comp P = P) (hne : P ≠ 0) : max 1 ‖P‖ = ‖P‖ := by
  apply max_eq_right
  have hbound := P.opNorm_comp_le P
  rw [hP] at hbound
  by_contra h
  have hsmall := mul_lt_mul_of_pos_left (lt_of_not_ge h) (norm_pos_iff.mpr hne)
  nlinarith

/-- An actual bounded equivalence with distortion at most C; no assumption
that a Banach--Mazur infimum is attained is made. -/
def IsomorphicWithBound (𝕜 : Type*) [RCLike 𝕜]
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (C : ℝ) : Prop :=
  ∃ e : X ≃L[𝕜] Y, ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ C

/-- Definition 2.2 with the user-approved extension at ||P||=0.
Only values of C on [1,infinity) matter; this is equivalent to giving C on
that interval, with no constraint on the irrelevant values outside it. -/
def IsUniformlyPrimary (𝕜 : Type*) [RCLike 𝕜]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ C : ℝ → ℝ, MonotoneOn C (Set.Ici 1) ∧ (∀ t, 1 ≤ t → 1 ≤ C t) ∧
    ∀ P : X →L[𝕜] X, P.comp P = P →
      IsomorphicWithBound 𝕜 X (LinearMap.range P.toLinearMap) (C (max 1 ‖P‖)) ∨
      IsomorphicWithBound 𝕜 X
        (LinearMap.range (ContinuousLinearMap.id 𝕜 X - P).toLinearMap) (C (max 1 ‖P‖))

/-- Forgetting the quantitative bound gives the actual primariness dichotomy. -/
theorem IsUniformlyPrimary.isPrimary {𝕜 : Type*} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (h : IsUniformlyPrimary 𝕜 X) : IsPrimary 𝕜 X := by
  obtain ⟨_, _, _, h⟩ := h
  intro P hP
  rcases h P hP with ⟨e, _⟩ | ⟨e, _⟩
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

/-- A weakly compact set whose linear span is norm-dense. Compactness is
in WeakSpace, while the closure of the span is in the original norm topology.
This does not assume separable-range consequences or any transfer theorem. -/
def IsWeaklyCompactlyGenerated (𝕜 : Type*) [RCLike 𝕜]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ K : Set X, IsCompact ((toWeakSpace 𝕜 X) '' K) ∧
    (Submodule.span 𝕜 K).topologicalClosure = ⊤

end ThesisCommon
