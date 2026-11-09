import BanachIsometric.EvenSphereClutchingTransitivity
import BanachIsometric.TransitiveBodyQuadratic
import BanachIsometric.HemisphereClutching
import BanachIsometric.ExactSectionQuadraticPropagation

/-! The real even-section argument for the actual exact-section bundle.
Odd ambient rank gives a genuine hairy-ball obstruction. The fixed model is
covariance-normalized, its body group is proved transitive, and its gauge
square is therefore quadratic. This route uses no even-homotopy torsion premise. -/

noncomputable section

namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {m : ℕ} {p : F → ℝ}
  {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem exists_reference_quadraticForm_of_odd_ambient_rank
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    {N : ℕ} [NeZero N] (e : F ≃L[ℝ] PiolaSpace N)
    (hOdd : Odd (Module.finrank ℝ F))
    (v : sphere (0 : F) 1) (q₀ : EquatorSphere v)
    (w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 := by
  obtain ⟨north, south, g, hnorth, hsouth, hglue⟩ :=
    D.exists_hemisphere_clutching μ hp hSphere hProj v
  have hnorth' : ∀ x, Function.Injective (north x) ∧
      ∀ y, inner ℝ x.val.val (north x y) = 0 := by
    intro x
    refine ⟨(hnorth x).1, fun y => ?_⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    exact hTangent x.val ((hnorth x).2.1.le (LinearMap.mem_range_self _ y))
  have hsouth' : ∀ x, Function.Injective (south x) ∧
      ∀ y, inner ℝ x.val.val (south x y) = 0 := by
    intro x
    refine ⟨(hsouth x).1, fun y => ?_⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    exact hTangent x.val ((hsouth x).2.1.le (LinearMap.mem_range_self _ y))
  obtain ⟨hS, _hreg, h0⟩ := D.modelBody_geometric_properties hp hSphere
  obtain ⟨A, _hA, htrans⟩ := exists_covariance_transitive_bodyGroup_of_tangent_clutching
    e hOdd μ hS h0 v q₀ north south hnorth' hsouth' g hglue
  exact exists_posDef_quadraticForm_of_normalized_transitive_bodyGroup
    (hp.comp_linearIsometry D.reference) A w (htrans w)

theorem exists_ambient_quadraticForm_of_odd_ambient_rank
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    {N : ℕ} [NeZero N] (e : F ≃L[ℝ] PiolaSpace N)
    (hOdd : Odd (Module.finrank ℝ F))
    (v : sphere (0 : F) 1) (q₀ : EquatorSphere v)
    (w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1)
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ (∀ x, Q x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | Q x ≤ 1} := by
  obtain ⟨Q, _hQpos, hQ⟩ := D.exists_reference_quadraticForm_of_odd_ambient_rank
    μ hp hSphere hProj hTangent e hOdd v q₀ w
  obtain ⟨L, hL⟩ := hp.exists_lipschitzWith hSphere
  exact D.exists_ambient_quadraticForm_of_reference_quadraticForm hp hL.continuous Q hQ hpair

end BanachIsometric.ExactSectionPrincipalData
