import BanachIsometric.RealEvenSectionsRigidity
import BanachIsometric.RealOddSectionsTorsion

/-! The real D/E pipelines for every section dimension at least two.
The even-section branch is proved unconditionally. The odd branch retains
the same explicit actual compact-body even-homotopy torsion input as the
complex and quaternionic pipelines. This file does not assert that input. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
  ∀ j : ℕ, Even (j + 2) →
  ∀ α : HomotopyGroup (Fin (j + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem positiveGaugeData_of_real_sections_of_body_even_homotopy_torsion
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hSphere : RealLocalSphereLipschitz n p) (hSections : RealEquivalentRealSections n p) :
    Nonempty (MetricGeometry.PositiveGaugeData p) := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact positiveGaugeData_of_real_even_sections hp hn heven hdim hSphere hSections
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    exact positiveGaugeData_of_real_odd_sections_of_body_even_homotopy_torsion
      hTorsion hp hn3 hodd hdim hSphere hSections

theorem real_normedCorollaryB_of_body_even_homotopy_torsion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ V)
    (hmetric : MetricSubspaceHomogeneity ℝ V n) : HasInnerProductForGivenScalarAction ℝ V := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact real_even_normedCorollaryB hn heven hdim hmetric
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    exact real_odd_normedCorollaryB_of_body_even_homotopy_torsion hTorsion hn3 hodd hdim hmetric

theorem real_separating_seminorm_family_normable_of_body_even_homotopy_torsion
    {X : Type*} [AddCommGroup X] [Module ℝ X] [UniformSpace X] [IsUniformAddGroup X]
    {ι : Type*} (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hseparating : ∀ x : X, x ≠ 0 → ∃ i, p i x ≠ 0)
    (hsim : ∀ E F : Submodule ℝ X, Module.finrank ℝ E = n → Module.finrank ℝ F = n →
      ∃ T : E ≃ₗ[ℝ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ D : MetricGeometry.PositiveGaugeData (p i₀ : X → ℝ),
      (∃ e : X ≃L[ℝ] MetricGeometry.GaugeNormModel D, ∀ x, ‖e x‖ = p i₀ x) ∧
      (∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x) ∧
      (CompleteSpace X → CompleteSpace (MetricGeometry.GaugeNormModel D)) := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact real_even_separating_seminorm_family_normable p hp hn heven hdim hseparating hsim
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    exact real_odd_separating_seminorm_family_normable_of_body_even_homotopy_torsion
      hTorsion p hp hn3 hodd hdim hseparating hsim

namespace MetricGeometry

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem real_hilbert_metric_model_of_convex_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : ∀ r ∈ Radii, Balanced ℝ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ Nonempty (X ≃L[ℝ] GaugeNormModel D) := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact real_even_hilbert_metric_model_of_convex_balls hn heven hdim hmetric hTI
      hcomplete Radii hRpos hRzero hballs
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    exact real_odd_hilbert_metric_model_of_convex_balls_of_body_even_homotopy_torsion
      hTorsion hn3 hodd hdim hmetric hTI hcomplete Radii hRpos hRzero hballs

theorem real_radial_metric_profile_of_convex_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced ℝ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact real_even_radial_metric_profile_of_convex_balls hn heven hdim hmetric hTI hballs
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    exact real_odd_radial_metric_profile_of_convex_balls_of_body_even_homotopy_torsion
      hTorsion hn3 hodd hdim hmetric hTI hballs

end MetricGeometry
end
end BanachIsometric
