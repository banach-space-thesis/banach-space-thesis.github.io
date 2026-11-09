import BanachIsometric.QuaternionicFunctionalTorsion
import BanachIsometric.QuaternionicCorollaryCompletion
import BanachIsometric.QuaternionicReducedFrechet
import BanachIsometric.QuaternionicMetricCorollaries
import BanachIsometric.MetricGroupUniformity

/-! Original quaternionic B, C and E follow from the same explicit remaining
actual compact-body even-homotopy torsion assertion. No functional theorem,
Hermitian gauge, inverse-limit conclusion or metric radiality is an input. -/

namespace BanachIsometric.Quaternionic

open Set Metric MeasureTheory UniformSpace
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable (hTorsion : ∀ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S →
  ∀ k : ℕ, Even (k + 2) →
  ∀ α : HomotopyGroup (Fin (k + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

section Normed

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]

theorem normedCorollaryB_of_body_even_homotopy_torsion (n : ℕ) : NormedCorollaryBAt (V := V) n :=
  functionalStatement_implies_corollaryB (functionalStatement_of_body_even_homotopy_torsion hTorsion) n

theorem completionCorollaryB_of_body_even_homotopy_torsion (n : ℕ) (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ V)
    (hmetric : MetricSubspaceHomogeneity (V := V) n) : IsHilbertForNorm (V := Completion V) :=
  functionalStatement_implies_completion_corollaryB
    (functionalStatement_of_body_even_homotopy_torsion hTorsion) n hn hdim hmetric

end Normed

section Frechet

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

theorem hilbertianGrading_iff_reducedNIsometricGrading_of_body_even_homotopy_torsion
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X) :
    AdmitsHilbertianGrading (X := X) ↔ AdmitsReducedNIsometricGrading (X := X) n :=
  admitsHilbertianGrading_iff_reducedNIsometricGrading n hn hdim
    (fun _ => functionalStatement_of_body_even_homotopy_torsion hTorsion)

theorem exists_cofinal_hilbert_inverseLimit_of_body_even_homotopy_torsion
    (p : ℕ → RightSeminorm X) (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm))
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : ReducedNIsometric p n) :
    ∃ k₀ : ℕ, (∀ k, SeminormIsHilbertian (p (k + k₀)) ∧
      IsHilbertForNorm (V := SeminormCompletion (p (k + k₀)))) ∧
      Nonempty (X ≃L[Hᵐᵒᵖ] seminormLimitSubmodule (fun k => p (k + k₀))
        (seminormTail_monotone p hmono k₀)) :=
  exists_cofinal_hilbert_inverseLimit p hmono hp n hn hdim
    (fun _ => functionalStatement_of_body_even_homotopy_torsion hTorsion) hmetric

end Frechet

section Metric

open MetricGeometry

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [IsScalarTower ℝ Hᵐᵒᵖ X] [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem exists_hilbert_metric_model_of_convex_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : ∀ r ∈ Radii, Balanced Hᵐᵒᵖ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass Hᵐᵒᵖ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧ Nonempty (X ≃L[Hᵐᵒᵖ] GaugeNormModel D) := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  exact exists_quaternionic_hilbert_metric_model_of_convex_balls
    (functionalStatement_of_body_even_homotopy_torsion hTorsion) hn hdim hmetric hTI Radii hRpos hRzero hballs

theorem exists_hilbert_metric_model_of_radial_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hsections : ∀ r ∈ Radii, FiniteScalarRadialBallSections (R := Hᵐᵒᵖ) (X := X) r)
    (hcircled : ∀ r ∈ Radii, ∀ Y : Submodule Hᵐᵒᵖ X, FiniteDimensional Hᵐᵒᵖ Y → Y ≠ ⊥ →
      ScalarCircled (R := Hᵐᵒᵖ) (Y.subtype ⁻¹' closedBall 0 r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass Hᵐᵒᵖ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧ Nonempty (X ≃L[Hᵐᵒᵖ] GaugeNormModel D) := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  exact exists_quaternionic_hilbert_metric_model_of_radial_balls
    (functionalStatement_of_body_even_homotopy_torsion hTorsion) hn hdim hmetric hTI Radii hRpos hRzero
    hsections hcircled

theorem exists_radial_metric_profile_of_convex_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced Hᵐᵒᵖ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ :=
  exists_quaternionic_radial_metric_profile_of_convex_balls
    (functionalStatement_of_body_even_homotopy_torsion hTorsion) hn hdim hmetric hTI hballs

end Metric

end
end BanachIsometric.Quaternionic
