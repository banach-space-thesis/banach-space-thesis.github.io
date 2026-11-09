import BanachIsometric.ComplexFunctionalTorsion
import BanachIsometric.ComplexReducedFrechet
import BanachIsometric.ComplexMetricCorollaries
import BanachIsometric.MetricGroupUniformity

/-! Original complex B, C and E, conditional only on the explicitly remaining
even-homotopy torsion assertion for the actual identity components of compact
regular-closed body automorphism groups. The original norm, scalar action,
grading, uniformity and metric are retained in the respective conclusions.
This file does not establish the torsion assertion or unconditional A--E. -/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory UniformSpace
open scoped Topology Topology.Homotopy NNReal

variable (hTorsion : ∀ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
  IsCompact S → closure (interior S) = S →
  (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S →
  ∀ k : ℕ, Even (k + 2) →
  ∀ α : HomotopyGroup (Fin (k + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem complex_corollaryB_of_body_even_homotopy_torsion (n : ℕ) :
    ComplexCorollaryBAt V n := by
  intro hn hdim hm
  apply hasCompatibleInnerProduct_iff_givenScalarAction.mp
  exact complexFunctionalStatement_implies_corollaryB
    (complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion) n hn hdim hm

theorem complex_norm_hermitianSquare_of_body_even_homotopy_torsion
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ V)
    (hm : MetricSubspaceHomogeneity ℂ V n) :
    HasHermitianSquare (norm : V → ℝ) :=
  complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion n norm hn hdim
    norm_isDefiniteComplexHomogeneous (norm_complexSphereLipschitz n)
    (metricSubspaceHomogeneity_realEquivalentSections hm)

theorem complex_completion_corollaryB_of_body_even_homotopy_torsion
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ V)
    (hm : MetricSubspaceHomogeneity ℂ V n) :
    ComplexIsHilbertForNorm (V := Completion V) :=
  complex_completion_isHilbertForNorm
    (complex_norm_hermitianSquare_of_body_even_homotopy_torsion hTorsion n hn hdim hm)

theorem complex_complete_corollaryB_of_body_even_homotopy_torsion
    [CompleteSpace V] (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ V)
    (hm : MetricSubspaceHomogeneity ℂ V n) : ComplexIsHilbertForNorm (V := V) :=
  ⟨inferInstance,
    complex_norm_hermitianSquare_of_body_even_homotopy_torsion hTorsion n hn hdim hm⟩

end Normed

section Frechet

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

theorem complex_hilbertianGrading_iff_reducedNIsometricGrading_of_body_even_homotopy_torsion
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X) :
    AdmitsHilbertianGrading (X := X) ↔ AdmitsReducedNIsometricGrading (X := X) n :=
  admitsHilbertianGrading_iff_reducedNIsometricGrading_of_functional n hn hdim
    (fun _ => complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion)

theorem complex_exists_cofinal_hilbert_inverseLimit_of_body_even_homotopy_torsion
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p)
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hReduced : ReducedNIsometric p n) :
    ∃ k₀ : ℕ, (∀ k, SeminormIsHilbertian (p (k + k₀)) ∧
      ComplexIsHilbertForNorm (V := SeminormCompletion (p (k + k₀)))) ∧
      Nonempty (X ≃L[ℂ] seminormLimitSubmodule (fun k => p (k + k₀))
        (seminormTail_monotone p hmono k₀)) :=
  exists_cofinal_hilbert_inverseLimit p hmono hp n hn hdim
    (fun _ => complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion) hReduced

end Frechet

section Metric

open MetricGeometry

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
    [IsScalarTower ℝ ℂ X] [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem complex_exists_hilbert_metric_model_of_convex_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hm : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : ∀ r ∈ Radii, Balanced ℂ (closedBall (0 : X) r) ∧
      Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[ℂ] GaugeNormModel D) := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  exact exists_complex_hilbert_metric_model_of_convex_balls
    (complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion)
    hn hdim hm hTI Radii hRpos hRzero hballs

theorem complex_exists_hilbert_metric_model_of_radial_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hm : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hsections : ∀ r ∈ Radii, FiniteScalarRadialBallSections (R := ℂ) (X := X) r)
    (hcircled : ∀ r ∈ Radii, ∀ Y : Submodule ℂ X, FiniteDimensional ℂ Y → Y ≠ ⊥ →
      ScalarCircled (R := ℂ) (Y.subtype ⁻¹' closedBall 0 r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[ℂ] GaugeNormModel D) := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  exact exists_complex_hilbert_metric_model_of_radial_balls
    (complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion)
    hn hdim hm hTI Radii hRpos hRzero hsections hcircled

theorem complex_exists_radial_metric_profile_of_convex_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hm : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced ℂ (closedBall (0 : X) r) ∧
      Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ :=
  exists_complex_radial_metric_profile_of_convex_balls
    (complexFunctionalStatement_of_body_even_homotopy_torsion hTorsion) hn hdim hm hTI hballs

end Metric
end BanachIsometric
