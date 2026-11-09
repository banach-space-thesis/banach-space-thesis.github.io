import BanachIsometric.HomologicalFunctionalRigidity
import BanachIsometric.QuaternionicCorollaryCompletion
import BanachIsometric.QuaternionicReducedFrechet
import BanachIsometric.QuaternionicMetricCorollaries
import BanachIsometric.MetricGroupUniformity

/-! The metric, grading, and completion conclusions on the original scalar action. -/

namespace BanachIsometric.Quaternionic

open Set Metric MeasureTheory UniformSpace
open scoped Topology Topology.Homotopy NNReal

noncomputable section

section Normed

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]

theorem corollaryB (n : ℕ) : NormedCorollaryBAt (V := V) n :=
  functionalStatement_implies_corollaryB theoremA n

theorem completionCorollaryB_homological (n : ℕ) (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ V)
    (hmetric : MetricSubspaceHomogeneity (V := V) n) : IsHilbertForNorm (V := Completion V) :=
  functionalStatement_implies_completion_corollaryB
    theoremA n hn hdim hmetric

theorem completeCorollaryB_homological [CompleteSpace V] (n : ℕ) (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ V)
    (hmetric : MetricSubspaceHomogeneity (V := V) n) : IsHilbertForNorm (V := V) :=
  ⟨inferInstance, corollaryB n hn hdim hmetric⟩

end Normed

section Frechet

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

theorem theoremC
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X) :
    AdmitsHilbertianGrading (X := X) ↔ AdmitsReducedNIsometricGrading (X := X) n :=
  admitsHilbertianGrading_iff_reducedNIsometricGrading n hn hdim
    (fun _ => theoremA)

theorem exists_cofinal_hilbert_inverseLimit_homological
    (p : ℕ → RightSeminorm X) (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm))
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : ReducedNIsometric p n) :
    ∃ k₀ : ℕ, (∀ k, SeminormIsHilbertian (p (k + k₀)) ∧
      IsHilbertForNorm (V := SeminormCompletion (p (k + k₀)))) ∧
      (∀ i j (hij : i ≤ j), DenseRange (completedSeminormFactor (seminormTail_monotone p hmono k₀ hij))) ∧
      Nonempty (X ≃L[Hᵐᵒᵖ] seminormLimitSubmodule (fun k => p (k + k₀))
        (seminormTail_monotone p hmono k₀)) := by
  obtain ⟨k₀, ht, he⟩ := exists_cofinal_hilbert_inverseLimit p hmono hp n hn hdim
    (fun _ => theoremA) hmetric
  exact ⟨k₀, ht, fun _ _ hij => completedSeminormFactor_denseRange (seminormTail_monotone p hmono k₀ hij), he⟩

end Frechet

section Metric

open MetricGeometry

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [IsScalarTower ℝ Hᵐᵒᵖ X] [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem exists_hilbert_metric_model_of_convex_balls_homological
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
    theoremA hn hdim hmetric hTI Radii hRpos hRzero hballs

theorem exists_hilbert_metric_model_of_radial_balls_homological
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
    theoremA hn hdim hmetric hTI Radii hRpos hRzero
    hsections hcircled

/-- The right-quaternionic case of Theorem E, with either manuscript ball hypothesis. -/
theorem theoremE
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : (∀ r ∈ Radii, Balanced Hᵐᵒᵖ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) ∨
      (∀ r ∈ Radii, FiniteScalarRadialBallSections (R := Hᵐᵒᵖ) (X := X) r ∧
        ∀ Y : Submodule Hᵐᵒᵖ X, FiniteDimensional Hᵐᵒᵖ Y → Y ≠ ⊥ →
          ScalarCircled (R := Hᵐᵒᵖ) (Y.subtype ⁻¹' closedBall (0 : X) r))) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass Hᵐᵒᵖ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[Hᵐᵒᵖ] GaugeNormModel D) := by
  rcases hballs with hconv | hradial
  · exact exists_hilbert_metric_model_of_convex_balls_homological
      hn hdim hmetric hTI hcomplete Radii hRpos hRzero hconv
  · exact exists_hilbert_metric_model_of_radial_balls_homological
      hn hdim hmetric hTI hcomplete Radii hRpos hRzero
      (fun r hr => (hradial r hr).1) (fun r hr => (hradial r hr).2)

theorem exists_radial_metric_profile_of_convex_balls_homological
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced Hᵐᵒᵖ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      HasHermitianSquare (centeredBallGauge (X := X) r₀) ∧
      CompleteSpace (GaugeNormModel D) ∧
      (∃ e : X ≃L[Hᵐᵒᵖ] GaugeNormModel D, ∀ x, ‖e x‖ = centeredBallGauge r₀ x) ∧
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  letI : Nontrivial X := ⟨⟨x₀, 0, hx₀⟩⟩
  let r₀ : ℝ := dist x₀ 0 / 2
  have hr₀ : 0 < r₀ := half_pos (dist_pos.mpr hx₀)
  have hproper : closedBall (0 : X) r₀ ≠ univ :=
    centeredBall_proper_of_lt_distance x₀ (half_lt_self (dist_pos.mpr hx₀))
  obtain ⟨h, hh, hpos⟩ := quaternionic_convexBallGauge_hermitian_of_functionalStatement
    theoremA hn hdim hmetric hr₀ (hballs r₀ hr₀).1 (hballs r₀ hr₀).2 hproper
  let D := quaternionicPositiveGaugeData h hh hpos (fun x => gauge_nonneg x)
  have hscale (r : ℝ) (hr : 0 < r) (hproperr : closedBall (0 : X) r ≠ univ) :=
    quaternionic_centeredBallGauge_proportional hn hdim hmetric r₀ r (hballs r₀ hr₀).1 ⟨h, hh, hpos⟩
      (quaternionic_convexBallGauge_hermitian_of_functionalStatement theoremA hn hdim hmetric hr
        (hballs r hr).1 (hballs r hr).2 hproperr)
  let S : Set ℝ := Ioo 0 (dist x₀ 0)
  have hS : CofinalPositiveRadii S := by
    intro ε hε
    have ha := dist_pos.mpr hx₀
    let r := min ε (dist x₀ 0) / 2
    have hr : 0 < r := half_pos (lt_min hε ha)
    have hs := half_lt_self (lt_min hε ha)
    exact ⟨r, ⟨hr, hs.trans_le (min_le_right _ _)⟩, hr, hs.trans_le (min_le_left _ _)⟩
  have hconv : ∀ r ∈ S, Convex ℝ (closedBall (0 : X) r) := fun r hr => (hballs r hr.1).2
  have hscaleS : ∀ r ∈ S, ∃ c : ℝ, 0 < c ∧
      ∀ x, centeredBallGauge r x = c * centeredBallGauge r₀ x :=
    fun r hr => hscale r hr.1 (centeredBall_proper_of_lt_distance x₀ hr.2)
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  let e := gaugeContinuousLinearEquivScalarOfBallGauges (R := Hᵐᵒᵖ) D hTI S hS hconv hscaleS
  exact ⟨r₀, hr₀, D, ⟨h, hh, hpos⟩, completeSpace_gaugeNormModel_of_ball_gauges D hTI S hS hconv hscaleS,
    ⟨e, fun x => norm_gaugeNormModel D (e x)⟩,
    exists_radial_metric_profile_of_proportional_ball_gauges D hTI (fun r hr => (hballs r hr).2) hscale⟩

end Metric

end
end BanachIsometric.Quaternionic
