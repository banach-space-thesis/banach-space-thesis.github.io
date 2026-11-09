import BanachIsometric.HomologicalFunctionalRigidity
import BanachIsometric.ComplexReducedFrechet
import BanachIsometric.ComplexMetricCorollaries
import BanachIsometric.MetricGroupUniformity

/-! The metric, grading, and completion conclusions on the original scalar action. -/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory UniformSpace
open scoped Topology Topology.Homotopy NNReal

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem complexCorollaryB (n : ℕ) :
    ComplexCorollaryBAt V n := by
  intro hn hdim hm
  apply hasCompatibleInnerProduct_iff_givenScalarAction.mp
  exact complexFunctionalStatement_implies_corollaryB
    complexTheoremA n hn hdim hm

theorem complex_norm_hermitianSquare_homological
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ V)
    (hm : MetricSubspaceHomogeneity ℂ V n) :
    HasHermitianSquare (norm : V → ℝ) :=
  complexTheoremA n norm hn hdim
    norm_isDefiniteComplexHomogeneous (norm_complexSphereLipschitz n)
    (metricSubspaceHomogeneity_realEquivalentSections hm)

theorem complex_completion_corollaryB_homological
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ V)
    (hm : MetricSubspaceHomogeneity ℂ V n) :
    ComplexIsHilbertForNorm (V := Completion V) :=
  complex_completion_isHilbertForNorm
    (complex_norm_hermitianSquare_homological n hn hdim hm)

theorem complex_complete_corollaryB_homological
    [CompleteSpace V] (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ V)
    (hm : MetricSubspaceHomogeneity ℂ V n) : ComplexIsHilbertForNorm (V := V) :=
  ⟨inferInstance,
    complex_norm_hermitianSquare_homological n hn hdim hm⟩

end Normed

section Frechet

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

theorem complexTheoremC
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X) :
    AdmitsHilbertianGrading (X := X) ↔ AdmitsReducedNIsometricGrading (X := X) n :=
  admitsHilbertianGrading_iff_reducedNIsometricGrading_of_functional n hn hdim
    (fun _ => complexTheoremA)

theorem complex_exists_cofinal_hilbert_inverseLimit_homological
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p)
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hReduced : ReducedNIsometric p n) :
    ∃ k₀ : ℕ, (∀ k, SeminormIsHilbertian (p (k + k₀)) ∧
      ComplexIsHilbertForNorm (V := SeminormCompletion (p (k + k₀)))) ∧
      (∀ i j (hij : i ≤ j), DenseRange (completedSeminormFactor (seminormTail_monotone p hmono k₀ hij))) ∧
      Nonempty (X ≃L[ℂ] seminormLimitSubmodule (fun k => p (k + k₀))
        (seminormTail_monotone p hmono k₀)) := by
  obtain ⟨k₀, ht, he⟩ := exists_cofinal_hilbert_inverseLimit p hmono hp n hn hdim
    (fun _ => complexTheoremA) hReduced
  exact ⟨k₀, ht, fun _ _ hij => completedSeminormFactor_denseRange (seminormTail_monotone p hmono k₀ hij), he⟩

end Frechet

section Metric

open MetricGeometry

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
    [IsScalarTower ℝ ℂ X] [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem complex_exists_hilbert_metric_model_of_convex_balls_homological
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
    complexTheoremA
    hn hdim hm hTI Radii hRpos hRzero hballs

theorem complex_exists_hilbert_metric_model_of_radial_balls_homological
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
    complexTheoremA
    hn hdim hm hTI Radii hRpos hRzero hsections hcircled

/-- The complex case of Theorem E, with either manuscript ball hypothesis. -/
theorem complexTheoremE
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hm : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : (∀ r ∈ Radii, Balanced ℂ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) ∨
      (∀ r ∈ Radii, FiniteScalarRadialBallSections (R := ℂ) (X := X) r ∧
        ∀ Y : Submodule ℂ X, FiniteDimensional ℂ Y → Y ≠ ⊥ →
          ScalarCircled (R := ℂ) (Y.subtype ⁻¹' closedBall (0 : X) r))) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[ℂ] GaugeNormModel D) := by
  rcases hballs with hconv | hradial
  · exact complex_exists_hilbert_metric_model_of_convex_balls_homological
      hn hdim hm hTI hcomplete Radii hRpos hRzero hconv
  · exact complex_exists_hilbert_metric_model_of_radial_balls_homological
      hn hdim hm hTI hcomplete Radii hRpos hRzero
      (fun r hr => (hradial r hr).1) (fun r hr => (hradial r hr).2)

theorem complex_exists_radial_metric_profile_of_convex_balls_homological
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hm : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced ℂ (closedBall (0 : X) r) ∧
      Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      HasHermitianSquare (centeredBallGauge (X := X) r₀) ∧
      CompleteSpace (GaugeNormModel D) ∧
      (∃ e : X ≃L[ℂ] GaugeNormModel D, ∀ x, ‖e x‖ = centeredBallGauge r₀ x) ∧
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  letI : Nontrivial X := ⟨⟨x₀, 0, hx₀⟩⟩
  let r₀ : ℝ := dist x₀ 0 / 2
  have hr₀ : 0 < r₀ := half_pos (dist_pos.mpr hx₀)
  have hproper : closedBall (0 : X) r₀ ≠ univ :=
    centeredBall_proper_of_lt_distance x₀ (half_lt_self (dist_pos.mpr hx₀))
  obtain ⟨h, hh⟩ := complex_convexBallGauge_hermitian_of_functionalStatement
    complexTheoremA hn hdim hm hr₀ (hballs r₀ hr₀).1 (hballs r₀ hr₀).2 hproper
  let D := complexPositiveGaugeData h hh (fun x => gauge_nonneg x)
  have hscale (r : ℝ) (hr : 0 < r) (hproperr : closedBall (0 : X) r ≠ univ) :=
    complex_centeredBallGauge_proportional hn hdim hm r₀ r (hballs r₀ hr₀).1 ⟨h, hh⟩
      (complex_convexBallGauge_hermitian_of_functionalStatement complexTheoremA hn hdim hm hr
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
  let e := gaugeContinuousLinearEquivScalarOfBallGauges (R := ℂ) D hTI S hS hconv hscaleS
  exact ⟨r₀, hr₀, D, ⟨h, hh⟩, completeSpace_gaugeNormModel_of_ball_gauges D hTI S hS hconv hscaleS,
    ⟨e, fun x => norm_gaugeNormModel D (e x)⟩,
    exists_radial_metric_profile_of_proportional_ball_gauges D hTI (fun r hr => (hballs r hr).2) hscale⟩

end Metric
end BanachIsometric
