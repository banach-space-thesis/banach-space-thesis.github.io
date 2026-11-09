import BanachIsometric.RealFunctionalRigidity
import BanachIsometric.RealOddConvexMetricTorsion
import BanachIsometric.RealOddMetricStarTorsion

/-! The real case of Theorem E for the original compatible translation-invariant
metric. Cofinal absolutely convex balls work in every section dimension at
least two. The circled Lipschitz star-body alternative uses odd section
dimension. The radial profile uses the same complete Hilbert norm. -/

noncomputable section
namespace BanachIsometric.MetricGeometry

open Set Metric
open scoped Topology NNReal

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

private theorem real_convexBallGauge_positiveGaugeData
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    {r : ℝ} (hr : 0 < r) (hb : Balanced ℝ (closedBall (0 : X) r))
    (hc : Convex ℝ (closedBall (0 : X) r)) (hproper : closedBall (0 : X) r ≠ univ) :
    Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r)) := by
  let p := divisionAlgebraCenteredBallSeminorm (R := ℝ) r hr hb hc
  have hdef : ∀ x : X, p x = 0 ↔ x = 0 :=
    centeredBallGauge_definite_of_linearMetric_homogeneity (by omega) hdim hmetric hr hb hc hproper
  let M := DefiniteSeminormModel p hdef
  letI : NormedSpace ℝ M :=
    { inferInstanceAs (Module ℝ M) with norm_smul_le := fun a x => (norm_smul a x).le }
  let e : X ≃ₗ[ℝ] M := toDefiniteSeminormModel p hdef
  have hnorm (x : X) : ‖e x‖ = centeredBallGauge r x := rfl
  have hm : MetricSubspaceHomogeneity ℝ M n := by
    intro E F hE hF
    obtain ⟨T⟩ := linearIsometry_subspaces_of_metric_ballGauge hmetric r e hnorm E F
      (Module.finrank_eq_of_rank_eq hE) (Module.finrank_eq_of_rank_eq hF)
    exact ⟨T.toIsometryEquiv⟩
  obtain ⟨D⟩ := real_norm_positiveGaugeData hn (e.rank_eq.symm ▸ hdim) hm
  exact ⟨D.comap e.toLinearMap e.injective⟩

private theorem real_hilbertMetricModel_of_quadratic_ball_gauges
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hconv : ∀ r ∈ Radii, Convex ℝ (closedBall (0 : X) r))
    (hforms : ∀ r ∈ Radii, closedBall (0 : X) r ≠ univ →
      Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r))) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ ∃ e : X ≃L[ℝ] GaugeNormModel D,
        ∀ x, ‖e x‖ = centeredBallGauge r₀ x := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  let S : Set ℝ := {r | r ∈ Radii ∧ r < dist x₀ 0}
  have hS : CofinalPositiveRadii S := cofinalPositiveRadii_restrict
    (cofinalPositiveRadii_of_zero_mem_closure hRpos hRzero) (dist_pos.mpr hx₀)
  obtain ⟨r₀, hr₀, _, _⟩ := hS 1 zero_lt_one
  obtain ⟨D⟩ := hforms r₀ hr₀.1 (centeredBall_proper_of_lt_distance x₀ hr₀.2)
  have hscale : ∀ r ∈ S, ∃ c : ℝ, 0 < c ∧
      ∀ x : X, centeredBallGauge r x = c * centeredBallGauge r₀ x := by
    intro r hr
    obtain ⟨Q⟩ := hforms r hr.1 (centeredBall_proper_of_lt_distance x₀ hr.2)
    exact real_centeredBallGauge_proportional hn hdim hmetric r₀ r D Q
  exact ⟨r₀, hr₀.1, D,
    completeSpace_gaugeNormModel_of_ball_gauges D hTI S hS (fun r hr => hconv r hr.1) hscale,
    gaugeContinuousLinearEquivOfBallGauges D hTI S hS (fun r hr => hconv r hr.1) hscale,
    fun x => norm_gaugeNormModel D (toGaugeNormModel D x)⟩

/-- The two ball hypotheses of the real case of Theorem E. Circledness is
stated on each actual finite-dimensional section. -/
theorem realTheoremE
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : (∀ r ∈ Radii, Balanced ℝ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) ∨
      (Odd n ∧ ∀ r ∈ Radii, FiniteScalarRadialBallSections (R := ℝ) (X := X) r ∧
        ∀ Y : Submodule ℝ X, FiniteDimensional ℝ Y → Y ≠ ⊥ →
          ScalarCircled (R := ℝ) (Y.subtype ⁻¹' closedBall (0 : X) r))) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ ∃ e : X ≃L[ℝ] GaugeNormModel D,
        ∀ x, ‖e x‖ = centeredBallGauge r₀ x := by
  rcases hballs with hconv | ⟨hodd, hstar⟩
  · exact real_hilbertMetricModel_of_quadratic_ball_gauges hn hdim hmetric hTI hcomplete
      Radii hRpos hRzero (fun r hr => (hconv r hr).2)
      (fun r hr hproper => real_convexBallGauge_positiveGaugeData hn hdim hmetric
        (hRpos hr) (hconv r hr).1 (hconv r hr).2 hproper)
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    have hforms (r : ℝ) (hr : r ∈ Radii) :
        Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r)) := by
      have hp := (finiteScalarRadialBallSections_gauge_data (R := ℝ) (hRpos hr) (hstar r hr).1).1
      exact positiveGaugeData_of_real_odd_sections hp hn3 hodd hdim
        (real_ballGauge_localSphereLipschitz_of_radial_sections (hstar r hr).1)
        (real_ballGauge_realEquivalentSections hmetric r)
    have hconv (r : ℝ) (hr : r ∈ Radii) : Convex ℝ (closedBall (0 : X) r) := by
      obtain ⟨D⟩ := hforms r hr
      exact convex_centeredBall_of_positive_gauge_data D r
        (finiteScalarRadialBallSections_gauge_data (R := ℝ) (hRpos hr) (hstar r hr).1).2
    exact real_hilbertMetricModel_of_quadratic_ball_gauges hn hdim hmetric hTI hcomplete
      Radii hRpos hRzero hconv (fun r hr _ => hforms r hr)

/-- The real radial metric conclusion with the same complete Hilbert model
and the literal original distance. -/
theorem realTheoremE_radial_profile
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced ℝ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ > 0, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ ∃ e : X ≃L[ℝ] GaugeNormModel D,
        (∀ x, ‖e x‖ = centeredBallGauge r₀ x) ∧
        ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
          (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
          ∀ x y : X, dist x y = φ ‖e x - e y‖₊ := by
  have hRzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    simp only [closure_Ioi, mem_Ici, le_refl]
  obtain ⟨r₀, hr₀, D, hD, e, hnorm⟩ := realTheoremE hn hdim hmetric hTI hcomplete
    (Ioi 0) (fun _ hr => hr) hRzero (Or.inl hballs)
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  letI : Nontrivial X := ⟨⟨x₀, 0, hx₀⟩⟩
  have hforms (r : ℝ) (hr : 0 < r) (hproper : closedBall (0 : X) r ≠ univ) :
      Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r)) :=
    real_convexBallGauge_positiveGaugeData hn hdim hmetric hr (hballs r hr).1 (hballs r hr).2 hproper
  obtain ⟨φ, hφcont, hφmono, hφzero, hφpos, hφsubadd, hφdist⟩ :=
    exists_radial_metric_profile_of_proportional_ball_gauges D hTI (fun r hr => (hballs r hr).2)
      (real_proper_ball_gauges_proportional hn hdim hmetric r₀ D hforms)
  refine ⟨r₀, hr₀, D, hD, e, hnorm, φ, hφcont, hφmono, hφzero, hφpos, hφsubadd, ?_⟩
  intro x y
  have harg : ‖e x - e y‖₊ = ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ := by
    apply Subtype.ext
    change ‖e x - e y‖ = centeredBallGauge r₀ (x - y)
    rw [← map_sub, hnorm]
  rw [harg]
  exact hφdist x y

end BanachIsometric.MetricGeometry
