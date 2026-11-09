import BanachIsometric.RealEvenNormRigidity
import BanachIsometric.RealOddConvexMetricTorsion

/-! The actual real even-section convex-ball branch. Proper-ball gauges are
proved quadratic, the original compatible complete topology is Hilbertian,
and the unchanged metric has a monotone subadditive radial profile. -/

namespace BanachIsometric.MetricGeometry

open Set Metric MeasureTheory
open scoped Topology NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
theorem real_even_convexBallGauge_positiveGaugeData
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
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
  obtain ⟨D⟩ := real_even_norm_positiveGaugeData
    hn heven (e.rank_eq.symm ▸ hdim) hm
  exact ⟨D.comap e.toLinearMap e.injective⟩

theorem real_even_hilbert_metric_model_of_convex_balls
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : ∀ r ∈ Radii, Balanced ℝ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ Nonempty (X ≃L[ℝ] GaugeNormModel D) := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  exact exists_real_hilbert_metric_model_of_ball_gauges (by omega) hdim hmetric hTI Radii hRpos hRzero
    (fun r hr => (hballs r hr).2)
    (fun r hr hproper => real_even_convexBallGauge_positiveGaugeData
      hn heven hdim hmetric (hRpos hr) (hballs r hr).1 (hballs r hr).2 hproper)

theorem real_even_radial_metric_profile_of_convex_balls
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced ℝ (closedBall (0 : X) r) ∧ Convex ℝ (closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ :=
  exists_real_radial_metric_profile_of_convex_balls (by omega) hdim hmetric hTI
    (fun r hr => (hballs r hr).2)
    (fun r hr hproper => real_even_convexBallGauge_positiveGaugeData
      hn heven hdim hmetric hr (hballs r hr).1 (hballs r hr).2 hproper)

end
end BanachIsometric.MetricGeometry
