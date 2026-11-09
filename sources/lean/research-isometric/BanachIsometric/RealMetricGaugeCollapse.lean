import BanachIsometric.MetricGaugeIsometries
import BanachIsometric.MetricHermitianReconstruction

/-! Theorem E's proportionality step over the real field, from actual
positive bilinear representations of the actual centered-ball gauges.
Existence of those representations is an explicit rigidity input; collapse
is proved by the already checked simultaneous-similarity theorem D. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

theorem real_centeredBallGauge_proportional {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (r s : ℝ) (D : PositiveGaugeData (centeredBallGauge (X := X) r))
    (Q : PositiveGaugeData (centeredBallGauge (X := X) s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : X, centeredBallGauge s x = c * centeredBallGauge r x := by
  let e := toGaugeNormModel D
  let B : GaugeNormModel D →ₗ[ℝ] GaugeNormModel D →ₗ[ℝ] ℝ :=
    Q.bilinear.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hB : ∀ x y, star (B x y) = B y x := by
    intro x y
    exact Q.symmetric (e.symm x) (e.symm y)
  have hpos : ∀ x : GaugeNormModel D, x ≠ 0 → 0 < B x x := by
    intro x hx
    change 0 < Q.bilinear (e.symm x) (e.symm x)
    rw [Q.diagonal]
    have hx' : e.symm x ≠ 0 := fun hz => hx (e.symm.injective (hz.trans e.symm.map_zero.symm))
    have hq : centeredBallGauge s (e.symm x) ≠ 0 := (Q.eq_zero_iff _).not.mpr hx'
    exact sq_pos_of_ne_zero hq
  have hsim := (hmetric.simultaneous_ball_gauges r s).map e
  have hnorm : (fun y : GaugeNormModel D => centeredBallGauge r (e.symm y)) = norm := by
    funext y
    exact (norm_gaugeNormModel D y).symm
  rw [hnorm] at hsim
  obtain ⟨c, hc, hprop⟩ := hermitianNorm_global_proportional_of_simultaneous_similarities
    (𝕜 := ℝ) hn (e.rank_eq.symm ▸ hdim) B hB hpos
    (fun y : GaugeNormModel D => centeredBallGauge s (e.symm y))
    (fun y => Q.nonneg (e.symm y)) (fun y => Q.diagonal (e.symm y)) hsim
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hprop (e x)
  rw [e.symm_apply_apply, norm_gaugeNormModel] at h
  exact h

/-- All actual proper centered-ball gauges collapse to the chosen anchor.
The only geometric rigidity input is their positive bilinear representation. -/
theorem real_proper_ball_gauges_proportional {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (r₀ : ℝ) (D : PositiveGaugeData (centeredBallGauge (X := X) r₀))
    (hforms : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : X) r ≠ univ →
      Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r))) :
    ∀ r : ℝ, 0 < r → Metric.closedBall (0 : X) r ≠ univ →
      ∃ c : ℝ, 0 < c ∧ ∀ x : X, centeredBallGauge r x = c * centeredBallGauge r₀ x := by
  intro r hr hproper
  obtain ⟨Q⟩ := hforms r hr hproper
  exact real_centeredBallGauge_proportional hn hdim hmetric r₀ r D Q

end
end BanachIsometric.MetricGeometry

