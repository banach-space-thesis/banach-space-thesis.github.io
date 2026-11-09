import BanachIsometric.OppositeNormedDivisionRing
import BanachIsometric.HermitianGaugeModels
import BanachIsometric.DivisionAlgebraGauge
import BanachIsometric.MetricGaugeIsometries

/-! Collapse of actual metric-ball gauges over C and the right quaternions.
Positive Hermitian-square witnesses are the explicit remaining rigidity input.
The simultaneous proportionality conclusion is proved, using theorem D with
exactly the original scalar-linear metric isometries. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

set_option maxHeartbeats 1600000

section Complex

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
    [MetricSpace X]

theorem complex_centeredBallGauge_proportional {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n) (r s : ℝ)
    (hb : Balanced ℂ (Metric.closedBall (0 : X) r))
    (hp : HasHermitianSquare (centeredBallGauge (X := X) r))
    (hq : HasHermitianSquare (centeredBallGauge (X := X) s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : X, centeredBallGauge s x = c * centeredBallGauge r x := by
  obtain ⟨pForm, hpForm⟩ := hp
  obtain ⟨qForm, hqForm⟩ := hq
  let D := complexPositiveGaugeData pForm hpForm (fun x => gauge_nonneg x)
  letI : NormSMulClass ℂ (GaugeNormModel D) := gaugeNormModelNormSMul (R := ℂ) (X := X) D
    (fun a x => centeredBallGauge_smul_divisionAlgebra (R := ℂ) (X := X) hb a x)
  letI : NormedSpace ℂ (GaugeNormModel D) :=
    { inferInstanceAs (Module ℂ (GaugeNormModel D)) with
      norm_smul_le := fun a x => (norm_smul a x).le }
  let e := toGaugeNormModelScalar (R := ℂ) D
  have hpM : HasHermitianSquare (norm : GaugeNormModel D → ℝ) := by
    refine ⟨pForm, ?_⟩
    intro x
    rw [norm_gaugeNormModel]
    exact hpForm x
  have hqM : HasHermitianSquare (fun x : GaugeNormModel D => centeredBallGauge s (e.symm x)) :=
    ⟨qForm, hqForm⟩
  have hsim := (hmetric.simultaneous_ball_gauges r s).map e
  have hnorm : (fun y : GaugeNormModel D => centeredBallGauge r (e.symm y)) = norm := by
    funext y
    exact (norm_gaugeNormModel D y).symm
  rw [hnorm] at hsim
  obtain ⟨c, hc, hprop⟩ := complex_norm_proportional_of_hermitian_similarities hn
    (e.rank_eq.symm ▸ hdim) hpM hqM (fun y => gauge_nonneg (e.symm y)) hsim
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hprop (e x)
  rw [e.symm_apply_apply, norm_gaugeNormModel] at h
  exact h

end Complex

section Quaternionic

open Quaternionic

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [IsScalarTower ℝ Hᵐᵒᵖ X] [MetricSpace X]

theorem quaternionic_centeredBallGauge_proportional {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n) (r s : ℝ)
    (hb : Balanced Hᵐᵒᵖ (Metric.closedBall (0 : X) r))
    (hp : Quaternionic.HasHermitianSquare (centeredBallGauge (X := X) r))
    (hq : Quaternionic.HasHermitianSquare (centeredBallGauge (X := X) s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : X, centeredBallGauge s x = c * centeredBallGauge r x := by
  obtain ⟨pForm, hpForm, hpPos⟩ := hp
  obtain ⟨qForm, hqForm, hqPos⟩ := hq
  let D := quaternionicPositiveGaugeData pForm hpForm hpPos (fun x => gauge_nonneg x)
  letI : NormSMulClass Hᵐᵒᵖ (GaugeNormModel D) := gaugeNormModelNormSMul (R := Hᵐᵒᵖ) (X := X) D
    (fun a x => centeredBallGauge_smul_divisionAlgebra (R := Hᵐᵒᵖ) (X := X) hb a x)
  let e := toGaugeNormModelScalar (R := Hᵐᵒᵖ) D
  have hpM : Quaternionic.HasHermitianSquare (norm : GaugeNormModel D → ℝ) := by
    refine ⟨pForm, ?_, hpPos⟩
    intro x
    change pForm.form x x = (‖x‖ ^ 2 : ℝ)
    rw [norm_gaugeNormModel]
    exact hpForm x
  have hqM : Quaternionic.HasHermitianSquare
      (fun x : GaugeNormModel D => centeredBallGauge s (e.symm x)) := ⟨qForm, hqForm, hqPos⟩
  have hsim := (hmetric.simultaneous_ball_gauges r s).map e
  have hnorm : (fun y : GaugeNormModel D => centeredBallGauge r (e.symm y)) = norm := by
    funext y
    exact (norm_gaugeNormModel D y).symm
  rw [hnorm] at hsim
  obtain ⟨c, hc, hprop⟩ := quaternionic_norm_proportional_of_hermitian_similarities hn
    (e.rank_eq.symm ▸ hdim) hpM hqM (fun y => gauge_nonneg (e.symm y)) hsim
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hprop (e x)
  rw [e.symm_apply_apply, norm_gaugeNormModel] at h
  exact h

end Quaternionic

end
end BanachIsometric.MetricGeometry





