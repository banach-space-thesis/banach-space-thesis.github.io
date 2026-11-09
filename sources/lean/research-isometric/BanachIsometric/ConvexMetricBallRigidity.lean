import BanachIsometric.DefiniteSeminormModel
import BanachIsometric.MetricGaugeNormTransport
import BanachIsometric.OppositeNormedDivisionRing
import BanachIsometric.QuaternionicCompletion
import BanachIsometric.ComplexPolarization

/-! Proper absolutely convex balls become Hermitian under the explicit
functional-rigidity premise. Their definite seminorms and their norm models
are constructed from the original balls; the original scalar-linear metric
maps induce the norm isometries required by the proved A-to-B reduction. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

section Complex

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
    [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem complex_convexBallGauge_hermitian_of_functionalStatement
    (hA : ComplexFunctionalStatement (X := X)) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    {r : ℝ} (hr : 0 < r) (hb : Balanced ℂ (Metric.closedBall (0 : X) r))
    (hc : Convex ℝ (Metric.closedBall (0 : X) r))
    (hproper : Metric.closedBall (0 : X) r ≠ univ) :
    HasHermitianSquare (centeredBallGauge (X := X) r) := by
  let p := divisionAlgebraCenteredBallSeminorm r hr hb hc
  have hdef : ∀ x : X, p x = 0 ↔ x = 0 :=
    centeredBallGauge_definite_of_linearMetric_homogeneity (by omega) hdim hmetric hr hb hc hproper
  let M := DefiniteSeminormModel p hdef
  letI : NormedSpace ℂ M :=
    { inferInstanceAs (Module ℂ M) with norm_smul_le := fun a x => (norm_smul a x).le }
  let e : X ≃ₗ[ℂ] M := toDefiniteSeminormModel p hdef
  have hnorm (x : X) : ‖e x‖ = centeredBallGauge r x := rfl
  have hm : ∀ E F : Submodule ℂ M,
      Module.rank ℂ E = (n : Cardinal) → Module.rank ℂ F = (n : Cardinal) → Nonempty (E ≃ᵢ F) := by
    intro E F hE hF
    obtain ⟨T⟩ := linearIsometry_subspaces_of_metric_ballGauge hmetric r e hnorm E F
      (Module.finrank_eq_of_rank_eq hE) (Module.finrank_eq_of_rank_eq hF)
    exact ⟨T.toIsometryEquiv⟩
  have hAm : ComplexFunctionalStatement (X := M) := hA
  obtain ⟨h, hdiag⟩ := hAm n norm hn (e.rank_eq.symm ▸ hdim)
    norm_isDefiniteComplexHomogeneous (norm_complexSphereLipschitz n)
    (metricSubspaceHomogeneity_realEquivalentSections hm)
  let hX : PositiveHermitianForm X :=
    { form x y := h.form (e x) (e y)
      conj_symm x y := h.conj_symm (e x) (e y)
      add_right x y z := by rw [e.map_add, h.add_right]
      smul_right x y a := by rw [e.map_smul, h.smul_right]
      self_im x := h.self_im (e x)
      self_nonneg x := h.self_nonneg (e x)
      self_pos x hx := h.self_pos (e x) (fun hz => hx (e.injective (hz.trans e.map_zero.symm))) }
  refine ⟨hX, ?_⟩
  intro x
  change h.form (e x) (e x) = _
  rw [hdiag, hnorm]

end Complex

section Quaternionic

open Quaternionic

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [IsScalarTower ℝ Hᵐᵒᵖ X] [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem quaternionic_convexBallGauge_hermitian_of_functionalStatement
    (hA : Quaternionic.FunctionalStatement (E := X)) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    {r : ℝ} (hr : 0 < r) (hb : Balanced Hᵐᵒᵖ (Metric.closedBall (0 : X) r))
    (hc : Convex ℝ (Metric.closedBall (0 : X) r))
    (hproper : Metric.closedBall (0 : X) r ≠ univ) :
    Quaternionic.HasHermitianSquare (centeredBallGauge (X := X) r) := by
  let p := divisionAlgebraCenteredBallSeminorm r hr hb hc
  have hdef : ∀ x : X, p x = 0 ↔ x = 0 :=
    centeredBallGauge_definite_of_linearMetric_homogeneity (by omega) hdim hmetric hr hb hc hproper
  let M := DefiniteSeminormModel p hdef
  let e : X ≃ₗ[Hᵐᵒᵖ] M := toDefiniteSeminormModel p hdef
  have hnorm (x : X) : ‖e x‖ = centeredBallGauge r x := rfl
  have hm : Quaternionic.MetricSubspaceHomogeneity (V := M) n := by
    intro E F hE hF
    obtain ⟨T⟩ := linearIsometry_subspaces_of_metric_ballGauge hmetric r e hnorm E F
      (Module.finrank_eq_of_rank_eq hE) (Module.finrank_eq_of_rank_eq hF)
    exact ⟨T.toIsometryEquiv⟩
  have hAm : Quaternionic.FunctionalStatement (E := M) := hA
  obtain ⟨h, hdiag, hpos⟩ := functionalStatement_implies_corollaryB (V := M) hAm n hn
    (e.rank_eq.symm ▸ hdim) hm
  refine ⟨h.comap e.toLinearMap, ?_, ?_⟩
  · intro x
    change h.form (e x) (e x) = _
    have hxx := hdiag (e x)
    change h.form (e x) (e x) = (‖e x‖ ^ 2 : ℝ) at hxx
    rw [hnorm] at hxx
    exact hxx
  · intro x hx
    exact hpos (e x) (fun hz => hx (e.injective (hz.trans e.map_zero.symm)))

end Quaternionic

end
end BanachIsometric.MetricGeometry
