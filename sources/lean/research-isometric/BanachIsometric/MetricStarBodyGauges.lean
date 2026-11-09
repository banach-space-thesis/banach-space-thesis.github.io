import BanachIsometric.MetricBallGauge
import BanachIsometric.RadialStarBody
import BanachIsometric.FunctionalStarBody

/-! Actual radial descriptions of finite-dimensional metric-ball sections
recover their infimum-defined Minkowski functionals. In particular, the local
sphere Lipschitz hypothesis in Theorem A follows from the stated positive
Lipschitz radii; it is not substituted as an assumption. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

/-- Coordinates and the literal radial carrier of an actual centered-ball
section. There is no norm on the original ambient X in this definition. -/
structure RadialBallSection (r : ℝ) (P : Submodule ℝ X) (d : ℕ) where
  coordinates : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗ[ℝ] P
  body : RadialStarBody (EuclideanSpace ℝ (Fin (d + 1)))
  carrier_image : coordinates '' body.carrier = P.subtype ⁻¹' Metric.closedBall 0 r
  radius_lipschitz : ∃ L : ℝ≥0, LipschitzWith L body.radius

theorem RadialBallSection.gauge_eq {r : ℝ} {P : Submodule ℝ X} {d : ℕ}
    (D : RadialBallSection r P d) (v : EuclideanSpace ℝ (Fin (d + 1))) :
    centeredBallGauge r (D.coordinates v : X) = D.body.gauge v := by
  have h := gauge_image_linearEquiv D.coordinates D.body.carrier v
  rw [D.carrier_image, gauge_preimage_submodule, D.body.gauge_eq_minkowski] at h
  exact h

theorem RadialBallSection.exists_gauge_sphere_lipschitz {r : ℝ} {P : Submodule ℝ X} {d : ℕ}
    (D : RadialBallSection r P d) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun v => centeredBallGauge r (D.coordinates v : X)) (Metric.sphere 0 1) := by
  obtain ⟨C, hC⟩ := D.radius_lipschitz
  obtain ⟨L, hL⟩ := D.body.exists_gauge_sphere_lipschitz hC
  refine ⟨L, ?_⟩
  have heq : (fun v => centeredBallGauge r (D.coordinates v : X)) = D.body.gauge :=
    funext D.gauge_eq
  rwa [heq]

theorem RadialBallSection.gauge_pos {r : ℝ} {P : Submodule ℝ X} {d : ℕ}
    (D : RadialBallSection r P d) {x : P} (hx : (x : X) ≠ 0) :
    0 < centeredBallGauge r (x : X) := by
  have hv : D.coordinates.symm x ≠ 0 := by
    intro hz
    have hx0 := congrArg (fun v => (D.coordinates v : X)) hz
    apply hx
    simpa only [D.coordinates.apply_symm_apply, D.coordinates.map_zero, Submodule.coe_zero] using hx0
  have h := D.body.gauge_pos hv
  rw [← D.gauge_eq, D.coordinates.apply_symm_apply] at h
  exact h

theorem RadialBallSection.gauge_le_one_iff {r : ℝ} {P : Submodule ℝ X} {d : ℕ}
    (D : RadialBallSection r P d) (x : P) :
    centeredBallGauge r (x : X) ≤ 1 ↔ dist (x : X) 0 ≤ r := by
  rw [← D.coordinates.apply_symm_apply x, D.gauge_eq]
  have hmem : D.coordinates (D.coordinates.symm x) ∈ D.coordinates '' D.body.carrier ↔
      D.coordinates.symm x ∈ D.body.carrier := D.coordinates.injective.mem_set_image
  rw [D.carrier_image, D.body.carrier_eq_sublevel] at hmem
  exact hmem.symm

/-- The one-dimensional scalar sections in the paper suffice for positivity
and exact unit-sublevel recovery. Higher sections supply local regularity. -/
theorem centeredBallGauge_algebraic_of_radial_sections {r : ℝ} (hr : 0 < r)
    (hsection : ∀ x : X, x ≠ 0 → ∃ P : Submodule ℝ X, ∃ _hx : x ∈ P,
      ∃ d : ℕ, Nonempty (RadialBallSection r P d)) :
    AlgebraicPositiveHomogeneous (centeredBallGauge (X := X) r) ∧
      ∀ x : X, centeredBallGauge r x ≤ 1 ↔ dist x 0 ≤ r := by
  have hpositive (x : X) (hx : x ≠ 0) : 0 < centeredBallGauge r x := by
    obtain ⟨P, hPx, d, ⟨D⟩⟩ := hsection x hx
    exact D.gauge_pos (x := ⟨x, hPx⟩) hx
  refine ⟨⟨fun x => gauge_nonneg x, ?_, ?_⟩, ?_⟩
  · intro x
    constructor
    · intro hz
      by_contra hx
      exact (hpositive x hx).ne' hz
    · rintro rfl
      exact gauge_zero
  · intro t ht x
    exact gauge_smul_of_nonneg ht x
  · intro x
    by_cases hx : x = 0
    · subst x
      simp only [centeredBallGauge, gauge_zero, dist_self]
      exact ⟨fun _ => hr.le, fun _ => zero_le_one⟩
    · obtain ⟨P, hPx, d, ⟨D⟩⟩ := hsection x hx
      exact D.gauge_le_one_iff ⟨x, hPx⟩

end
end BanachIsometric.MetricGeometry

