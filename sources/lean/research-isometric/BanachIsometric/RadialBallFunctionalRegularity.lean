import BanachIsometric.MetricStarBodyGauges
import BanachIsometric.QuaternionicFunctionalGeometry
import BanachIsometric.QuaternionicNormReduction

/-! Actual Lipschitz radial ball sections imply the auxiliary-coordinate
sphere regularity in the quaternionic functional theorem. The coordinate
change is allowed to be any real linear equivalence, as in the paper. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

theorem RadialBallSection.exists_gauge_lipschitz_in_coordinates
    {r : ℝ} {P : Submodule ℝ X} {d : ℕ} (D : RadialBallSection r P d)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : V ≃ₗ[ℝ] P) :
    ∃ L : ℝ≥0, LipschitzWith L (fun v : V => centeredBallGauge r (e v : X)) := by
  obtain ⟨C, hC⟩ := D.radius_lipschitz
  obtain ⟨L, hL⟩ := D.body.exists_gauge_lipschitz hC
  let f : V →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    LinearMap.toContinuousLinearMap (D.coordinates.symm.toLinearMap.comp e.toLinearMap)
  have heq : (fun v : V => centeredBallGauge r (e v : X)) = fun v => D.body.gauge (f v) := by
    funext v
    rw [← D.gauge_eq]
    exact congrArg (centeredBallGauge (X := X) r)
      (congrArg Subtype.val (D.coordinates.apply_symm_apply (e v))).symm
  rw [heq]
  exact ⟨L * ‖f‖₊, hL.comp f.lipschitz⟩

section Quaternionic

open Quaternionic
attribute [local instance] RestrictScalars.moduleOrig

variable [Module Hᵐᵒᵖ X] [IsScalarTower ℝ Hᵐᵒᵖ X]

theorem quaternionic_sphereLipschitz_of_radial_ball_sections {n : ℕ} {r : ℝ}
    (hsections : ∀ Y : Submodule Hᵐᵒᵖ X,
      Module.rank Hᵐᵒᵖ Y = ((n + 1 : ℕ) : Cardinal) →
      ∃ d : ℕ, Nonempty (RadialBallSection r (Y.restrictScalars ℝ) d)) :
    Quaternionic.SphereLipschitz n (centeredBallGauge (X := X) r) := by
  intro Y hY
  obtain ⟨d, ⟨D⟩⟩ := hsections Y hY
  letI : Module.Finite Hᵐᵒᵖ Y := Module.finite_of_rank_eq_nat hY
  letI : Module.Finite Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ Y) :=
    inferInstanceAs (Module.Finite Hᵐᵒᵖ Y)
  letI : Module.Finite ℝ (RestrictScalars ℝ Hᵐᵒᵖ Y) :=
    Module.Finite.trans Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ Y)
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 * (n + 1)))) =
      Module.finrank ℝ (RestrictScalars ℝ Hᵐᵒᵖ Y) := by
    rw [finrank_real_restrict, Module.finrank_eq_of_rank_eq hY]
    simp
  let e := LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin (4 * (n + 1))))
    (RestrictScalars ℝ Hᵐᵒᵖ Y) hd
  let er := e.trans (realSubmoduleCanonicalEquiv Y).symm
  obtain ⟨L, hL⟩ := D.exists_gauge_lipschitz_in_coordinates er
  exact ⟨e, L, hL.lipschitzOnWith⟩

end Quaternionic

end
end BanachIsometric.MetricGeometry

