import BanachIsometric.MetricGaugeIsometries

/-! Passing actual scalar-linear isometries of the original metric to the
norm defined by an actual ball gauge. This uses no Mazur--Ulam theorem and
preserves scalar-linearity, including right quaternionic linearity. -/

namespace BanachIsometric.MetricGeometry

noncomputable section

variable {R X V : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R]
    [AddCommGroup X] [Module R X] [Module ℝ X] [IsScalarTower ℝ R X] [MetricSpace X]
    [NormedAddCommGroup V] [Module R V]

theorem linearIsometry_subspaces_of_metric_ballGauge {n : ℕ}
    (hmetric : LinearMetricSubspaceHomogeneity (R := R) (X := X) n)
    (r : ℝ) (e : X ≃ₗ[R] V) (hnorm : ∀ x : X, ‖e x‖ = centeredBallGauge r x)
    (E F : Submodule R V) (hE : Module.finrank R E = n) (hF : Module.finrank R F = n) :
    Nonempty (E ≃ₗᵢ[R] F) := by
  let E' := E.comap e.toLinearMap
  let F' := F.comap e.toLinearMap
  let eE : E' ≃ₗ[R] E := e.ofSubmodule' E
  let eF : F' ≃ₗ[R] F := e.ofSubmodule' F
  obtain ⟨T, hT⟩ := hmetric E' F' (eE.finrank_eq.trans hE) (eF.finrank_eq.trans hF)
  let U : E ≃ₗ[R] F := eE.symm.trans (T.trans eF)
  have hval (x : E) : (U x : V) = e (T (eE.symm x) : X) := rfl
  have hback (x : E) : e (eE.symm x : X) = (x : V) := e.apply_symm_apply x.val
  refine ⟨{ U with norm_map' := ?_ }⟩
  intro x
  change ‖(U x : V)‖ = ‖(x : V)‖
  rw [hval, hnorm, centeredBallGauge_preserved_scalar_subspace T hT r]
  rw [← hnorm, hback]

end
end BanachIsometric.MetricGeometry
