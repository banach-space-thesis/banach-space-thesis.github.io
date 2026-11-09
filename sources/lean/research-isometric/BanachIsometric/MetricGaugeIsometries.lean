import BanachIsometric.MetricBallGauge
import BanachIsometric.HermitianGlobalProportionality

/-! The original scalar-linear metric isometries preserve every actual ball
Minkowski functional simultaneously. Scalars may form a noncommutative real
algebra, so this includes the paper's right quaternionic convention. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

variable {R X : Type*} [DivisionRing R] [AddCommGroup X] [Module R X] [MetricSpace X]

/-- Theorem E's linear metric hypothesis; scalar-linearity is part of it. -/
def LinearMetricSubspaceHomogeneity (n : ℕ) : Prop :=
  ∀ E F : Submodule R X, Module.finrank R E = n → Module.finrank R F = n →
    ∃ T : E ≃ₗ[R] F, Isometry T

variable [Algebra ℝ R] [Module ℝ X] [IsScalarTower ℝ R X]

def realRestrictedSubspaceEquiv {E F : Submodule R X} (T : E ≃ₗ[R] F) :
    E.restrictScalars ℝ ≃ₗ[ℝ] F.restrictScalars ℝ :=
  ((E.restrictScalarsEquiv ℝ).trans (T.trans (F.restrictScalarsEquiv ℝ).symm)).restrictScalars ℝ

theorem centeredBallGauge_preserved_scalar_subspace {E F : Submodule R X}
    (T : E ≃ₗ[R] F) (hT : Isometry T) (r : ℝ) (x : E) :
    centeredBallGauge r (T x : X) = centeredBallGauge r (x : X) := by
  let Tℝ := realRestrictedSubspaceEquiv T
  have hTℝ : Isometry Tℝ := by
    apply Isometry.of_dist_eq
    intro a b
    exact hT.dist_eq ((E.restrictScalarsEquiv ℝ) a) ((E.restrictScalarsEquiv ℝ) b)
  have h := centeredBallGauge_preserved Tℝ hTℝ r ((E.restrictScalarsEquiv ℝ).symm x)
  rw [centeredBallGauge_submodule, centeredBallGauge_submodule] at h
  exact h

theorem LinearMetricSubspaceHomogeneity.simultaneous_ball_gauges {n : ℕ}
    (h : LinearMetricSubspaceHomogeneity (R := R) (X := X) n) (r s : ℝ) :
    SimultaneousPairSimilarities (𝕜 := R) n (centeredBallGauge (X := X) r) (centeredBallGauge s) := by
  intro E F hE hF
  obtain ⟨T, hT⟩ := h E F hE hF
  refine ⟨T, 1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
  · intro x
    simpa only [one_mul] using centeredBallGauge_preserved_scalar_subspace T hT r x
  · intro x
    simpa only [one_mul] using centeredBallGauge_preserved_scalar_subspace T hT s x

end
end BanachIsometric.MetricGeometry

namespace BanachIsometric

noncomputable section

variable {R X Y : Type*} [DivisionRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]

/-- Algebraic transport of the same simultaneous similarities. -/
theorem SimultaneousPairSimilarities.map {n : ℕ} {p q : X → ℝ}
    (h : SimultaneousPairSimilarities (𝕜 := R) n p q) (e : X ≃ₗ[R] Y) :
    SimultaneousPairSimilarities (𝕜 := R) n (fun y => p (e.symm y)) (fun y => q (e.symm y)) := by
  intro E F hE hF
  let E' := E.comap e.toLinearMap
  let F' := F.comap e.toLinearMap
  let eE : E' ≃ₗ[R] E := e.ofSubmodule' E
  let eF : F' ≃ₗ[R] F := e.ofSubmodule' F
  obtain ⟨T, c₁, c₂, hc₁, hc₂, hp, hq⟩ := h E' F' (eE.finrank_eq.trans hE) (eF.finrank_eq.trans hF)
  let U : E ≃ₗ[R] F := eE.symm.trans (T.trans eF)
  have hval (x : E) : e.symm (U x : Y) = (T (eE.symm x) : X) := by
    change e.symm (e (T (eE.symm x) : X)) = _
    exact e.symm_apply_apply _
  refine ⟨U, c₁, c₂, hc₁, hc₂, ?_, ?_⟩
  · intro x
    change p (e.symm (U x : Y)) = c₁ * p (e.symm (x : Y))
    rw [hval]
    exact hp (eE.symm x)
  · intro x
    change q (e.symm (U x : Y)) = c₂ * q (e.symm (x : Y))
    rw [hval]
    exact hq (eE.symm x)

end
end BanachIsometric

