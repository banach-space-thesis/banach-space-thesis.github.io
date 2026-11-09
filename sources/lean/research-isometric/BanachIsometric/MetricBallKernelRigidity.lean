import BanachIsometric.DivisionAlgebraGauge
import BanachIsometric.MetricGaugeIsometries
import BanachIsometric.SimilarityKernel

/-! A proper absolutely convex metric ball has a definite gauge under the
paper's scalar-linear fixed-dimensional metric homogeneity. The stable kernel
and the kernel-rigidity argument are constructed for real division algebras,
including opposite quaternions. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

variable {R X : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R]
    [AddCommGroup X] [Module R X] [Module ℝ X] [IsScalarTower ℝ R X]
    [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

def divisionAlgebraCenteredBallSeminorm (r : ℝ) (hr : 0 < r)
    (hb : Balanced R (Metric.closedBall (0 : X) r))
    (hc : Convex ℝ (Metric.closedBall (0 : X) r)) : Seminorm R X :=
  Seminorm.of (centeredBallGauge r) (gauge_add_le hc (centeredBall_absorbent hr))
    (centeredBallGauge_smul_divisionAlgebra hb)

variable (R) in
def seminormZeroSubmodule (p : Seminorm R X) : Submodule R X where
  carrier := {x | p x = 0}
  zero_mem' := map_zero p
  add_mem' {x y} hx hy := le_antisymm
    ((map_add_le_add p x y).trans (by rw [hx, hy, zero_add])) (apply_nonneg p _)
  smul_mem' a x hx := by change p (a • x) = 0; rw [map_smul_eq_mul, hx, mul_zero]

theorem centeredBallGauge_definite_of_linearMetric_homogeneity
    {n : ℕ} (hn : 1 ≤ n) (hdim : (n : Cardinal) < Module.rank R X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := R) (X := X) n)
    {r : ℝ} (hr : 0 < r) (hb : Balanced R (Metric.closedBall (0 : X) r))
    (hc : Convex ℝ (Metric.closedBall (0 : X) r))
    (hproper : Metric.closedBall (0 : X) r ≠ univ) :
    ∀ x : X, centeredBallGauge r x = 0 ↔ x = 0 := by
  let p := divisionAlgebraCenteredBallSeminorm r hr hb hc
  have hsim : ∀ E F : Submodule R X,
      Module.finrank R E = n → Module.finrank R F = n →
      ∃ T : E ≃ₗ[R] F, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p (T x : X) = c * p (x : X) := by
    intro E F hE hF
    obtain ⟨T, hT⟩ := hmetric E F hE hF
    exact ⟨T, 1, zero_lt_one, fun x => by
      simpa only [one_mul] using centeredBallGauge_preserved_scalar_subspace T hT r x⟩
  rcases zero_or_definite_of_subspace_similarities p (seminormZeroSubmodule R p)
    (fun _ => Iff.rfl) n hn hdim hsim with hzero | hdef
  · obtain ⟨x, hx⟩ := centeredBallGauge_nonzero_of_proper hr hc hproper
    exact False.elim (hx (hzero x))
  · exact hdef

end
end BanachIsometric.MetricGeometry
