import BanachIsometric.SphereSignedDegree
import BanachIsometric.SignedCountPositive

/-!
# Computing actual sphere degree from positive regular fibers on an open target

An actual nonnull open set of positive finite fibers computes the degree.
The hypotheses concern the genuine fibers and actual derivatives; no degree
or additivity property is assumed.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem sphereSignedDegree_eq_of_count_on_open
    (μ : Measure V) [μ.IsAddHaarMeasure] {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ ball (0 : V) 1) (d : ℤ)
    (hcount : ∀ᵐ y ∂μ, y ∈ U → signedFiberCount (unitSphereCone φ)
      (fderiv ℝ (unitSphereCone φ)) (closedBall (0 : V) 1) y = d) :
    sphereSignedDegree e φ = d := by
  obtain ⟨u, hu⟩ := hne
  have hnon : μ (ball (0 : V) 1 ∩ U) ≠ 0 :=
    (isOpen_ball.inter hU).measure_ne_zero μ ⟨u, hsub hu, hu⟩
  exact ae_constants_eq_of_nonnull_inter μ hnon
    (ae_unitSphereCone_count_eq_sphereSignedDegree μ e hφ) hcount

theorem sphereSignedDegree_eq_of_finite_positive_fibers
    (μ : Measure V) [μ.IsAddHaarMeasure] {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ ball (0 : V) 1) (d : ℕ)
    (hfin : ∀ y ∈ U, {x : V | x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = y}.Finite)
    (hcard : ∀ y ∈ U, Nat.card {x : V // x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = y} = d)
    (hpos : ∀ y ∈ U, ∀ x ∈ closedBall (0 : V) 1,
      unitSphereCone φ x = y → 0 < (fderiv ℝ (unitSphereCone φ) x).det) :
    sphereSignedDegree e φ = (d : ℤ) := by
  apply sphereSignedDegree_eq_of_count_on_open μ e hφ hU hne hsub
  apply ae_of_all
  intro y hy
  rw [signedFiberCount_eq_card_of_pos_det (unitSphereCone φ)
    (fderiv ℝ (unitSphereCone φ)) _ y (hfin y hy) (hpos y hy), hcard y hy]

end BanachIsometric
