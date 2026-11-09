import BanachIsometric.SphereRepetitionConeRegular
import BanachIsometric.SphereRepetitionAnchor
import BanachIsometric.SphereRegularValueDegree

/-! The actual cubical sphere repetition has its specified integer degree.
The computation uses one preserved positive regular fiber, rather than an
assumed degree-additivity law for cubical concatenation. -/

namespace BanachIsometric.SphereGenerator

open Set Metric
open scoped NNReal

theorem exists_lipschitz_sphereRepetition_with_positive_anchor (n d : ℕ) :
    ∃ G : C(Sph (n + 1), Sph (n + 1)), ∃ L : ℝ≥0, LipschitzWith L G ∧
      (∀ w, dist (G w) (sphereRepetition n d w) < (1 / 4 : ℝ)) ∧
      (∀ x, unitSphereCone G x = sphereRepetitionAnchor n →
        DifferentiableAt ℝ (unitSphereCone G) x ∧ 0 < (fderiv ℝ (unitSphereCone G) x).det) ∧
      Nat.card {x : EuclideanSpace ℝ (Fin (n + 2)) //
        x ∈ closedBall 0 1 ∧ unitSphereCone G x = sphereRepetitionAnchor n} = d :=
  exists_lipschitz_sphereRepetition_with_positive_anchor_of_positive_raw_germs n d
    (unitSphereCone_repetition_positive_on_axis_fiber n d (1 / 2) (by norm_num))

theorem continuousSphereSignedDegree_sphereRepetition (n d : ℕ) :
    continuousSphereSignedDegree (euclideanCoordinates (n + 2)) (sphereRepetition n d) = (d : ℤ) := by
  obtain ⟨G, L, hL, hclose, hreg, hcard⟩ :=
    exists_lipschitz_sphereRepetition_with_positive_anchor n d
  rw [continuousSphereSignedDegree_eq_of_lipschitz_approximation
    (euclideanCoordinates (n + 2)) (sphereRepetition n d) hL hclose]
  have hv : ‖sphereRepetitionAnchor n‖ < 1 := by rw [norm_sphereRepetitionAnchor]; norm_num
  rw [sphereSignedDegree_eq_natCard_of_positive_regular_value (euclideanCoordinates (n + 2)) hL hv
    (fun x _ hx => (hreg x hx).1) (fun x _ hx => (hreg x hx).2), hcard]

theorem exists_lipschitz_sphereRepetition_degree (n d : ℕ) :
    ∃ G : C(Sph (n + 1), Sph (n + 1)), ∃ L : ℝ≥0, LipschitzWith L G ∧
      (∀ w, dist (G w) (sphereRepetition n d w) < (1 / 4 : ℝ)) ∧
      sphereSignedDegree (euclideanCoordinates (n + 2)) G = (d : ℤ) ∧
      (∀ x, unitSphereCone G x = sphereRepetitionAnchor n →
        DifferentiableAt ℝ (unitSphereCone G) x ∧ 0 < (fderiv ℝ (unitSphereCone G) x).det) ∧
      Nat.card {x : EuclideanSpace ℝ (Fin (n + 2)) //
        x ∈ closedBall 0 1 ∧ unitSphereCone G x = sphereRepetitionAnchor n} = d := by
  obtain ⟨G, L, hL, hclose, hreg, hcard⟩ :=
    exists_lipschitz_sphereRepetition_with_positive_anchor n d
  refine ⟨G, L, hL, hclose, ?_, hreg, hcard⟩
  rw [← continuousSphereSignedDegree_eq_of_lipschitz_approximation
    (euclideanCoordinates (n + 2)) (sphereRepetition n d) hL hclose]
  exact continuousSphereSignedDegree_sphereRepetition n d

theorem continuousSphereSignedDegree_sphereRepetition_pos (n d : ℕ) (hd : 0 < d) :
    0 < continuousSphereSignedDegree (euclideanCoordinates (n + 2)) (sphereRepetition n d) := by
  rw [continuousSphereSignedDegree_sphereRepetition]
  exact_mod_cast hd

end BanachIsometric.SphereGenerator
