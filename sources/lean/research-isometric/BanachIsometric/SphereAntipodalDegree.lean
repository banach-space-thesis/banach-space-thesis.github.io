import BanachIsometric.ContinuousSphereSignedDegree
import BanachIsometric.SphereHomotopy
import Mathlib.Topology.Algebra.Module.Determinant

/-! The actual antipodal degree and the real even-sphere tangent-field
obstruction, proved from the project's constructed analytic signed degree.
No Euler class, Gromov theorem or homotopy-group nonvanishing is assumed. -/

namespace BanachIsometric

open Metric
open scoped Topology NNReal

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def antipodalSphereMap : C(sphere (0 : V) 1, sphere (0 : V) 1) := by
  refine ⟨fun u => ⟨-u.val, ?_⟩, ?_⟩
  · simpa only [mem_sphere, dist_zero_right, norm_neg] using u.property
  · exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

omit [NormedSpace ℝ V] in
theorem antipodalSphereMap_lipschitz : LipschitzWith 1 (antipodalSphereMap (V := V)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (-x.val) (-y.val) ≤ (1 : ℝ) * dist x.val y.val
  rw [dist_neg_neg, one_mul]

variable [FiniteDimensional ℝ V]

theorem continuousSphereSignedDegree_antipodal_of_odd_finrank
    {N : ℕ} [NeZero N] (e : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V)) :
    continuousSphereSignedDegree e (antipodalSphereMap (V := V)) = -1 := by
  rw [continuousSphereSignedDegree_eq_sphereSignedDegree e _ antipodalSphereMap_lipschitz]
  have heq : (antipodalSphereMap (V := V) : sphere (0 : V) 1 → sphere (0 : V) 1) =
      sphereMapOfLinearIsometryEquiv (LinearIsometryEquiv.neg ℝ) := rfl
  rw [heq, sphereSignedDegree_linearIsometryEquiv]
  have hL : (LinearIsometryEquiv.neg ℝ : V ≃ₗᵢ[ℝ] V).toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap =
      (-1 : ℝ) • (LinearMap.id : V →ₗ[ℝ] V) := by
    apply LinearMap.ext
    intro x
    change -x = (-1 : ℝ) • x
    rw [neg_one_smul]
  change (SignType.sign (LinearMap.det _): ℤ) = -1
  rw [hL, LinearMap.det_smul, LinearMap.det_id, hOdd.neg_one_pow, mul_one]
  norm_num

theorem not_homotopic_id_antipodal_of_odd_finrank
    {N : ℕ} [NeZero N] (e : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V)) :
    ¬ ContinuousMap.Homotopic (ContinuousMap.id (sphere (0 : V) 1)) (antipodalSphereMap (V := V)) := by
  intro h
  have hd := continuousSphereSignedDegree_eq_of_homotopic e h
  rw [continuousSphereSignedDegree_id, continuousSphereSignedDegree_antipodal_of_odd_finrank e hOdd] at hd
  norm_num at hd

variable [InnerProductSpace ℝ V]

theorem no_unit_tangent_sphere_map_of_odd_finrank
    {N : ℕ} [NeZero N] (e : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V))
    (w : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hTangent : ∀ u, inner ℝ u.val (w u).val = 0) : False := by
  have h₁ : ContinuousMap.Homotopic (ContinuousMap.id (sphere (0 : V) 1)) w :=
    orthogonal_sphere_maps_homotopic _ _ hTangent
  have h₂ : ContinuousMap.Homotopic w (antipodalSphereMap (V := V)) := by
    apply orthogonal_sphere_maps_homotopic
    intro u
    change inner ℝ (w u).val (-u.val) = 0
    rw [inner_neg_right]
    exact neg_eq_zero.mpr ((real_inner_comm _ _).trans (hTangent u))
  exact not_homotopic_id_antipodal_of_odd_finrank e hOdd (h₁.trans h₂)

end
end BanachIsometric
