import BanachIsometric.ExactFamilyCoordinates
import BanachIsometric.ContinuousSphereSignedDegree
import BanachIsometric.SphereSignedDegreeExcision

/-!
# Degree under genuine isometric changes of the ambient Euclidean space

Both source and target spheres are conjugated by the same actual real linear
isometry. Their norm cones conjugate exactly. The resulting local indices
agree, using the proved independence of every positive source-cube radius.
The continuous extension is transported by actual Lipschitz approximations.
-/

namespace BanachIsometric

open Metric
open scoped NNReal

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def isometricSphereConjugate (L : W ≃ₗᵢ[ℝ] V)
    (f : sphere (0 : V) 1 → sphere (0 : V) 1) :
    sphere (0 : W) 1 → sphere (0 : W) 1 :=
  fun z => linearIsometry_unitSphereMap L.symm (f (linearIsometry_unitSphereMap L z))

theorem lipschitzWith_isometricSphereConjugate (L : W ≃ₗᵢ[ℝ] V)
    {f : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (isometricSphereConjugate L f) := by
  simpa only [one_mul, mul_one] using
    ((linearIsometry_unitSphereMap_isometry L.symm).lipschitz.comp hf).comp
      (linearIsometry_unitSphereMap_isometry L).lipschitz

noncomputable def isometricSphereConjugateContinuous (L : W ≃ₗᵢ[ℝ] V)
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) :
    C(sphere (0 : W) 1, sphere (0 : W) 1) :=
  (linearIsometry_unitSphereMap L.symm).comp (f.comp (linearIsometry_unitSphereMap L))

theorem unitSphereCone_isometricSphereConjugate (L : W ≃ₗᵢ[ℝ] V)
    (f : sphere (0 : V) 1 → sphere (0 : V) 1) (x : W) :
    unitSphereCone (isometricSphereConjugate L f) x = L.symm (unitSphereCone f (L x)) := by
  by_cases hx : x = 0
  · simp [hx, unitSphereCone]
  have hLx : L x ≠ 0 := by
    intro h
    apply hx
    apply L.injective
    simpa only [map_zero] using h
  have hdir : linearIsometry_unitSphereMap L (coneDirection x hx) = coneDirection (L x) hLx := by
    apply Subtype.ext
    change L (NormedSpace.normalize x) = NormedSpace.normalize (L x)
    simp only [NormedSpace.normalize, map_smul, L.norm_map]
  rw [unitSphereCone, coneExtension_of_ne _ x hx]
  change ‖x‖ • L.symm (f (linearIsometry_unitSphereMap L (coneDirection x hx))).val = _
  rw [hdir, unitSphereCone, coneExtension_of_ne _ (L x) hLx, map_smul, L.norm_map]

theorem coordinate_unitSphereCone_isometricSphereConjugate
    {n : ℕ} (e : V ≃L[ℝ] PiolaSpace n) (L : W ≃ₗᵢ[ℝ] V)
    (f : sphere (0 : V) 1 → sphere (0 : V) 1) :
    coordinateMapConjugate (L.toContinuousLinearEquiv.trans e)
      (unitSphereCone (isometricSphereConjugate L f)) =
      coordinateMapConjugate e (unitSphereCone f) := by
  funext x
  simp only [coordinateMapConjugate, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_trans_apply, unitSphereCone_isometricSphereConjugate]
  change e (L (L.symm (unitSphereCone f (L (L.symm (e.symm x)))))) = _
  rw [L.apply_symm_apply, L.apply_symm_apply]

variable [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ W] in
theorem sphereSignedDegree_isometricSphereConjugate
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n) (L : W ≃ₗᵢ[ℝ] V)
    {f : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hf : LipschitzWith C f) :
    sphereSignedDegree (L.toContinuousLinearEquiv.trans e) (isometricSphereConjugate L f) =
      sphereSignedDegree e f := by
  change localSignedIndex
    (coordinateMapConjugate (L.toContinuousLinearEquiv.trans e)
      (unitSphereCone (isometricSphereConjugate L f))) _ _ 0 = _
  rw [coordinate_unitSphereCone_isometricSphereConjugate]
  apply sphereConeCubeIndex_eq_sphereSignedDegree_of_pos e hf
  positivity

theorem continuousSphereSignedDegree_isometricSphereConjugate
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n) (L : W ≃ₗᵢ[ℝ] V)
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) :
    continuousSphereSignedDegree (L.toContinuousLinearEquiv.trans e)
      (isometricSphereConjugateContinuous L f) = continuousSphereSignedDegree e f := by
  let r := chosenSphereLipschitzRepresentative f
  have hL := lipschitzWith_isometricSphereConjugate L r.lipschitz
  have hclose : ∀ z, dist (isometricSphereConjugate L r.map z)
      (isometricSphereConjugateContinuous L f z) < (1 / 4 : ℝ) := by
    intro z
    change dist (linearIsometry_unitSphereMap L.symm (r.map (linearIsometry_unitSphereMap L z)))
      (linearIsometry_unitSphereMap L.symm (f (linearIsometry_unitSphereMap L z))) < _
    rw [(linearIsometry_unitSphereMap_isometry L.symm).dist_eq]
    exact r.close _
  rw [continuousSphereSignedDegree_eq_of_lipschitz_approximation _ _ hL hclose,
    sphereSignedDegree_isometricSphereConjugate e L r.lipschitz]
  rfl

end BanachIsometric
