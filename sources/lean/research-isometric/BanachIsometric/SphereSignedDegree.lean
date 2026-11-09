import BanachIsometric.SphereConeCount
import BanachIsometric.SignedIndexNormalization
import BanachIsometric.AEConstantUniqueness

/-!
# Sphere degree from the classical actual signed-fiber definition

For a Lipschitz map of the genuine norm sphere, its degree is the canonical
local signed index of its norm-preserving cone. The degree is characterized
by actual signed counts on the original unit ball. Hence it is independent
of coordinates and of sufficiently large enclosing cubes. Identity,
orthogonal-map signs and homotopy invariance are proved below.

This is the analytic signed-fiber construction of degree. No singular-homology
map, degree axiom, or assumed degree invariance is used.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable def sphereSignedDegree {n : ℕ} [NeZero n]
    (e : V ≃L[ℝ] PiolaSpace n) (φ : sphere (0 : V) 1 → sphere (0 : V) 1) : ℤ :=
  sphereConeCubeIndex e φ (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1)

section Measures

variable [MeasurableSpace V] [BorelSpace V]

theorem ae_unitSphereCone_count_eq_sphereSignedDegree
    (μ : Measure V) [μ.IsAddHaarMeasure] {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ) :
    ∀ᵐ v ∂μ, v ∈ ball (0 : V) 1 →
      signedFiberCount (unitSphereCone φ) (fderiv ℝ (unitSphereCone φ))
        (closedBall (0 : V) 1) v = sphereSignedDegree e φ := by
  apply ae_unitSphereCone_count_eq_cubeIndex μ e hφ
  linarith

theorem sphereConeCubeIndex_eq_of_coordinates
    (μ : Measure V) [μ.IsAddHaarMeasure] {n m : ℕ} [NeZero n] [NeZero m]
    (e : V ≃L[ℝ] PiolaSpace n) (e' : V ≃L[ℝ] PiolaSpace m)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {R R' : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R)
    (hR' : ‖(e' : V →L[ℝ] PiolaSpace m)‖ < R') :
    sphereConeCubeIndex e φ R = sphereConeCubeIndex e' φ R' := by
  exact ae_constants_eq_on_balls μ (0 : V) zero_lt_one zero_lt_one
    (ae_unitSphereCone_count_eq_cubeIndex μ e hφ hR)
    (ae_unitSphereCone_count_eq_cubeIndex μ e' hφ hR')

theorem sphereSignedDegree_eq_of_coordinates
    {n m : ℕ} [NeZero n] [NeZero m]
    (e : V ≃L[ℝ] PiolaSpace n) (e' : V ≃L[ℝ] PiolaSpace m)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ) :
    sphereSignedDegree e φ = sphereSignedDegree e' φ := by
  let μ : Measure V := Measure.map e.symm volume
  letI : μ.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map volume
  exact sphereConeCubeIndex_eq_of_coordinates μ e e' hφ (by linarith) (by linarith)

theorem sphereConeCubeIndex_eq_sphereSignedDegree
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R) :
    sphereConeCubeIndex e φ R = sphereSignedDegree e φ := by
  let μ : Measure V := Measure.map e.symm volume
  letI : μ.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map volume
  exact sphereConeCubeIndex_eq_of_coordinates μ e e hφ hR (by linarith)

end Measures

omit [FiniteDimensional ℝ V] in
theorem unitSphereCone_id : unitSphereCone (id : sphere (0 : V) 1 → sphere (0 : V) 1) = id := by
  funext x
  by_cases hx : x = 0
  · simp [hx, unitSphereCone]
  rw [unitSphereCone, coneExtension_of_ne _ x hx]
  exact NormedSpace.norm_smul_normalize x

omit [FiniteDimensional ℝ V] in
theorem sphereSignedDegree_id {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n) :
    sphereSignedDegree e (id : sphere (0 : V) 1 → sphere (0 : V) 1) = 1 := by
  unfold sphereSignedDegree sphereConeCubeIndex
  rw [unitSphereCone_id]
  have he : coordinateMapConjugate e (id : V → V) = id := by funext x; exact e.apply_symm_apply x
  rw [he]
  apply localSignedIndex_id
  · apply coordinateCube_lower_le_upper
    positivity
  · apply zero_mem_interior_coordinateCube
    positivity

def sphereMapOfLinearIsometryEquiv (L : V ≃ₗᵢ[ℝ] V)
    (u : sphere (0 : V) 1) : sphere (0 : V) 1 :=
  ⟨L u.val, by simpa only [mem_sphere, dist_zero_right, L.norm_map] using u.property⟩

omit [FiniteDimensional ℝ V] in
theorem unitSphereCone_linearIsometryEquiv (L : V ≃ₗᵢ[ℝ] V) :
    unitSphereCone (sphereMapOfLinearIsometryEquiv L) = L := by
  funext x
  by_cases hx : x = 0
  · simp [hx, unitSphereCone]
  rw [unitSphereCone, coneExtension_of_ne _ x hx]
  change ‖x‖ • L (NormedSpace.normalize x) = L x
  rw [← map_smul, NormedSpace.norm_smul_normalize]

omit [FiniteDimensional ℝ V] in
theorem sphereSignedDegree_linearIsometryEquiv
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n) (L : V ≃ₗᵢ[ℝ] V) :
    sphereSignedDegree e (sphereMapOfLinearIsometryEquiv L) =
      (SignType.sign (L.toContinuousLinearEquiv : V →L[ℝ] V).det : ℤ) := by
  let T : PiolaSpace n ≃L[ℝ] PiolaSpace n := e.symm.trans (L.toContinuousLinearEquiv.trans e)
  have he : coordinateMapConjugate e (L : V → V) = (T : PiolaSpace n → PiolaSpace n) := rfl
  have hdet : (T : PiolaSpace n →L[ℝ] PiolaSpace n).det =
      (L.toContinuousLinearEquiv : V →L[ℝ] V).det := by
    have hd := det_fderiv_coordinateConjugate e (L : V → V) 0
    have hLfder : fderiv ℝ (L : V → V) 0 = (L.toContinuousLinearEquiv : V →L[ℝ] V) :=
      (show HasFDerivAt (L : V → V) (L.toContinuousLinearEquiv : V →L[ℝ] V) 0 from
        L.toContinuousLinearEquiv.hasFDerivAt).fderiv
    rw [he, map_zero, T.fderiv, hLfder] at hd
    exact hd
  unfold sphereSignedDegree sphereConeCubeIndex
  rw [unitSphereCone_linearIsometryEquiv, he]
  let R : ℝ := ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hzero := zero_mem_interior_coordinateCube n hR
  rw [localSignedIndex_linearEquiv T _ _ (coordinateCube_lower_le_upper n hR.le) 0 ?_ ?_, hdet]
  · rintro ⟨x, hx, hTx⟩
    have hx0 : x = 0 := T.injective (by simpa only [map_zero] using hTx)
    subst x
    rw [piolaBoxBoundary_eq_frontier, frontier] at hx
    exact hx.2 hzero
  · change (0 : PiolaSpace n) ∈ interior (T.toHomeomorph ''
      Icc (coordinateCubeLower n R) (coordinateCubeUpper n R))
    rw [← T.toHomeomorph.image_interior]
    exact ⟨0, hzero, map_zero T⟩

theorem sphereSignedDegree_homotopy_eq
    {P : Type*} [PseudoMetricSpace P] [CompactSpace P] [PreconnectedSpace P]
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (H : P → sphere (0 : V) 1 → sphere (0 : V) 1)
    (hH : Continuous (fun z : P × sphere (0 : V) 1 => H z.1 z.2))
    (hLip : ∀ p, ∃ C : ℝ≥0, LipschitzWith C (H p)) (p q : P) :
    sphereSignedDegree e (H p) = sphereSignedDegree e (H q) := by
  apply localSignedIndex_coordinate_cone_homotopy_of_zero_mem_interior e H hH hLip
  · apply coordinateCube_lower_le_upper
    positivity
  · apply zero_mem_interior_coordinateCube
    positivity

end BanachIsometric
