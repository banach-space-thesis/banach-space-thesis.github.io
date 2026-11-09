import BanachIsometric.SignedSimplexBoundaryMap
import BanachIsometric.SignedRayTransportDerivative
import BanachIsometric.SignedCoordinateTransport

/-! The affine ray chart is tied to the actual boundary sphere. The positive
scalar in the radial target chart is the ratio of the two Euclidean norms. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace SphereGenerator Filter
open scoped Topology NNReal

def signedFacetEuclidean (n : ℕ) (i : Fin (n + 3)) (x : Fin (n + 1) → ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm (signedFacetVector (n + 1) i x)

theorem signedFacetEuclidean_eq_centered (n : ℕ) (i : Fin (n + 3))
    (x : signedSimplexDomain (n + 1)) :
    signedFacetEuclidean n i x.val = centeredSimplexVector n
      (face i ((signedSimplexCoordinates (n + 1)).symm x)) := by
  ext j
  rw [centeredSimplexVector_apply]
  change signedFacetVector (n + 1) i x.val j = _
  rw [signedFacetVector_apply]
  change _ = (face i ((signedSimplexCoordinates (n + 1)).symm x)).val j.succ - simplexCenter n
  rw [signedFace_barycentric]
  rfl

def signedFacetFunction (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    (i : Fin (n + 3)) : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
  signedSimplexExtension (n + 1) (σ.comp (face i))

theorem signedFacetFunction_eq (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (i : Fin (n + 3)) (x : signedSimplexDomain (n + 1)) :
    signedFacetFunction n σ i x.val = σ (face i ((signedSimplexCoordinates (n + 1)).symm x)) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_face i
  exact (signedSimplexExtension_spec (n + 1) (σ.comp (face i)) ⟨L * K, hσ.comp hK⟩).2 x

def signedFacetRadialFactor (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    (i : Fin (n + 3)) (x : Fin (n + 1) → ℝ) : ℝ :=
  ‖signedFacetEuclidean n i x‖ / ‖signedUpperVector (n + 1) (signedFacetFunction n σ i x)‖

theorem signedFacetRadialFactor_pos (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    (i : Fin (n + 3)) (x : signedSimplexDomain (n + 1)) :
    0 < signedFacetRadialFactor n σ i x.val := by
  have hx : signedFacetEuclidean n i x.val ≠ 0 := by
    rw [signedFacetEuclidean_eq_centered]
    exact centeredSimplexVector_face_ne_zero n i _
  exact div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr (signedUpperVector_ne_zero _ _))

theorem signedFacetRay_actual_semiconjugacy (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (i : Fin (n + 3)) (x : signedSimplexDomain (n + 1)) {r : ℝ} (hr : 0 < r) :
    coordinateMapConjugate (EuclideanSpace.equiv (Fin (n + 2)) ℝ)
        (unitSphereCone (signedSimplexBoundaryMap n σ))
        (signedFacetRay (n + 1) i (Fin.cons r x.val)) =
      signedTargetRay (n + 1) (signedRayTransport (n + 1) (signedFacetRadialFactor n σ i)
        (signedFacetFunction n σ i) (Fin.cons r x.val)) := by
  let e := EuclideanSpace.equiv (Fin (n + 2)) ℝ
  let w := (signedSimplexCoordinates (n + 1)).symm x
  let b := boundarySimplexFaceInclusion n i w
  let v := signedFacetEuclidean n i x.val
  have hv : v ≠ 0 := by
    change signedFacetEuclidean n i x.val ≠ 0
    rw [signedFacetEuclidean_eq_centered]
    exact centeredSimplexVector_face_ne_zero n i w
  have hray : e.symm (signedFacetRay (n + 1) i (Fin.cons r x.val)) = r • v := by
    change e.symm (r • signedFacetVector (n + 1) i x.val) = r • v
    exact e.symm.map_smul r _
  have hne : r • v ≠ 0 := smul_ne_zero hr.ne' hv
  have hdir : coneDirection (r • v) hne = simplexBoundarySphereHomeomorph n b := by
    apply Subtype.ext
    rw [simplexBoundarySphereHomeomorph_apply_val]
    change normalize (r • v) = normalize (centeredSimplexVector n (face i w))
    rw [normalize_smul_of_pos hr]
    change normalize (signedFacetEuclidean n i x.val) = _
    rw [signedFacetEuclidean_eq_centered]
  have hval : (signedSimplexBoundaryMap n σ (simplexBoundarySphereHomeomorph n b)).val =
      normalize (signedUpperVector (n + 1) (signedFacetFunction n σ i x.val)) := by
    change (signedUpperSphere (n + 1)
      (σ (((simplexBoundarySphereHomeomorph n).symm (simplexBoundarySphereHomeomorph n b)).val))).val = _
    rw [Homeomorph.symm_apply_apply, signedFacetFunction_eq n σ hσ]
    rfl
  rw [coordinateMapConjugate, hray, unitSphereCone, coneExtension_of_ne _ _ hne, hdir, hval]
  rw [norm_smul, Real.norm_of_nonneg hr.le, NormedSpace.normalize, smul_smul, e.map_smul]
  change (r * ‖v‖ * ‖signedUpperVector (n + 1) (signedFacetFunction n σ i x.val)‖⁻¹) •
      Fin.cons (α := fun _ => ℝ) 1 (signedFacetFunction n σ i x.val) =
    (r * signedFacetRadialFactor n σ i x.val) • Fin.cons (α := fun _ => ℝ) 1 (signedFacetFunction n σ i x.val)
  congr 1
  unfold signedFacetRadialFactor
  rw [div_eq_mul_inv]
  change r * ‖v‖ * _ = r * (‖v‖ * _)
  ring

end BanachIsometric.SingularPrism
