import BanachIsometric.SignedSimplexFacetFibers
import BanachIsometric.UnitSphereConeFibers

/-! The actual cone fiber at the half-unit upper direction is the disjoint
union of the actual regular facet fibers. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace SphereGenerator
open scoped NNReal Topology

def signedSimplexConeTarget (n : ℕ) (y : Fin (n + 1) → ℝ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 / 2 : ℝ) • (signedUpperSphere (n + 1) y).val

theorem norm_signedSimplexConeTarget (n : ℕ) (y : Fin (n + 1) → ℝ) :
    ‖signedSimplexConeTarget n y‖ = 1 / 2 := by
  rw [signedSimplexConeTarget, norm_smul, norm_eq_of_mem_sphere (signedUpperSphere (n + 1) y)]
  norm_num

theorem signedSimplexConeTarget_ne_zero (n : ℕ) (y : Fin (n + 1) → ℝ) :
    signedSimplexConeTarget n y ≠ 0 := by
  intro hz
  have hn := norm_signedSimplexConeTarget n y
  rw [hz, norm_zero] at hn
  norm_num at hn

theorem signedSimplexConeTarget_direction (n : ℕ) (y : Fin (n + 1) → ℝ) :
    coneDirection (signedSimplexConeTarget n y) (signedSimplexConeTarget_ne_zero n y) =
      signedUpperSphere (n + 1) y := by
  apply Subtype.ext
  change normalize ((1 / 2 : ℝ) • (signedUpperSphere (n + 1) y).val) = _
  rw [normalize_smul_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere _)

abbrev SignedBoundaryConeFiber (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) (y : Fin (n + 1) → ℝ) :=
  {v : EuclideanSpace ℝ (Fin (n + 2)) // v ∈ closedBall 0 1 ∧
    unitSphereCone (signedSimplexBoundaryMap n σ) v = signedSimplexConeTarget n y}

def signedBoundarySphereFiberEquiv (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) (y : Fin (n + 1) → ℝ) :
    SignedBoundaryFiber n σ y ≃ {u : Sph (n + 1) //
      signedSimplexBoundaryMap n σ u = signedUpperSphere (n + 1) y} where
  toFun w := ⟨simplexBoundarySphereHomeomorph n w.val, by
    simp only [signedSimplexBoundaryMap, Homeomorph.symm_apply_apply, w.property]⟩
  invFun u := ⟨(simplexBoundarySphereHomeomorph n).symm u.val,
    signedUpperSphere_injective (n + 1) u.property⟩
  left_inv w := Subtype.ext ((simplexBoundarySphereHomeomorph n).symm_apply_apply w.val)
  right_inv u := Subtype.ext ((simplexBoundarySphereHomeomorph n).apply_symm_apply u.val)

def signedSphereConeFiberEquiv (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) (y : Fin (n + 1) → ℝ) :
    {u : Sph (n + 1) // signedSimplexBoundaryMap n σ u = signedUpperSphere (n + 1) y} ≃
      SignedBoundaryConeFiber n σ y :=
  (Equiv.subtypeEquivRight (fun u : Sph (n + 1) => by
    rw [signedSimplexConeTarget_direction n y])).trans
      (unitSphereConeFiberEquiv (signedSimplexBoundaryMap n σ) (signedSimplexConeTarget n y)
        (signedSimplexConeTarget_ne_zero n y) (by rw [norm_signedSimplexConeTarget]; norm_num)).symm

def signedFacetConeFiberEquiv (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (y : Fin (n + 1) → ℝ)
    (hinter : ∀ i (x : SignedFacetFiber n σ i y), x.val.val ∈ interior (signedSimplexDomain (n + 1))) :
    (Σ i : Fin (n + 3), SignedFacetFiber n σ i y) ≃ SignedBoundaryConeFiber n σ y :=
  (signedFacetBoundaryFiberEquiv n σ hσ y hinter).trans
    ((signedBoundarySphereFiberEquiv n σ y).trans (signedSphereConeFiberEquiv n σ y))

theorem signedFacetConeFiberEquiv_apply (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (y : Fin (n + 1) → ℝ)
    (hinter : ∀ i (x : SignedFacetFiber n σ i y), x.val.val ∈ interior (signedSimplexDomain (n + 1)))
    (a : Σ i : Fin (n + 3), SignedFacetFiber n σ i y) :
    (signedFacetConeFiberEquiv n σ hσ y hinter a).val =
      ((1 / 2 : ℝ) / ‖signedFacetEuclidean n a.1 a.2.val.val‖) •
        signedFacetEuclidean n a.1 a.2.val.val := by
  change ‖signedSimplexConeTarget n y‖ •
    (simplexBoundarySphereHomeomorph n
      (boundarySimplexFaceInclusion n a.1 ((signedSimplexCoordinates (n + 1)).symm a.2.val))).val = _
  rw [norm_signedSimplexConeTarget, simplexBoundarySphereHomeomorph_apply_val]
  change (1 / 2 : ℝ) • NormedSpace.normalize (centeredSimplexVector n
    (face a.1 ((signedSimplexCoordinates (n + 1)).symm a.2.val))) = _
  rw [← signedFacetEuclidean_eq_centered]
  simp only [NormedSpace.normalize, smul_smul, div_eq_mul_inv]

end BanachIsometric.SingularPrism
