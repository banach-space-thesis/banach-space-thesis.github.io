import BanachIsometric.AffineRationalComplex

/-! Recursive barycentric subdivision of genuine affine chains. Each
simplex is coned from its actual barycenter over the subdivided boundary.
The actual cone identity proves this commutes with the boundary. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineBarycenter {n : ℕ} (v : Fin (n + 1) → E) : E :=
  (n + 1 : ℝ)⁻¹ • ∑ i, v i

def affineSubdivision : (n : ℕ) → AffineRationalChains E n →ₗ[ℚ] AffineRationalChains E n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℚ (fun v =>
      affineCone (affineBarycenter v) n
        (affineSubdivision n (affineBoundary n (Finsupp.single v 1))))

theorem affineSubdivision_single (n : ℕ) (v : Fin (n + 2) → E) :
    affineSubdivision (n + 1) (Finsupp.single v 1) =
      affineCone (affineBarycenter v) n
        (affineSubdivision n (affineBoundary n (Finsupp.single v 1))) := by
  simp only [affineSubdivision, Finsupp.linearCombination_single, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem affineBoundary_cone_apply (b : E) (n : ℕ) (c : AffineRationalChains E (n + 1)) :
    affineBoundary (n + 1) (affineCone b (n + 1) c) =
      c - affineCone b n (affineBoundary n c) := by
  have h := LinearMap.congr_fun (affineBoundary_cone b n) c
  exact eq_sub_iff_add_eq.mpr h

theorem affineSubdivision_boundary (n : ℕ) :
    (affineBoundary (E := E) n).comp (affineSubdivision (n + 1)) =
      (affineSubdivision n).comp (affineBoundary n) := by
  induction n with
  | zero =>
    apply Finsupp.lhom_ext
    intro v a
    have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change affineBoundary 0 (affineSubdivision 1 (Finsupp.single v 1)) =
      affineBoundary 0 (Finsupp.single v 1)
    rw [affineSubdivision_single, affineSubdivision, LinearMap.id_apply,
      affineBoundary_cone_zero]
    have hz := LinearMap.congr_fun (affineAugmentation_boundary E) (Finsupp.single v 1)
    change affineAugmentation E (affineBoundary 0 (Finsupp.single v 1)) = 0 at hz
    rw [hz, Finsupp.single_zero, sub_zero]
  | succ n ih =>
    apply Finsupp.lhom_ext
    intro v a
    have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change affineBoundary (n + 1) (affineSubdivision (n + 2) (Finsupp.single v 1)) =
      affineSubdivision (n + 1) (affineBoundary (n + 1) (Finsupp.single v 1))
    rw [affineSubdivision_single, affineBoundary_cone_apply]
    have hz : affineBoundary n (affineSubdivision (n + 1)
        (affineBoundary (n + 1) (Finsupp.single v 1))) = 0 := by
      have h := LinearMap.congr_fun ih (affineBoundary (n + 1) (Finsupp.single v 1))
      simp only [LinearMap.comp_apply] at h
      rw [h]
      have hsq := LinearMap.congr_fun (affineBoundary_squared (E := E) n) (Finsupp.single v 1)
      change affineBoundary n (affineBoundary (n + 1) (Finsupp.single v 1)) = 0 at hsq
      rw [hsq, map_zero]
    rw [hz, map_zero, sub_zero]

end BanachIsometric.SingularPrism
