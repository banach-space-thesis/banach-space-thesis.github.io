import BanachIsometric.AffineBarycentricSubdivision

/-! An explicit chain homotopy from affine barycentric subdivision to the
identity. The filling is a literal cone in the same affine simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineSubdivisionHomotopy :
    (n : ℕ) → AffineRationalChains E n →ₗ[ℚ] AffineRationalChains E (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℚ (fun v =>
      affineCone (affineBarycenter v) (n + 1)
        (Finsupp.single v 1 - affineSubdivision (n + 1) (Finsupp.single v 1) -
          affineSubdivisionHomotopy n (affineBoundary n (Finsupp.single v 1))))

theorem affineSubdivisionHomotopy_single (n : ℕ) (v : Fin (n + 2) → E) :
    affineSubdivisionHomotopy (n + 1) (Finsupp.single v 1) =
      affineCone (affineBarycenter v) (n + 1)
        (Finsupp.single v 1 - affineSubdivision (n + 1) (Finsupp.single v 1) -
          affineSubdivisionHomotopy n (affineBoundary n (Finsupp.single v 1))) := by
  simp only [affineSubdivisionHomotopy, Finsupp.linearCombination_single, one_smul]

theorem affineSubdivisionHomotopy_identity (n : ℕ) :
    (affineBoundary (E := E) (n + 1)).comp (affineSubdivisionHomotopy (n + 1)) +
      (affineSubdivisionHomotopy n).comp (affineBoundary n) =
        LinearMap.id - affineSubdivision (n + 1) := by
  induction n with
  | zero =>
    apply Finsupp.lhom_ext
    intro v a
    have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change affineBoundary 1 (affineSubdivisionHomotopy 1 (Finsupp.single v 1)) +
      affineSubdivisionHomotopy 0 (affineBoundary 0 (Finsupp.single v 1)) =
        Finsupp.single v 1 - affineSubdivision 1 (Finsupp.single v 1)
    rw [affineSubdivisionHomotopy_single, affineBoundary_cone_apply]
    have hcycle : affineBoundary 0 (Finsupp.single v 1 -
        affineSubdivision 1 (Finsupp.single v 1) -
        affineSubdivisionHomotopy 0 (affineBoundary 0 (Finsupp.single v 1))) = 0 := by
      have h := LinearMap.congr_fun (affineSubdivision_boundary (E := E) 0) (Finsupp.single v 1)
      change affineBoundary 0 (affineSubdivision 1 (Finsupp.single v 1)) =
        affineBoundary 0 (Finsupp.single v 1) at h
      simp only [map_sub, affineSubdivisionHomotopy, LinearMap.zero_apply,
        sub_zero, h, sub_self]
    rw [hcycle, map_zero, sub_zero]
    simp only [affineSubdivisionHomotopy, LinearMap.zero_apply, sub_zero, add_zero]
  | succ n ih =>
    apply Finsupp.lhom_ext
    intro v a
    have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change affineBoundary (n + 2) (affineSubdivisionHomotopy (n + 2) (Finsupp.single v 1)) +
      affineSubdivisionHomotopy (n + 1) (affineBoundary (n + 1) (Finsupp.single v 1)) =
        Finsupp.single v 1 - affineSubdivision (n + 2) (Finsupp.single v 1)
    rw [affineSubdivisionHomotopy_single, affineBoundary_cone_apply]
    have hcycle : affineBoundary (n + 1) (Finsupp.single v 1 -
        affineSubdivision (n + 2) (Finsupp.single v 1) -
        affineSubdivisionHomotopy (n + 1) (affineBoundary (n + 1) (Finsupp.single v 1))) = 0 := by
      have hSd := LinearMap.congr_fun (affineSubdivision_boundary (E := E) (n + 1))
        (Finsupp.single v 1)
      have hT := LinearMap.congr_fun ih (affineBoundary (n + 1) (Finsupp.single v 1))
      have hsq := LinearMap.congr_fun (affineBoundary_squared (E := E) n) (Finsupp.single v 1)
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.zero_apply] at hSd hT hsq
      rw [hsq, map_zero, add_zero] at hT
      simp only [map_sub]
      rw [hSd, hT, sub_self]
    rw [hcycle, map_zero, sub_zero]
    abel

theorem affineSubdivisionHomotopy_zero_identity :
    (affineBoundary (E := E) 0).comp (affineSubdivisionHomotopy 0) =
      LinearMap.id - affineSubdivision 0 := by
  simp only [affineSubdivisionHomotopy, affineSubdivision, LinearMap.comp_zero, sub_self]

end BanachIsometric.SingularPrism
