import BanachIsometric.AffineSubdivisionHomotopy

/-! Subdivision and the explicit subdivision homotopy commute with actual
real linear maps. In particular they commute with every affine coordinate
face embedding of the universal standard simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

def affineVertexMap {E F : Type*} (f : E → F) (n : ℕ) :
    AffineRationalChains E n →ₗ[ℚ] AffineRationalChains F n :=
  Finsupp.lmapDomain ℚ ℚ (fun v => f ∘ v)

theorem affineVertexMap_single {E F : Type*} (f : E → F) (n : ℕ)
    (v : Fin (n + 1) → E) (a : ℚ) :
    affineVertexMap f n (Finsupp.single v a) = Finsupp.single (f ∘ v) a := by
  simp only [affineVertexMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem affineVertexMap_boundary {E F : Type*} (f : E → F) (n : ℕ) :
    (affineBoundary n).comp (affineVertexMap f (n + 1)) =
      (affineVertexMap f n).comp (affineBoundary n) := by
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, affineVertexMap_single, affineBoundary_single,
    map_sum, map_zsmul, Function.comp_assoc]

theorem affineVertexMap_cone {E F : Type*} (f : E → F) (b : E) (n : ℕ) :
    (affineVertexMap f (n + 1)).comp (affineCone b n) =
      (affineCone (f b) n).comp (affineVertexMap f n) := by
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, affineVertexMap_single, affineCone_single]
  congr 1
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ j => rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineBarycenter_map (f : E →ₗ[ℝ] F) {n : ℕ} (v : Fin (n + 1) → E) :
    affineBarycenter (f ∘ v) = f (affineBarycenter v) := by
  simp only [affineBarycenter, Function.comp_apply, map_smul, map_sum]

theorem affineSubdivision_natural (f : E →ₗ[ℝ] F) (n : ℕ) :
    (affineVertexMap f n).comp (affineSubdivision n) =
      (affineSubdivision n).comp (affineVertexMap f n) := by
  induction n with
  | zero => simp only [affineSubdivision, LinearMap.comp_id, LinearMap.id_comp]
  | succ n ih =>
    apply Finsupp.lhom_ext
    intro v a
    have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change affineVertexMap f (n + 1) (affineSubdivision (n + 1) (Finsupp.single v 1)) =
      affineSubdivision (n + 1) (affineVertexMap f (n + 1) (Finsupp.single v 1))
    rw [affineVertexMap_single, affineSubdivision_single, affineSubdivision_single,
      affineBarycenter_map]
    have hcone := LinearMap.congr_fun (affineVertexMap_cone f (affineBarycenter v) n)
      (affineSubdivision n (affineBoundary n (Finsupp.single v 1)))
    simp only [LinearMap.comp_apply] at hcone
    rw [hcone]
    congr 1
    have hSd := LinearMap.congr_fun ih (affineBoundary n (Finsupp.single v 1))
    have hd := LinearMap.congr_fun (affineVertexMap_boundary f n) (Finsupp.single v 1)
    simp only [LinearMap.comp_apply, affineVertexMap_single] at hSd hd
    rw [hSd, hd]

theorem affineSubdivisionHomotopy_natural (f : E →ₗ[ℝ] F) (n : ℕ) :
    (affineVertexMap f (n + 1)).comp (affineSubdivisionHomotopy n) =
      (affineSubdivisionHomotopy n).comp (affineVertexMap f n) := by
  induction n with
  | zero => simp only [affineSubdivisionHomotopy, LinearMap.comp_zero, LinearMap.zero_comp]
  | succ n ih =>
    apply Finsupp.lhom_ext
    intro v a
    have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change affineVertexMap f (n + 2) (affineSubdivisionHomotopy (n + 1) (Finsupp.single v 1)) =
      affineSubdivisionHomotopy (n + 1) (affineVertexMap f (n + 1) (Finsupp.single v 1))
    rw [affineVertexMap_single, affineSubdivisionHomotopy_single,
      affineSubdivisionHomotopy_single, affineBarycenter_map]
    have hcone := LinearMap.congr_fun (affineVertexMap_cone f (affineBarycenter v) (n + 1))
      (Finsupp.single v 1 - affineSubdivision (n + 1) (Finsupp.single v 1) -
        affineSubdivisionHomotopy n (affineBoundary n (Finsupp.single v 1)))
    simp only [LinearMap.comp_apply] at hcone
    rw [hcone]
    apply congrArg (affineCone (f (affineBarycenter v)) (n + 1))
    rw [map_sub, map_sub, affineVertexMap_single]
    congr 2
    · have h := LinearMap.congr_fun (affineSubdivision_natural f (n + 1)) (Finsupp.single v 1)
      simpa only [LinearMap.comp_apply, affineVertexMap_single] using h
    · have h := LinearMap.congr_fun ih (affineBoundary n (Finsupp.single v 1))
      have hd := LinearMap.congr_fun (affineVertexMap_boundary f n) (Finsupp.single v 1)
      simp only [LinearMap.comp_apply, affineVertexMap_single] at h hd
      rw [h, hd]

end BanachIsometric.SingularPrism
