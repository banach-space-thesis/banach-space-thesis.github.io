import BanachIsometric.UniversalSubdivisionBoundary

/-! Actual barycentric subdivision on arbitrary continuous singular chains
is a chain map, with the explicit actual subdivision homotopy. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable (X : Type*) [TopologicalSpace X]

theorem rawSubdivision_boundary (n : ℕ) :
    (rawBoundary n).comp (rawSubdivision X (n + 1)) =
      (rawSubdivision X n).comp (rawBoundary n) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  change rawBoundary n (rawSubdivision X (n + 1) (Finsupp.single simplex 1)) =
    rawSubdivision X n (rawBoundary n (Finsupp.single simplex 1))
  rw [rawSubdivision_single_one]
  have hmap := LinearMap.congr_fun (rawChainMap_boundary simplex n)
    (universalSingularSubdivision (n + 1))
  simp only [LinearMap.comp_apply] at hmap
  rw [hmap, universalSingularSubdivision_boundary, rawBoundary_single]
  simp only [map_sum, map_zsmul, rawSubdivision_single_one]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun c => (-1 : ℤ) ^ i.val • c)
    (LinearMap.congr_fun (rawChainMap_comp (face i) simplex n) (universalSingularSubdivision n)).symm

theorem rawSubdivisionHomotopy_identity (n : ℕ) :
    (rawBoundary (n + 1)).comp (rawSubdivisionHomotopy X (n + 1)) +
      (rawSubdivisionHomotopy X n).comp (rawBoundary n) =
        LinearMap.id - rawSubdivision X (n + 1) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  change rawBoundary (n + 1) (rawSubdivisionHomotopy X (n + 1) (Finsupp.single simplex 1)) +
      rawSubdivisionHomotopy X n (rawBoundary n (Finsupp.single simplex 1)) =
    Finsupp.single simplex 1 - rawSubdivision X (n + 1) (Finsupp.single simplex 1)
  rw [rawSubdivisionHomotopy_single_one, rawBoundary_single]
  simp only [map_sum, map_zsmul, rawSubdivisionHomotopy_single_one]
  have hmap := LinearMap.congr_fun (rawChainMap_boundary simplex (n + 1))
    (universalSingularSubdivisionHomotopy (n + 1))
  simp only [LinearMap.comp_apply] at hmap
  rw [hmap]
  have hface : (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        rawChainMap (simplex.comp (face i)) (n + 1) (universalSingularSubdivisionHomotopy n)) =
      rawChainMap simplex (n + 1) (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        rawChainMap (face i) (n + 1) (universalSingularSubdivisionHomotopy n)) := by
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun c => (-1 : ℤ) ^ i.val • c)
      (LinearMap.congr_fun (rawChainMap_comp (face i) simplex (n + 1))
        (universalSingularSubdivisionHomotopy n))
  rw [hface, ← map_add, universalSingularSubdivisionHomotopy_boundary, map_sub,
    rawSubdivision_single_one]
  congr 1
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ContinuousMap.comp_id]

theorem universalSingularSubdivisionHomotopy_zero : universalSingularSubdivisionHomotopy 0 = 0 := by
  change affineCarrierRealization (convex_stdSimplex ℝ (Fin 1)) 1 0 = 0
  exact map_zero _

theorem universalSingularSubdivision_zero :
    universalSingularSubdivision 0 = Finsupp.single (ContinuousMap.id (Simplex 0)) 1 := by
  apply rawChainMap_injective (affineCarrierInclusion (stdSimplex ℝ (Fin 1))) Subtype.val_injective 0
  rw [universalSingularSubdivision_ambient, universalIdentity_ambient]
  rfl

theorem rawSubdivisionHomotopy_zero : rawSubdivisionHomotopy X 0 = 0 := by
  apply Finsupp.lhom_ext
  intro simplex a
  simp only [rawSubdivisionHomotopy, Finsupp.linearCombination_single,
    universalSingularSubdivisionHomotopy_zero, map_zero, smul_zero, LinearMap.zero_apply]

theorem rawSubdivision_zero : rawSubdivision X 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro simplex a
  simp only [rawSubdivision, Finsupp.linearCombination_single, universalSingularSubdivision_zero,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ContinuousMap.comp_id,
    Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

theorem rawSubdivisionHomotopy_zero_identity :
    (rawBoundary 0).comp (rawSubdivisionHomotopy X 0) = LinearMap.id - rawSubdivision X 0 := by
  rw [rawSubdivisionHomotopy_zero, rawSubdivision_zero, LinearMap.comp_zero, sub_self]

end BanachIsometric.SingularPrism
