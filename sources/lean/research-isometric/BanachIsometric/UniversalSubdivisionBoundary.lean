import BanachIsometric.UniversalSubdivisionFaces

/-! The actual universal subdivision chains have exactly the subdivided
boundary. Their explicit homotopy has boundary identity minus subdivision.
All equations are in genuine singular chains of the standard simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

theorem affineStandardSimplex_inclusion (n : ℕ) :
    affineSingularSimplex (simplexStandardVertices n) =
      affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1))) := by
  classical
  apply ContinuousMap.ext
  intro w
  funext i
  change (∑ j, w j • simplexStandardVertices n j) i = w.val i
  rw [Finset.sum_apply]
  change (∑ j, w.val j * (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) i) = w.val i
  simp [Pi.single_apply]

theorem universalIdentity_ambient (n : ℕ) :
    rawChainMap (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))) n
        (Finsupp.single (ContinuousMap.id (Simplex n)) 1) =
      affineChainRealization n (Finsupp.single (simplexStandardVertices n) 1) := by
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    affineChainRealization_single, affineStandardSimplex_inclusion, ContinuousMap.comp_id]

theorem universalSingularSubdivision_boundary (n : ℕ) :
    rawBoundary n (universalSingularSubdivision (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        rawChainMap (face i) n (universalSingularSubdivision n) := by
  let incl := affineCarrierInclusion (stdSimplex ℝ (Fin (n + 2)))
  apply rawChainMap_injective incl Subtype.val_injective n
  have hmap := LinearMap.congr_fun (rawChainMap_boundary incl n)
    (universalSingularSubdivision (n + 1))
  have hreal := LinearMap.congr_fun (affineChainRealization_boundary n)
    (affineSubdivision (n + 1) (Finsupp.single (simplexStandardVertices (n + 1)) 1))
  have hSd := LinearMap.congr_fun (affineSubdivision_boundary n)
    (Finsupp.single (simplexStandardVertices (n + 1)) 1)
  simp only [LinearMap.comp_apply] at hmap hreal hSd
  calc
    _ = rawBoundary n (rawChainMap incl (n + 1) (universalSingularSubdivision (n + 1))) := hmap.symm
    _ = rawBoundary n (affineChainRealization (n + 1)
        (affineSubdivision (n + 1) (Finsupp.single (simplexStandardVertices (n + 1)) 1))) := by
      rw [universalSingularSubdivision_ambient]
    _ = affineChainRealization n (affineBoundary n
        (affineSubdivision (n + 1) (Finsupp.single (simplexStandardVertices (n + 1)) 1))) := hreal
    _ = affineChainRealization n (affineSubdivision n
        (affineBoundary n (Finsupp.single (simplexStandardVertices (n + 1)) 1))) :=
      congrArg (affineChainRealization n) hSd
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        affineChainRealization n (affineSubdivision n
          (Finsupp.single (simplexStandardVertices (n + 1) ∘ i.succAbove) 1)) := by
      rw [affineBoundary_single]
      simp only [map_sum, map_zsmul]
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        rawChainMap incl n (rawChainMap (face i) n (universalSingularSubdivision n)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun c => (-1 : ℤ) ^ i.val • c) (universalSingularSubdivision_face_ambient i).symm
    _ = _ := by simp only [map_sum, map_zsmul]

theorem universalSingularSubdivisionHomotopy_boundary (n : ℕ) :
    rawBoundary (n + 1) (universalSingularSubdivisionHomotopy (n + 1)) +
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        rawChainMap (face i) (n + 1) (universalSingularSubdivisionHomotopy n) =
      Finsupp.single (ContinuousMap.id (Simplex (n + 1))) 1 -
        universalSingularSubdivision (n + 1) := by
  let incl := affineCarrierInclusion (stdSimplex ℝ (Fin (n + 2)))
  apply rawChainMap_injective incl Subtype.val_injective (n + 1)
  have hmap := LinearMap.congr_fun (rawChainMap_boundary incl (n + 1))
    (universalSingularSubdivisionHomotopy (n + 1))
  have hreal := LinearMap.congr_fun (affineChainRealization_boundary (n + 1))
    (affineSubdivisionHomotopy (n + 1) (Finsupp.single (simplexStandardVertices (n + 1)) 1))
  have hT := LinearMap.congr_fun (affineSubdivisionHomotopy_identity (E := Fin (n + 2) → ℝ) n)
    (Finsupp.single (simplexStandardVertices (n + 1)) 1)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
    at hmap hreal hT
  have hfirst : rawChainMap incl (n + 1)
        (rawBoundary (n + 1) (universalSingularSubdivisionHomotopy (n + 1))) =
      affineChainRealization (n + 1) (affineBoundary (n + 1)
        (affineSubdivisionHomotopy (n + 1) (Finsupp.single (simplexStandardVertices (n + 1)) 1))) := by
    rw [← hmap, universalSingularSubdivisionHomotopy_ambient]
    exact hreal
  have hsecond : rawChainMap incl (n + 1)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          rawChainMap (face i) (n + 1) (universalSingularSubdivisionHomotopy n)) =
      affineChainRealization (n + 1) (affineSubdivisionHomotopy n
        (affineBoundary n (Finsupp.single (simplexStandardVertices (n + 1)) 1))) := by
    rw [affineBoundary_single]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun c => (-1 : ℤ) ^ i.val • c)
      (universalSingularSubdivisionHomotopy_face_ambient i)
  rw [map_add, hfirst, hsecond, ← map_add, hT, map_sub]
  rw [map_sub, universalIdentity_ambient, universalSingularSubdivision_ambient]

end BanachIsometric.SingularPrism
