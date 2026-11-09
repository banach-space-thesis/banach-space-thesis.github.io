import BanachIsometric.RawSubdivisionNaturality
import BanachIsometric.UniversalSubdivisionFaces
import BanachIsometric.AffineSimplexLinearExtension

/-! Subdivision of an actual affine singular simplex is exactly the
realization of its constructed affine subdivision. This compatibility
transfers the proved mesh bounds to iterated singular subdivision. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineSimplexLinearExtension_vertices {n : ℕ} (v : Fin (n + 1) → E) :
    affineSimplexLinearExtension v ∘ simplexStandardVertices n = v := by
  classical
  funext i
  simp only [Function.comp_apply, affineSimplexLinearExtension_apply, simplexStandardVertices]
  simp [Pi.single_apply, eq_comm]

set_option maxHeartbeats 1000000 in
theorem rawSubdivision_affine_single (n : ℕ) (v : Fin (n + 1) → E) :
    rawSubdivision E n (Finsupp.single (affineSingularSimplex v) 1) =
      affineChainRealization n (affineSubdivision n (Finsupp.single v 1)) := by
  let f : C(Fin (n + 1) → ℝ, E) :=
    ⟨affineSimplexLinearExtension v, (affineSimplexLinearExtension v).continuous⟩
  have hmap := congrArg (fun h => rawChainMap h n) (affineSimplexLinearExtension_inclusion v)
  simp only [rawChainMap_comp] at hmap
  have hreal := LinearMap.congr_fun (affineChainRealization_linearMap (affineSimplexLinearExtension v) n)
    (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1))
  have hSd := LinearMap.congr_fun (affineSubdivision_natural (affineSimplexLinearExtension v).toLinearMap n)
    (Finsupp.single (simplexStandardVertices n) 1)
  simp only [LinearMap.comp_apply, affineVertexMap_single] at hreal hSd
  change affineVertexMap (affineSimplexLinearExtension v) n
      (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1)) =
    affineSubdivision n (Finsupp.single (affineSimplexLinearExtension v ∘ simplexStandardVertices n) 1) at hSd
  rw [affineSimplexLinearExtension_vertices] at hSd
  rw [rawSubdivision_single_one]
  calc
    _ = rawChainMap f n (rawChainMap (affineCarrierInclusion
          (stdSimplex ℝ (Fin (n + 1)))) n (universalSingularSubdivision n)) :=
      (LinearMap.congr_fun hmap _).symm
    _ = rawChainMap f n (affineChainRealization n
          (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1))) := by
      rw [universalSingularSubdivision_ambient]
    _ = affineChainRealization n (affineVertexMap (affineSimplexLinearExtension v) n
          (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1))) := hreal
    _ = _ := congrArg (affineChainRealization n) hSd

theorem rawSubdivision_affineChainRealization (n : ℕ) :
    (rawSubdivision E n).comp (affineChainRealization n) =
      (affineChainRealization n).comp (affineSubdivision n) := by
  apply Finsupp.lhom_ext
  intro v a
  have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  change rawSubdivision E n (affineChainRealization n (Finsupp.single v 1)) =
    affineChainRealization n (affineSubdivision n (Finsupp.single v 1))
  rw [affineChainRealization_single]
  exact rawSubdivision_affine_single n v

end BanachIsometric.SingularPrism
