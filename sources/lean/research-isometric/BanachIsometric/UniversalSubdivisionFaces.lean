import BanachIsometric.UniversalSingularSubdivision
import BanachIsometric.RawSingularHomology
import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-! The universal subdivision chains respect the actual coordinate faces.
This is derived from the proved affine linear naturality, including the
literal ambient inclusion comparison. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

def simplexFaceLinear {n : ℕ} (i : Fin (n + 2)) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 2) → ℝ) :=
  ⟨FunOnFinite.linearMap ℝ ℝ i.succAbove,
    FunOnFinite.continuous_linearMap ℝ ℝ i.succAbove⟩

theorem simplexFaceLinear_vertices {n : ℕ} (i : Fin (n + 2)) :
    simplexFaceLinear i ∘ simplexStandardVertices n =
      simplexStandardVertices (n + 1) ∘ i.succAbove := by
  funext j
  exact FunOnFinite.linearMap_piSingle ℝ ℝ i.succAbove j 1

theorem simplexFaceLinear_inclusion {n : ℕ} (i : Fin (n + 2)) :
    (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 2)))).comp (face i) =
      (⟨simplexFaceLinear i, (simplexFaceLinear i).continuous⟩ :
        C(Fin (n + 1) → ℝ, Fin (n + 2) → ℝ)).comp
          (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))) := rfl

theorem universalSingularSubdivision_ambient (n : ℕ) :
    rawChainMap (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))) n
        (universalSingularSubdivision n) =
      affineChainRealization n (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1)) :=
  affineCarrierRealization_ambient_apply (convex_stdSimplex ℝ _) n (universalAffineSubdivision n)

theorem universalSingularSubdivisionHomotopy_ambient (n : ℕ) :
    rawChainMap (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))) (n + 1)
        (universalSingularSubdivisionHomotopy n) =
      affineChainRealization (n + 1)
        (affineSubdivisionHomotopy n (Finsupp.single (simplexStandardVertices n) 1)) :=
  affineCarrierRealization_ambient_apply (convex_stdSimplex ℝ _) (n + 1)
    (universalAffineSubdivisionHomotopy n)

set_option maxHeartbeats 1000000 in
theorem universalSingularSubdivision_face_ambient {n : ℕ} (i : Fin (n + 2)) :
    rawChainMap (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 2)))) n
        (rawChainMap (face i) n (universalSingularSubdivision n)) =
      affineChainRealization n (affineSubdivision n
        (Finsupp.single (simplexStandardVertices (n + 1) ∘ i.succAbove) 1)) := by
  let f : C(Fin (n + 1) → ℝ, Fin (n + 2) → ℝ) :=
    ⟨simplexFaceLinear i, (simplexFaceLinear i).continuous⟩
  have hmap := congrArg (fun h => rawChainMap h n) (simplexFaceLinear_inclusion i)
  simp only [rawChainMap_comp] at hmap
  have hreal := LinearMap.congr_fun (affineChainRealization_linearMap (simplexFaceLinear i) n)
    (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1))
  have hSd := LinearMap.congr_fun (affineSubdivision_natural (simplexFaceLinear i).toLinearMap n)
    (Finsupp.single (simplexStandardVertices n) 1)
  simp only [LinearMap.comp_apply, affineVertexMap_single] at hreal hSd
  change affineVertexMap (simplexFaceLinear i) n
      (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1)) =
    affineSubdivision n (Finsupp.single (simplexFaceLinear i ∘ simplexStandardVertices n) 1) at hSd
  rw [simplexFaceLinear_vertices] at hSd
  calc
    _ = rawChainMap f n (rawChainMap (affineCarrierInclusion
          (stdSimplex ℝ (Fin (n + 1)))) n (universalSingularSubdivision n)) :=
      LinearMap.congr_fun hmap _
    _ = rawChainMap f n (affineChainRealization n
          (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1))) := by
      rw [universalSingularSubdivision_ambient]
    _ = affineChainRealization n (affineVertexMap (simplexFaceLinear i) n
          (affineSubdivision n (Finsupp.single (simplexStandardVertices n) 1))) := hreal
    _ = _ := congrArg (affineChainRealization n) hSd

set_option maxHeartbeats 1000000 in
theorem universalSingularSubdivisionHomotopy_face_ambient {n : ℕ} (i : Fin (n + 2)) :
    rawChainMap (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 2)))) (n + 1)
        (rawChainMap (face i) (n + 1) (universalSingularSubdivisionHomotopy n)) =
      affineChainRealization (n + 1) (affineSubdivisionHomotopy n
        (Finsupp.single (simplexStandardVertices (n + 1) ∘ i.succAbove) 1)) := by
  let f : C(Fin (n + 1) → ℝ, Fin (n + 2) → ℝ) :=
    ⟨simplexFaceLinear i, (simplexFaceLinear i).continuous⟩
  have hmap := congrArg (fun h => rawChainMap h (n + 1)) (simplexFaceLinear_inclusion i)
  simp only [rawChainMap_comp] at hmap
  have hreal := LinearMap.congr_fun (affineChainRealization_linearMap (simplexFaceLinear i) (n + 1))
    (affineSubdivisionHomotopy n (Finsupp.single (simplexStandardVertices n) 1))
  have hT := LinearMap.congr_fun
    (affineSubdivisionHomotopy_natural (simplexFaceLinear i).toLinearMap n)
      (Finsupp.single (simplexStandardVertices n) 1)
  simp only [LinearMap.comp_apply, affineVertexMap_single] at hreal hT
  change affineVertexMap (simplexFaceLinear i) (n + 1)
      (affineSubdivisionHomotopy n (Finsupp.single (simplexStandardVertices n) 1)) =
    affineSubdivisionHomotopy n (Finsupp.single (simplexFaceLinear i ∘ simplexStandardVertices n) 1) at hT
  rw [simplexFaceLinear_vertices] at hT
  calc
    _ = rawChainMap f (n + 1) (rawChainMap (affineCarrierInclusion
          (stdSimplex ℝ (Fin (n + 1)))) (n + 1) (universalSingularSubdivisionHomotopy n)) :=
      LinearMap.congr_fun hmap _
    _ = rawChainMap f (n + 1) (affineChainRealization (n + 1)
          (affineSubdivisionHomotopy n (Finsupp.single (simplexStandardVertices n) 1))) := by
      rw [universalSingularSubdivisionHomotopy_ambient]
    _ = affineChainRealization (n + 1) (affineVertexMap (simplexFaceLinear i) (n + 1)
          (affineSubdivisionHomotopy n (Finsupp.single (simplexStandardVertices n) 1))) := hreal
    _ = _ := congrArg (affineChainRealization (n + 1)) hT

end BanachIsometric.SingularPrism
