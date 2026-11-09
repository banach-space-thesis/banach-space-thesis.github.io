import BanachIsometric.AffineCarrierRealization
import BanachIsometric.AffineSubdivisionNaturality

/-! Actual carrier realization commutes with the boundary. The proof uses
the proved ambient comparison and injectivity of literal inclusion on free
singular chains. Linear ambient maps also commute with affine realization. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

theorem rawChainMap_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Function.Injective f) (n : ℕ) : Function.Injective (rawChainMap f n) := by
  apply Finsupp.mapDomain_injective
  intro a b h
  apply ContinuousMap.ext
  intro w
  exact hf (ContinuousMap.congr_fun h w)

def affineCarrierBoundary {E : Type*} (s : Set E) (n : ℕ) :
    affineCarrier s (n + 1) →ₗ[ℚ] affineCarrier s n :=
  ((affineBoundary n).comp (affineCarrier s (n + 1)).subtype).codRestrict
    (affineCarrier s n) (fun c => affineBoundary_carrier s n c.property)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineCarrierRealization_ambient_apply {s : Set E} (hs : Convex ℝ s) (n : ℕ)
    (c : affineCarrier s n) :
    rawChainMap (affineCarrierInclusion s) n (affineCarrierRealization hs n c) =
      affineChainRealization n c.val := LinearMap.congr_fun (affineCarrierRealization_ambient hs n) c

theorem affineCarrierRealization_boundary {s : Set E} (hs : Convex ℝ s) (n : ℕ) :
    (rawBoundary n).comp (affineCarrierRealization hs (n + 1)) =
      (affineCarrierRealization hs n).comp (affineCarrierBoundary s n) := by
  apply LinearMap.ext
  intro c
  apply rawChainMap_injective (affineCarrierInclusion s) Subtype.val_injective n
  change rawChainMap (affineCarrierInclusion s) n
      (rawBoundary n (affineCarrierRealization hs (n + 1) c)) =
    rawChainMap (affineCarrierInclusion s) n
      (affineCarrierRealization hs n (affineCarrierBoundary s n c))
  have hmap := LinearMap.congr_fun (rawChainMap_boundary (affineCarrierInclusion s) n)
    (affineCarrierRealization hs (n + 1) c)
  simp only [LinearMap.comp_apply] at hmap
  rw [← hmap, affineCarrierRealization_ambient_apply, affineCarrierRealization_ambient_apply]
  exact LinearMap.congr_fun (affineChainRealization_boundary n) c.val

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineSingularSimplex_linearMap (f : E →L[ℝ] F) {n : ℕ} (v : Fin (n + 1) → E) :
    (⟨f, f.continuous⟩ : C(E, F)).comp (affineSingularSimplex v) =
      affineSingularSimplex (f ∘ v) := by
  apply ContinuousMap.ext
  intro w
  change f (∑ i, w i • v i) = ∑ i, w i • f (v i)
  simp only [map_sum, map_smul]

theorem affineChainRealization_linearMap (f : E →L[ℝ] F) (n : ℕ) :
    (rawChainMap ⟨f, f.continuous⟩ n).comp (affineChainRealization n) =
      (affineChainRealization n).comp (affineVertexMap f n) := by
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, affineChainRealization_single, affineVertexMap_single,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, affineSingularSimplex_linearMap]

end BanachIsometric.SingularPrism
