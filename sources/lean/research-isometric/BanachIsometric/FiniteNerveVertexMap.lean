import BanachIsometric.FiniteNerveNormalization

/-! Actual ordered-vertex maps on weak simplicial chains, and the chain
inclusion of strict normalized faces. These identities are proved directly
from finite face deletion. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def orderedVertexMap (K : Complex ι) (f : ι →o ι)
    (hf : ∀ s ∈ K.faces, s.image f ∈ K.faces) {n : ℕ} (v : OrderedSimplex K n) :
    OrderedSimplex K n :=
  ⟨f.comp v.val, by simpa only [Finset.image_image, Function.comp_def] using hf _ v.property⟩

theorem orderedVertexMap_face (K : Complex ι) (f : ι →o ι)
    (hf : ∀ s ∈ K.faces, s.image f ∈ K.faces) {n : ℕ}
    (v : OrderedSimplex K (n + 1)) (i : Fin (n + 2)) :
    orderedVertexMap K f hf (orderedFace K i v) = orderedFace K i (orderedVertexMap K f hf v) := rfl

def weakVertexChainMap (K : Complex ι) (f : ι →o ι)
    (hf : ∀ s ∈ K.faces, s.image f ∈ K.faces) (n : ℕ) :
    WeakRationalChains K n →ₗ[ℚ] WeakRationalChains K n :=
  Finsupp.lmapDomain ℚ ℚ (orderedVertexMap K f hf)

@[simp] theorem weakVertexChainMap_single (K : Complex ι) (f : ι →o ι)
    (hf : ∀ s ∈ K.faces, s.image f ∈ K.faces) (n : ℕ) (v : OrderedSimplex K n) (a : ℚ) :
    weakVertexChainMap K f hf n (Finsupp.single v a) =
      Finsupp.single (orderedVertexMap K f hf v) a := Finsupp.mapDomain_single

theorem weakVertexChainMap_boundary (K : Complex ι) (f : ι →o ι)
    (hf : ∀ s ∈ K.faces, s.image f ∈ K.faces) (n : ℕ) :
    (weakRationalBoundary K n).comp (weakVertexChainMap K f hf (n + 1)) =
      (weakVertexChainMap K f hf n).comp (weakRationalBoundary K n) := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, weakVertexChainMap_single, weakRationalBoundary_single,
    map_sum, map_zsmul, orderedVertexMap_face]

theorem strictChainInclusion_boundary (K : Complex ι) (n : ℕ) :
    (weakRationalBoundary K n).comp (strictChainInclusion K (n + 1)) =
      (strictChainInclusion K n).comp (finiteRationalBoundary K n) := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, strictChainInclusion, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, weakRationalBoundary_single, finiteRationalBoundary_single,
    map_sum, map_zsmul, strictOrderedFace]

end BanachIsometric.FiniteNerve
