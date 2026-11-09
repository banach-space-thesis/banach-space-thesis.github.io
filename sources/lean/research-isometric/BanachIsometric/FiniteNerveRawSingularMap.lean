import BanachIsometric.FiniteNerveRationalBoundary
import BanachIsometric.FiniteNerveBarycentricGeometry
import BanachIsometric.RawSingularChains

/-! The actual finite ordered simplicial chains map to actual rational
singular chains by their literal barycentric simplex maps. The chain map
and its degreewise injectivity are proved; no homology isomorphism or
surjectivity on singular homology is asserted. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def barycentricSingularSimplex (K : Complex ι) (n : ℕ) (v : StrictOrderedSimplex K n) :
    RawSingularSimplex K.space n :=
  faceBarycentricMap K (fun j => v.val.val j) v.val.property

theorem barycentricSingularSimplex_injective (K : Complex ι) (n : ℕ) :
    Function.Injective (barycentricSingularSimplex K n) := by
  intro v w he
  apply Subtype.ext
  apply Subtype.ext
  ext j
  apply vertex_injective
  have h := congrArg (fun σ : RawSingularSimplex K.space n =>
    ((σ (stdSimplex.vertex j) : K.space) : ι → ℝ)) he
  change (faceBarycentricMap K (fun i => v.val.val i) v.val.property (stdSimplex.vertex j) : ι → ℝ) =
    (faceBarycentricMap K (fun i => w.val.val i) w.val.property (stdSimplex.vertex j) : ι → ℝ) at h
  rwa [faceBarycentricMap_vertex, faceBarycentricMap_vertex] at h

@[simp] theorem barycentricSingularSimplex_face (K : Complex ι) (n : ℕ) (i : Fin (n + 2))
    (v : StrictOrderedSimplex K (n + 1)) :
    barycentricSingularSimplex K n (strictOrderedFace K i v) =
      (barycentricSingularSimplex K (n + 1) v).comp (SingularPrism.face i) := by
  apply ContinuousMap.ext
  intro t
  exact faceBarycentricMap_naturality K i.succAbove (fun j => v.val.val j) v.val.property t

def rationalToRawSingularChain (K : Complex ι) (n : ℕ) :
    RationalChains K n →ₗ[ℚ] RawRationalChains K.space n :=
  (Finsupp.lmapDomain ℚ ℚ (barycentricSingularSimplex K n)).comp
    (rationalChainBasis K n).repr.toLinearMap

@[simp] theorem rationalToRawSingularChain_basis (K : Complex ι) (n : ℕ)
    (v : StrictOrderedSimplex K n) :
    rationalToRawSingularChain K n (rationalChainBasis K n v) =
      Finsupp.single (barycentricSingularSimplex K n v) 1 := by
  simp [rationalToRawSingularChain]

theorem rationalToRawSingularChain_injective (K : Complex ι) (n : ℕ) :
    Function.Injective (rationalToRawSingularChain K n) :=
  (Finsupp.mapDomain_injective (barycentricSingularSimplex_injective K n)).comp
    (rationalChainBasis K n).repr.injective

theorem rationalToRawSingularChain_boundary (K : Complex ι) (n : ℕ) :
    (rawBoundary (X := K.space) n).comp (rationalToRawSingularChain K (n + 1)) =
      (rationalToRawSingularChain K n).comp (rationalBoundary K n) := by
  apply (rationalChainBasis K (n + 1)).ext
  intro v
  simp only [LinearMap.comp_apply, rationalToRawSingularChain_basis, rawBoundary_single,
    rationalBoundary_basis, map_sum, map_zsmul, barycentricSingularSimplex_face]

end BanachIsometric.FiniteNerve

