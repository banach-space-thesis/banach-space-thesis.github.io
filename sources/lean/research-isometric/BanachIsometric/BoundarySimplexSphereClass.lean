import BanachIsometric.BoundarySimplexTopCycle
import BanachIsometric.CanonicalSphereCycle
import BanachIsometric.FiniteNerveRawHomologyMap

/-! The explicit nonzero finite top class maps to EXACTLY the singular sphere
class used by `SphereCycleClassMap`. This proves correspondence of the actual
chain formulas and quotient maps. It does not claim nonzero singular image:
injectivity of the finite/singular homology comparison remains separate. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve Module SphereGenerator

def boundarySimplexRealizationToSphere (n : ℕ) :
    C((boundarySimplexComplex n).space, Sph (n + 1)) :=
  ⟨boundarySimplexComplexSphereHomeomorph n,
    (boundarySimplexComplexSphereHomeomorph n).continuous⟩

theorem boundarySimplexRealizationToSphere_facet (n : ℕ) (i : Fin (n + 3)) :
    (boundarySimplexRealizationToSphere n).comp
      (barycentricSingularSimplex (boundarySimplexComplex n) (n + 1)
        (boundarySimplexFacet n i)) = boundarySimplexSphereFace n i := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  change (simplexBoundarySphereHomeomorph n
    (boundarySimplexRealizationHomeomorph n
      (barycentricSingularSimplex (boundarySimplexComplex n) (n + 1)
        (boundarySimplexFacet n i) w))).val =
      NormedSpace.normalize (centeredSimplexVector n (face i w))
  rw [simplexBoundarySphereHomeomorph_apply_val]
  rfl

theorem boundarySimplexTopChain_sphere_image (n : ℕ) :
    rawChainMap (boundarySimplexRealizationToSphere n) (n + 1)
      (rationalToRawSingularChain (boundarySimplexComplex n) (n + 1)
        (boundarySimplexTopChain n)) = canonicalSphereChain n := by
  simp only [boundarySimplexTopChain, map_sum, map_zsmul,
    rationalToRawSingularChain_basis, canonicalSphereChain]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [boundarySimplexRealizationToSphere_facet]

set_option maxHeartbeats 1000000 in
theorem boundarySimplexTopClass_sphere_image (n : ℕ) :
    rawHomologyMap (boundarySimplexRealizationToSphere n) n
      (finiteToRawPositiveHomology (boundarySimplexComplex n) n
        (boundarySimplexTopClass n)) = canonicalSphereClass n := by
  change rawHomologyMap (boundarySimplexRealizationToSphere n) n
    (Submodule.Quotient.mk
      (finiteToRawSingularCycles (boundarySimplexComplex n) n (boundarySimplexTopCycle n))) = _
  rw [rawHomologyMap_mk]
  apply congrArg (fun c : rawCycles (Sph (n + 1)) n =>
    (Submodule.Quotient.mk c : RawPositiveHomology (Sph (n + 1)) n))
  apply Subtype.ext
  change rawChainMap (boundarySimplexRealizationToSphere n) (n + 1)
    (finiteToRawSingularChain (boundarySimplexComplex n) (n + 1)
      ((rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr
        (boundarySimplexTopChain n))) = canonicalSphereChain n
  simp only [finiteToRawSingularChain, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact boundarySimplexTopChain_sphere_image n

end BanachIsometric.SingularPrism
