import BanachIsometric.SimplexBoundarySphere
import BanachIsometric.AlternatingFaceCycle
import BanachIsometric.RawSingularHomology

/-!
# An explicit singular cycle on the genuine Euclidean sphere

The alternating sum of the ACTUAL radially projected boundary faces is a
cycle. Its homology class is constructed as the literal cycles/boundaries
quotient. No filling, nonzero/generator property, or Hurewicz comparison is
assumed. Both the sphere dimension and singular degree are `n+1`.
-/

noncomputable section
namespace BanachIsometric.SingularPrism

open SphereGenerator

def canonicalSphereChain (n : ℕ) : RawRationalChains (Sph (n + 1)) (n + 1) :=
  ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
    Finsupp.single (boundarySimplexSphereFace n i) (1 : ℚ)

theorem canonicalSphereChain_boundary (n : ℕ) :
    rawBoundary n (canonicalSphereChain n) = 0 :=
  rawBoundary_alternating_face_family n (boundarySimplexSphereFace n)
    (boundarySimplexSphereFace_face n)

def canonicalSphereCycle (n : ℕ) : rawCycles (Sph (n + 1)) n :=
  ⟨canonicalSphereChain n, canonicalSphereChain_boundary n⟩

def canonicalSphereClass (n : ℕ) : RawPositiveHomology (Sph (n + 1)) n :=
  Submodule.Quotient.mk (canonicalSphereCycle n)

end BanachIsometric.SingularPrism
