import BanachIsometric.AffineCarrierBoundary

/-! Universal subdivision chains are realized in the literal standard
simplex, and then pushed along each actual continuous singular simplex.
The support and continuity of every affine piece are proved internally. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

def simplexStandardVertices (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℝ := Pi.single i 1

theorem simplexStandardVertices_mem (n : ℕ) (i : Fin (n + 1)) :
    simplexStandardVertices n i ∈ stdSimplex ℝ (Fin (n + 1)) := single_mem_stdSimplex ℝ i

def universalAffineSimplex (n : ℕ) : affineCarrier (stdSimplex ℝ (Fin (n + 1))) n :=
  ⟨Finsupp.single (simplexStandardVertices n) 1,
    Finsupp.single_mem_supported ℚ 1 (simplexStandardVertices_mem n)⟩

def universalAffineSubdivision (n : ℕ) : affineCarrier (stdSimplex ℝ (Fin (n + 1))) n :=
  ⟨affineSubdivision n (universalAffineSimplex n).val,
    affineSubdivision_carrier (convex_stdSimplex ℝ _) n (universalAffineSimplex n).property⟩

def universalAffineSubdivisionHomotopy (n : ℕ) :
    affineCarrier (stdSimplex ℝ (Fin (n + 1))) (n + 1) :=
  ⟨affineSubdivisionHomotopy n (universalAffineSimplex n).val,
    affineSubdivisionHomotopy_carrier (convex_stdSimplex ℝ _) n (universalAffineSimplex n).property⟩

def universalSingularSubdivision (n : ℕ) : RawRationalChains (Simplex n) n :=
  affineCarrierRealization (convex_stdSimplex ℝ _) n (universalAffineSubdivision n)

def universalSingularSubdivisionHomotopy (n : ℕ) : RawRationalChains (Simplex n) (n + 1) :=
  affineCarrierRealization (convex_stdSimplex ℝ _) (n + 1) (universalAffineSubdivisionHomotopy n)

def rawSubdivision (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawRationalChains X n →ₗ[ℚ] RawRationalChains X n :=
  Finsupp.linearCombination ℚ (fun simplex => rawChainMap simplex n (universalSingularSubdivision n))

def rawSubdivisionHomotopy (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawRationalChains X n →ₗ[ℚ] RawRationalChains X (n + 1) :=
  Finsupp.linearCombination ℚ (fun simplex =>
    rawChainMap simplex (n + 1) (universalSingularSubdivisionHomotopy n))

theorem rawSubdivision_single_one {X : Type*} [TopologicalSpace X]
    (n : ℕ) (simplex : RawSingularSimplex X n) :
    rawSubdivision X n (Finsupp.single simplex 1) =
      rawChainMap simplex n (universalSingularSubdivision n) := by
  simp only [rawSubdivision, Finsupp.linearCombination_single, one_smul]

theorem rawSubdivisionHomotopy_single_one {X : Type*} [TopologicalSpace X]
    (n : ℕ) (simplex : RawSingularSimplex X n) :
    rawSubdivisionHomotopy X n (Finsupp.single simplex 1) =
      rawChainMap simplex (n + 1) (universalSingularSubdivisionHomotopy n) := by
  simp only [rawSubdivisionHomotopy, Finsupp.linearCombination_single, one_smul]

end BanachIsometric.SingularPrism
