import BanachIsometric.RawSubspaceChains
import BanachIsometric.RawSingularHomology
import Mathlib.LinearAlgebra.Prod

/-! A rational cycle subordinate to a two-set open cover is the sum of
two subspace chains. The space of such pairs surjects onto ambient homology. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

abbrev RawUnionChainPair (U V : Set X) (n : ℕ) :=
  RawRationalChains U n × RawRationalChains V n

def rawUnionChainSum (U V : Set X) (n : ℕ) :
    RawUnionChainPair U V n →ₗ[ℚ] RawRationalChains X n :=
  (rawSubspaceChainInclusion U n).coprod (rawSubspaceChainInclusion V n)

abbrev rawUnionPairCycles (U V : Set X) (n : ℕ) : Submodule ℚ (RawUnionChainPair U V (n + 1)) :=
  LinearMap.ker ((rawBoundary n).comp (rawUnionChainSum U V (n + 1)))

theorem rawUnionPairBoundary_add_eq_zero (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V n) :
    rawSubspaceChainInclusion U n (rawBoundary n z.val.1) +
      rawSubspaceChainInclusion V n (rawBoundary n z.val.2) = 0 := by
  have h : rawBoundary n
      (rawSubspaceChainInclusion U (n + 1) z.val.1 +
        rawSubspaceChainInclusion V (n + 1) z.val.2) = 0 := z.property
  rw [map_add] at h
  have hU : rawBoundary n (rawSubspaceChainInclusion U (n + 1) z.val.1) =
      rawSubspaceChainInclusion U n (rawBoundary n z.val.1) :=
    LinearMap.congr_fun (rawSubspaceChainInclusion_boundary U n) z.val.1
  have hV : rawBoundary n (rawSubspaceChainInclusion V (n + 1) z.val.2) =
      rawSubspaceChainInclusion V n (rawBoundary n z.val.2) :=
    LinearMap.congr_fun (rawSubspaceChainInclusion_boundary V n) z.val.2
  rwa [hU, hV] at h

def rawUnionPairToCycles (U V : Set X) (n : ℕ) :
    rawUnionPairCycles U V n →ₗ[ℚ] rawCycles X n :=
  ((rawUnionChainSum U V (n + 1)).comp (rawUnionPairCycles U V n).subtype).codRestrict
    (rawCycles X n) fun z => z.property

def rawUnionPairToHomology (U V : Set X) (n : ℕ) :
    rawUnionPairCycles U V n →ₗ[ℚ] RawPositiveHomology X n :=
  (rawBoundaries X n).mkQ.comp (rawUnionPairToCycles U V n)

end BanachIsometric.SingularPrism
