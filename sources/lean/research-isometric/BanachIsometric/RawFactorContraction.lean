import BanachIsometric.VectorChainNormalizedContraction
import BanachIsometric.ConvexSingularAcyclicity
import BanachIsometric.ContractibleZeroHomology

/-! Actual factor contraction maps on literal raw singular chains, with
their homology-representative projectors. On a contractible space the positive
projectors vanish, and the degree-zero projector kills augmentation-zero chains. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism

variable (X : Type*) [TopologicalSpace X]

abbrev rawFactorObjects (n : ℕ) := ModuleCat.of ℚ (RawRationalChains X n)

def rawFactorContraction (n : ℕ) : RawRationalChains X n →ₗ[ℚ] RawRationalChains X (n + 1) :=
  VectorChainSplitting.contraction (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n

def rawFactorProjector (n : ℕ) : RawRationalChains X n →ₗ[ℚ] RawRationalChains X n :=
  (VectorChainSplitting.homologyInclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n).comp
    (VectorChainSplitting.homologyProjection (rawFactorObjects X) (rawBoundary (X := X))
      (rawBoundary_squared (X := X)) n)

theorem rawFactorContraction_zero_identity (x : RawRationalChains X 0) :
    rawBoundary 0 (rawFactorContraction X 0 x) = x - rawFactorProjector X 0 x :=
  VectorChainSplitting.contraction_zero_identity (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) x

theorem rawFactorContraction_succ_identity (n : ℕ) (x : RawRationalChains X (n + 1)) :
    rawBoundary (n + 1) (rawFactorContraction X (n + 1) x) +
      rawFactorContraction X n (rawBoundary n x) = x - rawFactorProjector X (n + 1) x :=
  VectorChainSplitting.contraction_succ_identity (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n x

theorem rawFactorProjector_boundary (n : ℕ) (x : RawRationalChains X (n + 1)) :
    rawFactorProjector X n (rawBoundary n x) = 0 := by
  change VectorChainSplitting.homologyInclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n
    (VectorChainSplitting.homologyProjection (rawFactorObjects X) (rawBoundary (X := X))
      (rawBoundary_squared (X := X)) n (rawBoundary n x)) = 0
  rw [VectorChainSplitting.homologyProjection_boundary, map_zero]

theorem rawBoundary_factorProjector (n : ℕ) (x : RawRationalChains X (n + 1)) :
    rawBoundary n (rawFactorProjector X (n + 1) x) = 0 :=
  VectorChainSplitting.differential_homologyInclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n _

theorem rawFactorProjector_succ_eq_zero [ContractibleSpace X] (n : ℕ) :
    rawFactorProjector X (n + 1) = 0 := by
  haveI : Subsingleton (VectorChainSplitting.Homology (rawFactorObjects X)
      (rawBoundary (X := X)) (rawBoundary_squared (X := X)) (n + 1)) :=
    rawPositiveHomology_contractible X n
  apply LinearMap.ext
  intro x
  change VectorChainSplitting.homologyInclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) (n + 1)
    (VectorChainSplitting.homologyProjection (rawFactorObjects X) (rawBoundary (X := X))
      (rawBoundary_squared (X := X)) (n + 1) x) = 0
  rw [Subsingleton.elim (VectorChainSplitting.homologyProjection (rawFactorObjects X)
    (rawBoundary (X := X)) (rawBoundary_squared (X := X)) (n + 1) x) 0, map_zero]

theorem rawFactorProjector_zero_of_augmentation_eq_zero [ContractibleSpace X]
    {x : RawRationalChains X 0} (hx : rawAugmentation X x = 0) :
    rawFactorProjector X 0 x = 0 := by
  have hq : (Submodule.Quotient.mk x : RawZeroHomology X) = 0 := by
    apply (rawZeroHomologyContractibleEquiv X).injective
    change rawAugmentation X x = 0
    exact hx
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range (rawBoundary (X := X) 0))).mp hq
  rw [← hb]
  exact rawFactorProjector_boundary X 0 b

end BanachIsometric.SingularAW
