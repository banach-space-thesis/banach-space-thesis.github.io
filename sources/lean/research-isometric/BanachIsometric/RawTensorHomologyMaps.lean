import BanachIsometric.RawFactorContraction
import BanachIsometric.RawTensorHomogeneousGenerators

/-! Apply the actual homology projection and cycle-section maps to both
factors of the raw tensor complex, retaining the literal bidegrees. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

abbrev RawHomology (X : Type*) [TopologicalSpace X] (n : ℕ) :=
  VectorChainSplitting.Homology (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n

abbrev rawFactorHomologyProjection (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawRationalChains X n →ₗ[ℚ] RawHomology X n :=
  VectorChainSplitting.homologyProjection (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n

abbrev rawFactorHomologyInclusion (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawHomology X n →ₗ[ℚ] RawRationalChains X n :=
  VectorChainSplitting.homologyInclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n

@[simp] theorem rawFactorHomologyProjection_inclusion (n : ℕ) (a : RawHomology X n) :
    rawFactorHomologyProjection X n (rawFactorHomologyInclusion X n a) = a :=
  VectorChainSplitting.homologyProjection_inclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n a

@[simp] theorem rawFactorHomologyProjection_boundary (n : ℕ) (a : RawRationalChains X (n + 1)) :
    rawFactorHomologyProjection X n (rawBoundary n a) = 0 :=
  VectorChainSplitting.homologyProjection_boundary (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n a

@[simp] theorem rawBoundary_factorHomologyInclusion (n : ℕ) (a : RawHomology X (n + 1)) :
    rawBoundary n (rawFactorHomologyInclusion X (n + 1) a) = 0 :=
  VectorChainSplitting.differential_homologyInclusion (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n a

theorem rawFactorHomologyProjection_cycle (n : ℕ)
    (a : VectorChainSplitting.cycles (rawFactorObjects X) (rawBoundary (X := X)) n) :
    rawFactorHomologyProjection X n a.val = Submodule.Quotient.mk a :=
  congrArg (VectorChainSplitting.boundaries (rawFactorObjects X) (rawBoundary (X := X))
    (rawBoundary_squared (X := X)) n).mkQ
    (VectorChainSplitting.cycleProjection_cycle (rawFactorObjects X) (rawBoundary (X := X))
      (rawBoundary_squared (X := X)) n a)

abbrev HomologyBidegrees (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}

abbrev RawHomologyTensorDegree (n : ℕ) :=
  ⨁ ij : HomologyBidegrees n, RawHomology X ij.val.1 ⊗[ℚ] RawHomology Y ij.val.2

def rawHomologyTensorInclusion {n p q : ℕ} (h : p + q = n) :
    (RawHomology X p ⊗[ℚ] RawHomology Y q) →ₗ[ℚ] RawHomologyTensorDegree X Y n :=
  DirectSum.lof ℚ (HomologyBidegrees n)
    (fun ij => RawHomology X ij.val.1 ⊗[ℚ] RawHomology Y ij.val.2) ⟨(p, q), h⟩

def rawTensorHomologyInclusion (n : ℕ) :
    RawHomologyTensorDegree X Y n →ₗ[ℚ] rawTensorTotalDegree X Y n :=
  DirectSum.toModule ℚ (HomologyBidegrees n) (rawTensorTotalDegree X Y n) (fun ij =>
    (rawTensorHomogeneousInclusion ij.property).comp
      (TensorProduct.map (rawFactorHomologyInclusion X ij.val.1)
        (rawFactorHomologyInclusion Y ij.val.2)))

def rawTensorHomologyProjectionTotal (n : ℕ) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawHomologyTensorDegree X Y n :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawHomologyTensorDegree X Y n) (fun ij =>
    if h : ij.1 + ij.2 = n then
      (rawHomologyTensorInclusion X Y h).comp
        (TensorProduct.map (rawFactorHomologyProjection X ij.1) (rawFactorHomologyProjection Y ij.2))
    else 0)

def rawTensorHomologyProjection (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] RawHomologyTensorDegree X Y n :=
  (rawTensorHomologyProjectionTotal X Y n).comp (rawTensorTotalDegree X Y n).subtype

@[simp] theorem rawTensorHomologyInclusion_tmul {n p q : ℕ} (h : p + q = n)
    (a : RawHomology X p) (b : RawHomology Y q) :
    rawTensorHomologyInclusion X Y n (rawHomologyTensorInclusion X Y h (a ⊗ₜ[ℚ] b)) =
      rawTensorHomogeneousInclusion h
        (rawFactorHomologyInclusion X p a ⊗ₜ[ℚ] rawFactorHomologyInclusion Y q b) := by
  simp only [rawTensorHomologyInclusion, rawHomologyTensorInclusion, DirectSum.toModule_lof,
    LinearMap.comp_apply, TensorProduct.map_tmul]

@[simp] theorem rawTensorHomologyProjectionTotal_tmul {n p q : ℕ} (h : p + q = n)
    (a : RawRationalChains X p) (b : RawRationalChains Y q) :
    rawTensorHomologyProjectionTotal X Y n (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b)) =
      rawHomologyTensorInclusion X Y h
        (rawFactorHomologyProjection X p a ⊗ₜ[ℚ] rawFactorHomologyProjection Y q b) := by
  simp only [rawTensorHomologyProjectionTotal, rawTensorInclusion, DirectSum.toModule_lof,
    dif_pos h, LinearMap.comp_apply, TensorProduct.map_tmul]

@[simp] theorem rawTensorHomologyProjectionTotal_of_ne {n p q : ℕ} (h : p + q ≠ n)
    (c : RawTensorChains X Y p q) :
    rawTensorHomologyProjectionTotal X Y n (rawTensorInclusion X Y p q c) = 0 := by
  simp only [rawTensorHomologyProjectionTotal, rawTensorInclusion, DirectSum.toModule_lof,
    dif_neg h, LinearMap.zero_apply]

@[simp] theorem rawTensorHomologyProjection_tmul {n p q : ℕ} (h : p + q = n)
    (a : RawRationalChains X p) (b : RawRationalChains Y q) :
    rawTensorHomologyProjection X Y n (rawTensorHomogeneousInclusion h (a ⊗ₜ[ℚ] b)) =
      rawHomologyTensorInclusion X Y h
        (rawFactorHomologyProjection X p a ⊗ₜ[ℚ] rawFactorHomologyProjection Y q b) :=
  rawTensorHomologyProjectionTotal_tmul X Y h a b

end BanachIsometric.SingularAW
