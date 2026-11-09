import BanachIsometric.RawSingularChains
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.DirectSum.Module

/-! The actual bigraded rational tensor chains and their signed total
boundary. Degree-zero factor boundaries are zero. All summands retain their
literal natural-number bidegrees, so no subtraction cast is used. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

abbrev RawTensorChains (p q : ℕ) := RawRationalChains X p ⊗[ℚ] RawRationalChains Y q

abbrev RawBigradedTensorChains := ⨁ ij : ℕ × ℕ, RawTensorChains X Y ij.1 ij.2

def rawTensorInclusion (p q : ℕ) :
    RawTensorChains X Y p q →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.lof ℚ (ℕ × ℕ) (fun ij => RawTensorChains X Y ij.1 ij.2) (p, q)

def rawTensorLeftComponent : (p q : ℕ) →
    RawTensorChains X Y p q →ₗ[ℚ] RawBigradedTensorChains X Y
  | 0, _ => 0
  | p + 1, q => (rawTensorInclusion X Y p q).comp
      (TensorProduct.map (rawBoundary p) LinearMap.id)

def rawTensorRightComponent : (p q : ℕ) →
    RawTensorChains X Y p q →ₗ[ℚ] RawBigradedTensorChains X Y
  | _, 0 => 0
  | p, q + 1 => (-1 : ℚ) ^ p • (rawTensorInclusion X Y p q).comp
      (TensorProduct.map LinearMap.id (rawBoundary q))

def rawTensorLeftBoundary : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X Y)
    (fun ij => rawTensorLeftComponent X Y ij.1 ij.2)

def rawTensorRightBoundary : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X Y)
    (fun ij => rawTensorRightComponent X Y ij.1 ij.2)

def rawTensorTotalBoundary : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  rawTensorLeftBoundary X Y + rawTensorRightBoundary X Y

@[simp] theorem rawTensorLeftBoundary_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q c) = rawTensorLeftComponent X Y p q c := by
  simp only [rawTensorLeftBoundary, rawTensorInclusion, DirectSum.toModule_lof]

@[simp] theorem rawTensorRightBoundary_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorRightBoundary X Y (rawTensorInclusion X Y p q c) = rawTensorRightComponent X Y p q c := by
  simp only [rawTensorRightBoundary, rawTensorInclusion, DirectSum.toModule_lof]

theorem rawTensorTotalBoundary_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorTotalBoundary X Y (rawTensorInclusion X Y p q c) =
      rawTensorLeftComponent X Y p q c + rawTensorRightComponent X Y p q c := by
  simp only [rawTensorTotalBoundary, LinearMap.add_apply,
    rawTensorLeftBoundary_inclusion, rawTensorRightBoundary_inclusion]

@[simp] theorem rawTensorLeftBoundary_tmul (p q : ℕ)
    (c : RawRationalChains X (p + 1)) (d : RawRationalChains Y q) :
    rawTensorLeftBoundary X Y (rawTensorInclusion X Y (p + 1) q (c ⊗ₜ[ℚ] d)) =
      rawTensorInclusion X Y p q (rawBoundary p c ⊗ₜ[ℚ] d) := by
  rw [rawTensorLeftBoundary_inclusion]
  simp only [rawTensorLeftComponent, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]

@[simp] theorem rawTensorRightBoundary_tmul (p q : ℕ)
    (c : RawRationalChains X p) (d : RawRationalChains Y (q + 1)) :
    rawTensorRightBoundary X Y (rawTensorInclusion X Y p (q + 1) (c ⊗ₜ[ℚ] d)) =
      (-1 : ℚ) ^ p • rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] rawBoundary q d) := by
  rw [rawTensorRightBoundary_inclusion]
  simp only [rawTensorRightComponent, LinearMap.smul_apply, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]

end BanachIsometric.SingularAW
