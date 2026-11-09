import BanachIsometric.RawFactorContraction
import BanachIsometric.RawTensorTotalDegree

/-! Explicit homotopy maps on the actual raw tensor bicomplex. The second
term has the Koszul sign and the first-factor homology projector. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

def rawTensorLeftProjector : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X Y) (fun ij =>
    (rawTensorInclusion X Y ij.1 ij.2).comp
      (TensorProduct.map (rawFactorProjector X ij.1) LinearMap.id))

def rawTensorBothProjector : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X Y) (fun ij =>
    (rawTensorInclusion X Y ij.1 ij.2).comp
      (TensorProduct.map (rawFactorProjector X ij.1) (rawFactorProjector Y ij.2)))

def rawTensorLeftHomotopy : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X Y) (fun ij =>
    (rawTensorInclusion X Y (ij.1 + 1) ij.2).comp
      (TensorProduct.map (rawFactorContraction X ij.1) LinearMap.id))

def rawTensorRightHomotopy : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X Y) (fun ij =>
    (-1 : ℚ) ^ ij.1 • (rawTensorInclusion X Y ij.1 (ij.2 + 1)).comp
      (TensorProduct.map (rawFactorProjector X ij.1) (rawFactorContraction Y ij.2)))

def rawTensorTotalHomotopy : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y :=
  rawTensorLeftHomotopy X Y + rawTensorRightHomotopy X Y

@[simp] theorem rawTensorLeftProjector_tmul (p q : ℕ)
    (c : RawRationalChains X p) (d : RawRationalChains Y q) :
    rawTensorLeftProjector X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
      rawTensorInclusion X Y p q (rawFactorProjector X p c ⊗ₜ[ℚ] d) := by
  simp only [rawTensorLeftProjector, rawTensorInclusion, DirectSum.toModule_lof,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]

@[simp] theorem rawTensorBothProjector_tmul (p q : ℕ)
    (c : RawRationalChains X p) (d : RawRationalChains Y q) :
    rawTensorBothProjector X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
      rawTensorInclusion X Y p q (rawFactorProjector X p c ⊗ₜ[ℚ] rawFactorProjector Y q d) := by
  simp only [rawTensorBothProjector, rawTensorInclusion, DirectSum.toModule_lof,
    LinearMap.comp_apply, TensorProduct.map_tmul]

@[simp] theorem rawTensorLeftHomotopy_tmul (p q : ℕ)
    (c : RawRationalChains X p) (d : RawRationalChains Y q) :
    rawTensorLeftHomotopy X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
      rawTensorInclusion X Y (p + 1) q (rawFactorContraction X p c ⊗ₜ[ℚ] d) := by
  simp only [rawTensorLeftHomotopy, rawTensorInclusion, DirectSum.toModule_lof,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]

@[simp] theorem rawTensorRightHomotopy_tmul (p q : ℕ)
    (c : RawRationalChains X p) (d : RawRationalChains Y q) :
    rawTensorRightHomotopy X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
      (-1 : ℚ) ^ p • rawTensorInclusion X Y p (q + 1)
        (rawFactorProjector X p c ⊗ₜ[ℚ] rawFactorContraction Y q d) := by
  simp only [rawTensorRightHomotopy, rawTensorInclusion, DirectSum.toModule_lof,
    LinearMap.smul_apply, LinearMap.comp_apply, TensorProduct.map_tmul]

end BanachIsometric.SingularAW
