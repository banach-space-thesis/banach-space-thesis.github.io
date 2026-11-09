import BanachIsometric.RawTensorTotalDegree

/-! The canonical additive-group instances of the rational tensor factors,
their direct sum, and the genuine homogeneous submodules. The instances
retain the existing addition and rational scalar multiplication. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

instance rawBigradedTensorChainsAddCommGroup : AddCommGroup (RawBigradedTensorChains X Y) := by
  letI tensorGroup : ∀ ij : ℕ × ℕ, AddCommGroup (RawTensorChains X Y ij.1 ij.2) := fun ij => by
    change AddCommGroup (RawRationalChains X ij.1 ⊗[ℚ] RawRationalChains Y ij.2)
    exact TensorProduct.addCommGroup
  change AddCommGroup (⨁ ij : ℕ × ℕ, RawTensorChains X Y ij.1 ij.2)
  infer_instance

instance rawTensorTotalDegreeAddCommGroup (n : ℕ) : AddCommGroup (rawTensorTotalDegree X Y n) :=
  Submodule.addCommGroup (rawTensorTotalDegree X Y n)

end BanachIsometric.SingularAW
