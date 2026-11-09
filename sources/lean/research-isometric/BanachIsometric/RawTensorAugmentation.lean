import BanachIsometric.RawFactorContraction
import BanachIsometric.RawTensorComponents

/-! The literal product augmentation controls the degree-zero tensor
homology projector on two contractible spaces. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

def rawFactorZeroRepresentative (x : X) : RawRationalChains X 0 :=
  rawFactorProjector X 0 (Finsupp.single (ContinuousMap.const (Simplex 0) x) 1)

theorem rawFactorProjector_zero_eq_augmentation_smul [ContractibleSpace X]
    (x : X) (c : RawRationalChains X 0) :
    rawFactorProjector X 0 c = rawAugmentation X c • rawFactorZeroRepresentative X x := by
  let e : RawRationalChains X 0 := Finsupp.single (ContinuousMap.const (Simplex 0) x) 1
  have he : rawAugmentation X e = 1 := rawAugmentation_single X _ 1
  have hz : rawAugmentation X (c - rawAugmentation X c • e) = 0 := by
    rw [map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
  have h := rawFactorProjector_zero_of_augmentation_eq_zero X hz
  rw [map_sub, map_smul] at h
  exact sub_eq_zero.mp h

def rawTensorZeroAugmentation : RawTensorChains X Y 0 0 →ₗ[ℚ] ℚ :=
  (TensorProduct.lid ℚ ℚ).toLinearMap.comp
    (TensorProduct.map (rawAugmentation X) (rawAugmentation Y))

theorem rawTensorZeroAugmentation_tmul
    (c : RawRationalChains X 0) (d : RawRationalChains Y 0) :
    rawTensorZeroAugmentation X Y (c ⊗ₜ[ℚ] d) = rawAugmentation X c * rawAugmentation Y d := by
  simp only [rawTensorZeroAugmentation, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul]

def rawTensorAugmentation : RawBigradedTensorChains X Y →ₗ[ℚ] ℚ :=
  (rawTensorZeroAugmentation X Y).comp (rawTensorComponent X Y 0 0)

theorem rawTensorZeroProjector_factor [ContractibleSpace X] [ContractibleSpace Y]
    (x : X) (y : Y) (c : RawTensorChains X Y 0 0) :
    TensorProduct.map (rawFactorProjector X 0) (rawFactorProjector Y 0) c =
      rawTensorZeroAugmentation X Y c •
        (rawFactorZeroRepresentative X x ⊗ₜ[ℚ] rawFactorZeroRepresentative Y y) := by
  have h : TensorProduct.map (rawFactorProjector X 0) (rawFactorProjector Y 0) =
      (rawTensorZeroAugmentation X Y).smulRight
        (rawFactorZeroRepresentative X x ⊗ₜ[ℚ] rawFactorZeroRepresentative Y y) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change TensorProduct.map (rawFactorProjector X 0) (rawFactorProjector Y 0) (a ⊗ₜ[ℚ] b) =
      rawTensorZeroAugmentation X Y (a ⊗ₜ[ℚ] b) •
        (rawFactorZeroRepresentative X x ⊗ₜ[ℚ] rawFactorZeroRepresentative Y y)
    rw [TensorProduct.map_tmul, rawFactorProjector_zero_eq_augmentation_smul X x,
      rawFactorProjector_zero_eq_augmentation_smul Y y, rawTensorZeroAugmentation_tmul,
      TensorProduct.smul_tmul_smul]
  exact LinearMap.congr_fun h c

theorem rawTensorZeroProjector_eq_zero_of_augmentation [ContractibleSpace X] [ContractibleSpace Y]
    {c : RawTensorChains X Y 0 0} (hc : rawTensorZeroAugmentation X Y c = 0) :
    TensorProduct.map (rawFactorProjector X 0) (rawFactorProjector Y 0) c = 0 := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  rw [rawTensorZeroProjector_factor X Y x y, hc, zero_smul]

end BanachIsometric.SingularAW
