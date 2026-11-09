import BanachIsometric.KoszulTensorAssociativity
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Module.TransferInstance

/-! A separately tagged ring and algebra for the Koszul tensor product.
Its underlying additive group and K-action are the genuine tensor ones.
Its multiplication is the constructed graded product. The ordinary tensor
ring remains a distinct existing object with its original multiplication. -/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

structure KoszulTensor (𝒜 : ℕ → Submodule K A) where
  val : A ⊗[K] A

namespace KoszulTensor

variable (𝒜 : ℕ → Submodule K A)

theorem val_injective : Function.Injective (val (𝒜 := 𝒜)) := by
  intro x y h
  cases x
  cases y
  cases h
  rfl

def tensorEquiv : KoszulTensor 𝒜 ≃ A ⊗[K] A where
  toFun := val
  invFun := mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : Zero (KoszulTensor 𝒜) := ⟨⟨0⟩⟩
instance : Add (KoszulTensor 𝒜) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Neg (KoszulTensor 𝒜) := ⟨fun x => ⟨-x.val⟩⟩
instance : One (KoszulTensor 𝒜) := ⟨⟨1 ⊗ₜ[K] 1⟩⟩

@[simp] theorem val_zero : (0 : KoszulTensor 𝒜).val = 0 := rfl
@[simp] theorem val_one : (1 : KoszulTensor 𝒜).val = 1 ⊗ₜ[K] 1 := rfl
@[simp] theorem val_add (x y : KoszulTensor 𝒜) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_neg (x : KoszulTensor 𝒜) : (-x).val = -x.val := rfl

variable [GradedAlgebra 𝒜]

instance : Mul (KoszulTensor 𝒜) := ⟨fun x y => ⟨koszulTensorMul 𝒜 x.val y.val⟩⟩

instance : Ring (KoszulTensor 𝒜) := Ring.ofMinimalAxioms
  (fun x y z => val_injective 𝒜 (add_assoc x.val y.val z.val))
  (fun x => val_injective 𝒜 (zero_add x.val))
  (fun x => val_injective 𝒜 (neg_add_cancel x.val))
  (fun x y z => val_injective 𝒜 (koszulTensorMul_assoc 𝒜 x.val y.val z.val))
  (fun x => val_injective 𝒜 (koszulTensorMul_one_left 𝒜 x.val))
  (fun x => val_injective 𝒜 (koszulTensorMul_one_right 𝒜 x.val))
  (fun x y z => val_injective 𝒜 ((koszulTensorMul 𝒜 x.val).map_add y.val z.val))
  (fun x y z => val_injective 𝒜 (congrArg (fun L : A ⊗[K] A →ₗ[K] A ⊗[K] A => L z.val)
    ((koszulTensorMul 𝒜).map_add x.val y.val)))

def tensorAddEquiv : KoszulTensor 𝒜 ≃+ A ⊗[K] A where
  toEquiv := tensorEquiv 𝒜
  map_add' := fun _ _ => rfl

instance : Module K (KoszulTensor 𝒜) := (tensorAddEquiv 𝒜).module K

def tensorLinearEquiv : KoszulTensor 𝒜 ≃ₗ[K] A ⊗[K] A where
  toAddEquiv := tensorAddEquiv 𝒜
  map_smul' := fun _ _ => rfl

instance : Algebra K (KoszulTensor 𝒜) := Algebra.ofModule
  (fun r x y => by
    apply val_injective 𝒜
    change koszulTensorMul 𝒜 (r • x.val) y.val = r • koszulTensorMul 𝒜 x.val y.val
    exact congrArg (fun L : A ⊗[K] A →ₗ[K] A ⊗[K] A => L y.val)
      ((koszulTensorMul 𝒜).map_smul r x.val))
  (fun r x y => by
    apply val_injective 𝒜
    change koszulTensorMul 𝒜 x.val (r • y.val) = r • koszulTensorMul 𝒜 x.val y.val
    exact (koszulTensorMul 𝒜 x.val).map_smul r y.val)

@[simp] theorem val_smul (r : K) (x : KoszulTensor 𝒜) : (r • x).val = r • x.val := rfl
@[simp] theorem val_mul (x y : KoszulTensor 𝒜) :
    (x * y).val = koszulTensorMul 𝒜 x.val y.val := rfl
@[simp] theorem val_algebraMap (r : K) :
    (algebraMap K (KoszulTensor 𝒜) r).val = r • (1 ⊗ₜ[K] 1) := rfl

def tmul (a b : A) : KoszulTensor 𝒜 := ⟨a ⊗ₜ[K] b⟩

theorem tmul_mul_of_mem (a d : A) {j k : ℕ} {b c : A}
    (hb : b ∈ 𝒜 j) (hc : c ∈ 𝒜 k) :
    tmul 𝒜 a b * tmul 𝒜 c d =
      (-1 : K) ^ (j * k) • tmul 𝒜 (a * c) (b * d) := by
  apply val_injective 𝒜
  exact koszulTensorMul_homogeneous_tmul 𝒜 a d hb hc

end KoszulTensor
end BanachIsometric
