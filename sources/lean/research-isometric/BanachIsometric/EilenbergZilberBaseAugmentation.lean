import BanachIsometric.EilenbergZilberUniversalEvaluation
import BanachIsometric.RawTensorAugmentationBoundary
import BanachIsometric.PathConnectedZeroChainFilling

/-! The actual universal degree-zero product chain has coefficient one.
Its evaluated crossproduct preserves the literal product augmentation. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct

def universalProductBase : UniversalProductChains 0 := fun p q _ =>
  Finsupp.single (ContinuousMap.const (Simplex 0) (simplexVertex p 0, simplexVertex q 0)) 1

theorem universalProductBase_augmentation (p q : ℕ) (h : p + q = 0) :
    rawAugmentation (Simplex p × Simplex q) (universalProductBase p q h) = 1 :=
  rawAugmentation_single _ _ 1

theorem universalProductBase_evaluation_augmentation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    (rawAugmentation (X × Y)).comp (universalCrossEvaluation (X := X) (Y := Y) universalProductBase) =
      rawTensorAugmentation X Y := by
  classical
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  by_cases h : p + q = 0
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    apply TensorProduct.ext
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    apply Finsupp.lhom_ext'
    intro τ
    apply LinearMap.ext_ring
    change rawAugmentation (X × Y) (universalCrossEvaluation universalProductBase
        (rawTensorInclusion X Y 0 0 (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1))) =
      rawTensorZeroAugmentation X Y
        (rawTensorComponent X Y 0 0 (rawTensorInclusion X Y 0 0
          (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)))
    rw [universalCrossEvaluation_inclusion universalProductBase rfl, universalCrossBidegree_single,
      rawTensorComponent_inclusion, rawTensorZeroAugmentation_tmul,
      rawAugmentation_single, rawAugmentation_single, mul_one]
    simp only [one_smul]
    have hn := LinearMap.congr_fun (rawAugmentation_natural (awProductMap σ τ))
      (universalProductBase 0 0 rfl)
    exact hn.trans (universalProductBase_augmentation 0 0 rfl)
  · apply LinearMap.ext
    intro c
    change rawAugmentation (X × Y) (universalCrossEvaluation universalProductBase
        (rawTensorInclusion X Y p q c)) =
      rawTensorZeroAugmentation X Y (rawTensorComponent X Y 0 0 (rawTensorInclusion X Y p q c))
    have hpq : (p, q) ≠ (0, 0) := by
      intro he
      have hp := congrArg Prod.fst he
      have hq := congrArg Prod.snd he
      change p = 0 at hp
      change q = 0 at hq
      exact h (by omega)
    rw [universalCrossEvaluation_inclusion_of_ne universalProductBase h, map_zero,
      rawTensorComponent_inclusion_of_ne X Y hpq, map_zero]

theorem universalProductBase_boundary_augmentation (p q : ℕ) :
    rawAugmentation (Simplex p × Simplex q) (universalCrossEvaluation universalProductBase
      (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))) = 0 := by
  have he := LinearMap.congr_fun
    (universalProductBase_evaluation_augmentation (X := Simplex p) (Y := Simplex q))
    (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))
  have hd := LinearMap.congr_fun (rawTensorAugmentation_boundary (Simplex p) (Simplex q))
    (universalTensorGenerator p q)
  exact he.trans hd

end BanachIsometric.SingularEZ
