import BanachIsometric.SingularKunneth

/-! The external product on actual rational singular homology, and its
literal tensor-of-cycles formula. A supplied total degree avoids casts in
later comparisons of parenthesizations. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW VectorChainSplitting
open scoped TensorProduct

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

def rawHomologyCross {n p q : ℕ} (h : p + q = n) :
    RawHomology X p →ₗ[ℚ] RawHomology Y q →ₗ[ℚ] RawHomology (X × Y) n :=
  TensorProduct.curry ((rawSingularKunnethEquiv X Y n).symm.toLinearMap.comp (rawHomologyTensorInclusion X Y h))

theorem rawHomologyCross_apply {n p q : ℕ} (h : p + q = n) (a : RawHomology X p)
    (b : RawHomology Y q) :
    rawHomologyCross X Y h a b =
      (rawSingularKunnethEquiv X Y n).symm (rawHomologyTensorInclusion X Y h (a ⊗ₜ[ℚ] b)) :=
  rfl

theorem rawHomologyCross_compare {n p q : ℕ} (h : p + q = n) (a : RawHomology X p)
    (b : RawHomology Y q) :
    rawSingularKunnethEquiv X Y n (rawHomologyCross X Y h a b) =
      rawHomologyTensorInclusion X Y h (a ⊗ₜ[ℚ] b) :=
  (rawSingularKunnethEquiv X Y n).apply_symm_apply _

theorem rawTensorPureCycle_boundary {p q : ℕ}
    (a : RawHomologyCycles X p) (b : RawHomologyCycles Y q) :
    rawTensorTotalBoundary X Y (rawTensorInclusion X Y p q (a.val ⊗ₜ[ℚ] b.val)) = 0 := by
  have hleft : rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (a.val ⊗ₜ[ℚ] b.val)) = 0 := by
    cases p with
    | zero => simp only [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent, LinearMap.zero_apply]
    | succ p =>
      rw [rawTensorLeftBoundary_tmul, show rawBoundary p a.val = 0 from a.property,
        TensorProduct.zero_tmul, map_zero]
  have hright : rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (a.val ⊗ₜ[ℚ] b.val)) = 0 := by
    cases q with
    | zero => simp only [rawTensorRightBoundary_inclusion, rawTensorRightComponent, LinearMap.zero_apply]
    | succ q =>
      rw [rawTensorRightBoundary_tmul, show rawBoundary q b.val = 0 from b.property,
        TensorProduct.tmul_zero, map_zero, smul_zero]
  simp only [rawTensorTotalBoundary, LinearMap.add_apply, hleft, hright, add_zero]

def rawTensorPureCycle {n p q : ℕ} (h : p + q = n) (a : RawHomologyCycles X p)
    (b : RawHomologyCycles Y q) : rawTensorCycles X Y n :=
  rawTensorCyclesOfTotalBoundaryZero X Y n (rawTensorHomogeneousInclusion h (a.val ⊗ₜ[ℚ] b.val))
    (rawTensorPureCycle_boundary X Y a b)

theorem rawHomologyCross_cycle {n p q : ℕ} (h : p + q = n) (a : RawHomologyCycles X p)
    (b : RawHomologyCycles Y q) :
    rawHomologyCross X Y h (rawFactorHomologyProjection X p a.val) (rawFactorHomologyProjection Y q b.val) =
      rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilberTotal n
        (rawTensorInclusion X Y p q (a.val ⊗ₜ[ℚ] b.val))) := by
  rw [rawHomologyCross_apply]
  have he := rawSingularKunnethEquiv_symm_tensorCycle X Y n (rawTensorPureCycle X Y h a b)
  change (rawSingularKunnethEquiv X Y n).symm
      (rawTensorHomologyProjection X Y n (rawTensorHomogeneousInclusion h (a.val ⊗ₜ[ℚ] b.val))) = _ at he
  rw [rawTensorHomologyProjection_tmul] at he
  exact he

end BanachIsometric.SingularEZ
