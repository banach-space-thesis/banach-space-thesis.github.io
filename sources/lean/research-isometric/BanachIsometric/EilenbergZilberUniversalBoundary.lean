import BanachIsometric.EilenbergZilberUniversalEvaluation

/-! A literal universal boundary identity extends to the actual crossproduct
chain identity by natural pushforward. The universal identities will be
constructed from acyclic-model fillings, rather than postulated for EZ. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem universalCrossEvaluation_leftComponent_of_ne {n p q : ℕ}
    (U : UniversalProductChains n) (h : p + q ≠ n + 1) (c : RawTensorChains X Y p q) :
    universalCrossEvaluation U (rawTensorLeftComponent X Y p q c) = 0 := by
  cases p with
  | zero => simp only [rawTensorLeftComponent, LinearMap.zero_apply, map_zero]
  | succ p =>
    change universalCrossEvaluation U
      (rawTensorInclusion X Y p q (TensorProduct.map (rawBoundary p) LinearMap.id c)) = 0
    exact universalCrossEvaluation_inclusion_of_ne U (by omega) _

theorem universalCrossEvaluation_rightComponent_of_ne {n p q : ℕ}
    (U : UniversalProductChains n) (h : p + q ≠ n + 1) (c : RawTensorChains X Y p q) :
    universalCrossEvaluation U (rawTensorRightComponent X Y p q c) = 0 := by
  cases q with
  | zero => simp only [rawTensorRightComponent, LinearMap.zero_apply, map_zero]
  | succ q =>
    change universalCrossEvaluation U
      ((-1 : ℚ) ^ p • rawTensorInclusion X Y p q
        (TensorProduct.map LinearMap.id (rawBoundary q) c)) = 0
    rw [map_smul, universalCrossEvaluation_inclusion_of_ne U (by omega), smul_zero]

theorem universalCrossEvaluation_boundary_inclusion_of_ne {n p q : ℕ}
    (U : UniversalProductChains n) (h : p + q ≠ n + 1) (c : RawTensorChains X Y p q) :
    universalCrossEvaluation U (rawTensorTotalBoundary X Y (rawTensorInclusion X Y p q c)) = 0 := by
  rw [rawTensorTotalBoundary_inclusion, map_add,
    universalCrossEvaluation_leftComponent_of_ne U h,
    universalCrossEvaluation_rightComponent_of_ne U h, add_zero]

def UniversalBoundaryCompatible {n : ℕ}
    (U : UniversalProductChains n) (V : UniversalProductChains (n + 1)) : Prop :=
  ∀ p q : ℕ, ∀ h : p + q = n + 1,
    rawBoundary n (V p q h) =
      universalCrossEvaluation U
        (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))

theorem universalCrossEvaluation_boundary_of_compatible {n : ℕ}
    {U : UniversalProductChains n} {V : UniversalProductChains (n + 1)}
    (hUV : UniversalBoundaryCompatible U V) :
    (rawBoundary (X := X × Y) n).comp (universalCrossEvaluation V) =
      (universalCrossEvaluation U).comp (rawTensorTotalBoundary X Y) := by
  classical
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  by_cases h : p + q = n + 1
  · apply TensorProduct.ext
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    apply Finsupp.lhom_ext'
    intro τ
    apply LinearMap.ext_ring
    change rawBoundary n (universalCrossEvaluation V (rawTensorInclusion X Y p q
        (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1))) =
      universalCrossEvaluation U (rawTensorTotalBoundary X Y
        (rawTensorInclusion X Y p q (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)))
    rw [universalCrossEvaluation_inclusion V h, universalCrossBidegree_single, one_smul, one_smul]
    calc
      rawBoundary n (rawChainMap (awProductMap σ τ) (n + 1) (V p q h)) =
          rawChainMap (awProductMap σ τ) n (rawBoundary n (V p q h)) :=
        LinearMap.congr_fun (rawChainMap_boundary (awProductMap σ τ) n) (V p q h)
      _ = rawChainMap (awProductMap σ τ) n (universalCrossEvaluation U
          (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))) := by
        rw [hUV p q h]
      _ = universalCrossEvaluation U (rawBigradedTensorMap σ τ
          (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))) :=
        (LinearMap.congr_fun (universalCrossEvaluation_naturality U σ τ)
          (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))).symm
      _ = universalCrossEvaluation U (rawTensorTotalBoundary X Y
          (rawBigradedTensorMap σ τ (universalTensorGenerator p q))) :=
        congrArg (universalCrossEvaluation U)
          (LinearMap.congr_fun (rawBigradedTensorMap_boundary σ τ) (universalTensorGenerator p q))
      _ = _ := by rw [universalTensorGenerator_pushforward]
  · apply LinearMap.ext
    intro c
    change rawBoundary n (universalCrossEvaluation V (rawTensorInclusion X Y p q c)) =
      universalCrossEvaluation U (rawTensorTotalBoundary X Y (rawTensorInclusion X Y p q c))
    rw [universalCrossEvaluation_inclusion_of_ne V h, map_zero,
      universalCrossEvaluation_boundary_inclusion_of_ne U h]

end BanachIsometric.SingularEZ
