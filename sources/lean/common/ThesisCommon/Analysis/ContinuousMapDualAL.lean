import ThesisCommon.Analysis.DualLatticeComplete
import ThesisCommon.Analysis.ContinuousMapJordanNorm
import ThesisCommon.Analysis.RealALModel

/-! The actual continuous real dual of C(K) is an intrinsic AL-space.
The lattice is the already constructed Riesz–Kantorovich dual lattice;
positivity identifies the operator norm with evaluation at the constant one. -/
noncomputable section
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

instance continuousMapReal_orderedModule : IsOrderedModule ℝ C(K, ℝ) :=
  IsOrderedModule.of_smul_nonneg fun r hr f hf t => mul_nonneg hr (hf t)

instance continuousMapReal_solidNorm : HasSolidNorm C(K, ℝ) where
  solid {f g} h := by
    apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
    intro t
    change |f t| ≤ ‖g‖
    have ht : |f t| ≤ |g t| := h t
    exact ht.trans (g.norm_coe_le_norm t)

open scoped PositiveOperatorOrder DualLattice

theorem norm_positive_continuousMapDual (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) :
    ‖φ‖ = φ 1 := norm_positive_continuousMap_functional φ ((operator_nonneg_iff φ).mp hφ)

theorem continuousMapDual_norm_add_of_nonneg
    (φ ψ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ) :
    ‖φ + ψ‖ = ‖φ‖ + ‖ψ‖ := by
  rw [norm_positive_continuousMapDual _ (add_nonneg hφ hψ),
    norm_positive_continuousMapDual _ hφ, norm_positive_continuousMapDual _ hψ]
  rfl

theorem continuousMap_real_dual_isALSpace : IsALSpace ℝ (C(K, ℝ) →L[ℝ] ℝ) :=
  isALSpace_of_real_lattice _ continuousMapDual_norm_add_of_nonneg

end ThesisCommon
