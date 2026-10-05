import ThesisCommon.Analysis.ContinuousMapComplexModulus
import ThesisCommon.Analysis.ContinuousMapDualCoordinates

/-! The constructed complex dual modulus is exactly the least upper bound
of the real parts of all unit-phase rotations. -/
noncomputable section
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem continuousMapComplexModulus_le (φ : C(K, ℂ) →L[ℂ] ℂ)
    (R : C(K, ℝ) →L[ℝ] ℝ)
    (hR : ∀ f, 0 ≤ f → ‖φ (continuousMapOfReal f)‖ ≤ R f) :
    continuousMapComplexModulus φ ≤ R := by
  intro f hf
  rw [continuousMapComplexModulus_apply_nonneg φ f hf]
  apply (continuousMapComplexModulusPos_isLUB φ f hf).2
  rintro _ ⟨d, rfl⟩
  calc
    continuousMapComplexDecompositionValue φ d ≤ ∑ i, R (d.part i) :=
      sum_le_sum fun i _ => hR _ (d.nonneg i)
    _ = R f := by rw [← map_sum, d.sum_eq]

theorem continuousMapDualRe_phase_le (φ : C(K, ℂ) →L[ℂ] ℂ)
    (a : ℂ) (ha : ‖a‖ ≤ 1) : continuousMapDualRe (a • φ) ≤ continuousMapComplexModulus φ := by
  intro f hf
  change (a * φ (continuousMapOfReal f)).re ≤ _
  calc
    (a * φ (continuousMapOfReal f)).re ≤ ‖a * φ (continuousMapOfReal f)‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ ≤ ‖φ (continuousMapOfReal f)‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ continuousMapComplexModulus φ f := continuousMapComplexModulus_dominates φ f hf

theorem continuousMapComplexModulus_isLUB (φ : C(K, ℂ) →L[ℂ] ℂ) :
    IsLUB {R | ∃ a : ℂ, ‖a‖ = 1 ∧ R = continuousMapDualRe (a • φ)}
      (continuousMapComplexModulus φ) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact continuousMapDualRe_phase_le φ a ha.le
  · intro R hR
    apply continuousMapComplexModulus_le φ R
    intro f hf
    obtain ⟨a, ha, he⟩ := Complex.exists_norm_eq_mul_self (φ (continuousMapOfReal f))
    have h := hR ⟨a, ha, rfl⟩ f hf
    change (a * φ (continuousMapOfReal f)).re ≤ R f at h
    rw [← he] at h
    exact h

end ThesisCommon
