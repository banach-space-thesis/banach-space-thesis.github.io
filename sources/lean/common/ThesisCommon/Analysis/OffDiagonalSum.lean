import ThesisCommon.Analysis.RosenthalSelection
import Mathlib.Tactic

/-! Absolute error bound after removing one atom from a supported series. -/
noncomputable section
namespace ThesisCommon

theorem abs_tsum_sub_le_offdiagonal (f w : ℕ → ℝ) (hw : Summable w)
    (hbound : ∀ k, |f k| ≤ w k) (J : Set ℕ)
    (hsupport : Function.support f ⊆ J) (n : ℕ) :
    |(∑' k, f k) - f n| ≤ ∑' k : ↥(J \ {n}), w k.val := by
  classical
  have hf : Summable f := hw.of_norm_bounded (by simpa only [Real.norm_eq_abs] using hbound)
  let g : ℕ → ℝ := fun k => if k = n then 0 else f k
  have hg : Summable g := by
    have : g = ({n}ᶜ : Set ℕ).indicator f := by funext k; simp [g, Set.indicator_apply]
    rw [this]
    exact hf.indicator _
  have hgs : Function.support g ⊆ J \ {n} := by
    intro k hk
    have hkn : k ≠ n := by intro h; subst k; simpa [g] using hk
    have hkf : f k ≠ 0 := by simpa [g, hkn] using hk
    exact ⟨hsupport hkf, hkn⟩
  have heq : (∑' k, f k) - f n = ∑' k : ↥(J \ {n}), g k.val := by
    rw [tsum_subtype_eq_of_support_subset hgs, hf.tsum_eq_add_tsum_ite n]
    dsimp [g]
    ring
  rw [heq]
  have hgn : Summable (fun k : ↥(J \ {n}) => ‖g k.val‖) := (hg.subtype _).norm
  calc
    |∑' k : ↥(J \ {n}), g k.val| ≤ ∑' k : ↥(J \ {n}), ‖g k.val‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hgn
    _ ≤ ∑' k : ↥(J \ {n}), w k.val := hgn.tsum_le_tsum (fun k => by
      have hkn : k.val ≠ n := k.property.2
      simpa [g, hkn, Real.norm_eq_abs] using hbound k.val) (hw.subtype _)

end ThesisCommon
