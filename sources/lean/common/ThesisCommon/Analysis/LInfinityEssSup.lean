import ThesisCommon.Analysis.LInfinityL1Pairing

/-! The real essential supremum of a nonnegative L-infinity function equals
its actual norm, including the zero-measure case. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem linfty_norm_eq_essSup_of_nonneg (g : Lp ℝ ∞ μ) (hg : 0 ≤ g) :
    ‖g‖ = essSup (fun x => g x) μ := by
  by_cases hμ : μ = 0
  · subst μ
    simp [essSup_eq_sInf]
  letI : NeZero μ := ⟨hμ⟩
  have hp : ∀ᵐ x ∂μ, 0 ≤ g x := by simpa using (Lp.coeFn_nonneg g).mpr hg
  have hb : ∀ᵐ x ∂μ, g x ≤ ‖g‖ := (linfty_ae_norm_le_norm g).mono
    fun x hx => (le_abs_self (g x)).trans hx
  have he : ∀ᵐ x ∂μ, g x ≤ essSup (fun x => g x) μ := ae_le_essSup ⟨‖g‖, hb⟩
  have hepos : 0 ≤ essSup (fun x => g x) μ := by
    obtain ⟨x, hx, hx'⟩ := (hp.and he).exists
    exact hx.trans hx'
  apply le_antisymm
  · apply linfty_norm_le_of_ae_bound g hepos
    filter_upwards [hp, he] with x hx he
    rwa [Real.norm_of_nonneg hx]
  · exact limsup_le_of_le (isCoboundedUnder_le_of_eventually_le (ae μ) hp) hb

theorem linfty_norm_eq_essSup_of_ae_eq (g : Lp ℝ ∞ μ) {r : X → ℝ}
    (heq : g =ᵐ[μ] r) (hr : ∀ᵐ x ∂μ, 0 ≤ r x) : ‖g‖ = essSup r μ := by
  have hg : 0 ≤ g := by
    apply (Lp.coeFn_nonneg g).mp
    filter_upwards [heq, hr] with x hx hr
    change 0 ≤ g x
    rwa [hx]
  exact (linfty_norm_eq_essSup_of_nonneg g hg).trans (essSup_congr_ae heq)

end ThesisCommon
