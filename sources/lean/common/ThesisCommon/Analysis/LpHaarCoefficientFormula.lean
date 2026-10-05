import ThesisCommon.Analysis.LpHaarAdjacentMeans
import ThesisCommon.Analysis.LpHaarLevelProjection

/-! Explicit integral coefficients and local formulas for the Haar-level maps. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace ThesisCommon

theorem lpHaarCoefficient_apply_integrals {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (f : Lp 𝕜 p μ) :
    lpHaarCoefficient s t hs ht hst f = (μ.real (s ∪ t) : 𝕜)⁻¹ *
      ((∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ) := by
  rw [lpHaarCoefficient_apply]
  have heq : (fun x => lpHaarFunction 𝕜 s t x * f x) = s.indicator f - t.indicator f := by
    funext x
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
      simp [lpHaarFunction, hxs, hxt]
  rw [heq]
  change (μ.real (s ∪ t) : 𝕜)⁻¹ * (∫ x, s.indicator f x - t.indicator f x ∂μ) = _
  rw [integral_sub (((Lp.memLp f).integrable Fact.out).indicator hs)
    (((Lp.memLp f).integrable Fact.out).indicator ht), integral_indicator hs, integral_indicator ht]

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem lpHaarDyadicCoefficient_apply_integrals (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k : ℕ) (hk : k < 2 ^ n) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 p n k f = (intervalLpDyadicRadius n : 𝕜)⁻¹ *
      ((∫ x in lpHaarCell (n + 1) (2 * k), f x ∂(volume.restrict (Icc (0 : ℝ) 1))) -
        ∫ x in lpHaarCell (n + 1) (2 * k + 1), f x ∂(volume.restrict (Icc (0 : ℝ) 1))) := by
  unfold lpHaarDyadicCoefficient
  rw [lpHaarCoefficient_apply_integrals, lpHaarCell_children, measureReal_def,
    lpHaarCell_measure n k hk, ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]

theorem lpHaarLevelProjection_restrict_parent (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarLevelProjection 𝕜 p n f) =
      lpHaarDyadicCoefficient 𝕜 p n k f •
        lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarDyadic 𝕜 p n k) := by
  rw [lpHaarLevelProjection_apply, map_sum]
  simp only [map_smul]
  apply Finset.sum_eq_single k
  · intro j _ hjk
    rw [lpHaarDyadic_restrict_other_parent 𝕜 p n j k
      (fun h => hjk (Fin.ext h.symm)), smul_zero]
  · simp

theorem lpHaarLevelProjection_coe_parent (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ lpHaarCell n k →
      lpHaarLevelProjection 𝕜 p n f x = lpHaarDyadicCoefficient 𝕜 p n k f *
        lpHaarFunction 𝕜 (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1)) x := by
  apply (ae_restrict_iff' (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)).mp
  have hEq := lpHaarLevelProjection_restrict_parent 𝕜 p n k f
  have hcoe := Lp.coeFn_smul (lpHaarDyadicCoefficient 𝕜 p n k f)
    (lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarDyadic 𝕜 p n k))
  rw [← hEq] at hcoe
  filter_upwards [hcoe,
    lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarLevelProjection 𝕜 p n f),
    lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarDyadic 𝕜 p n k),
    ae_restrict_of_ae (lpHaarVector_coe (𝕜 := 𝕜) (p := p.val)
      (μ := volume.restrict (Icc (0 : ℝ) 1))
      (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
      measurableSet_Ioc measurableSet_Ioc)] with x h₁ h₂ h₃ h₄
  change lpHaarDyadic 𝕜 p n k x = _ at h₄
  simpa only [Pi.smul_apply, smul_eq_mul, h₂, h₃, h₄] using h₁

end ThesisCommon
