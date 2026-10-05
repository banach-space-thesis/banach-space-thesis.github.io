import ThesisCommon.Analysis.ContinuousMapJordan

/-! Sharp norm identities for the Riesz--Kantorovich decomposition. -/
noncomputable section
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem continuousMapPositiveValue_le_add_negative (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) :
    continuousMapPositiveValue μ f ≤ μ f + continuousMapPositiveValue (-μ) f := by
  apply csSup_le (continuousMap_positive_image_nonempty μ hf)
  rintro y ⟨g, hg, rfl⟩
  have hfg : f-g ∈ Set.Icc 0 f := by
    exact ⟨sub_nonneg.2 hg.2, sub_le_self _ hg.1⟩
  have h := le_csSup (continuousMap_positive_image_bddAbove (-μ) f)
    (Set.mem_image_of_mem (-μ) hfg)
  change (-μ) (f-g) ≤ continuousMapPositiveValue (-μ) f at h
  simp only [ContinuousLinearMap.neg_apply, map_sub] at h
  linarith

theorem continuousMapPositiveValue_neg (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) :
    continuousMapPositiveValue (-μ) f = continuousMapPositiveValue μ f - μ f := by
  have h₁ := continuousMapPositiveValue_le_add_negative μ hf
  have h₂ := continuousMapPositiveValue_le_add_negative (-μ) hf
  simp only [neg_neg, ContinuousLinearMap.neg_apply] at h₂
  linarith

theorem continuousMapNegativePart_eq_positive_neg (μ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapNegativePart μ = continuousMapPositivePart (-μ) := by
  ext f
  have hp : continuousMapNegativePart μ f⁺ = continuousMapPositivePart (-μ) f⁺ := by
    change continuousMapPositivePart μ f⁺ - μ f⁺ = _
    rw [continuousMapPositivePart_apply_nonneg μ (posPart_nonneg f),
      continuousMapPositivePart_apply_nonneg (-μ) (posPart_nonneg f),
      continuousMapPositiveValue_neg μ (posPart_nonneg f)]
  have hn : continuousMapNegativePart μ f⁻ = continuousMapPositivePart (-μ) f⁻ := by
    change continuousMapPositivePart μ f⁻ - μ f⁻ = _
    rw [continuousMapPositivePart_apply_nonneg μ (negPart_nonneg f),
      continuousMapPositivePart_apply_nonneg (-μ) (negPart_nonneg f),
      continuousMapPositiveValue_neg μ (negPart_nonneg f)]
  calc
    continuousMapNegativePart μ f = continuousMapNegativePart μ (f⁺ - f⁻) := by
      rw [posPart_sub_negPart]
    _ = continuousMapPositivePart (-μ) (f⁺ - f⁻) := by rw [map_sub, map_sub, hp, hn]
    _ = continuousMapPositivePart (-μ) f := by rw [posPart_sub_negPart]

theorem norm_continuousMapNegativePart_le (μ : C(K, ℝ) →L[ℝ] ℝ) :
    ‖continuousMapNegativePart μ‖ ≤ ‖μ‖ := by
  rw [continuousMapNegativePart_eq_positive_neg]
  exact (norm_continuousMapPositivePart_le (-μ)).trans_eq (norm_neg μ)

theorem norm_positive_continuousMap_functional (Λ : C(K, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f) : ‖Λ‖ = Λ 1 := by
  let P := PositiveLinearMap.mk₀ Λ.toLinearMap hΛ
  have h1 : 0 ≤ (1 : C(K, ℝ)) := fun _ => zero_le_one
  have hpos : 0 ≤ Λ 1 := hΛ 1 h1
  have hbound : ∀ f : C(K, ℝ), ‖Λ f‖ ≤ Λ 1 * ‖f‖ := by
    intro f
    have hu : f ≤ ‖f‖ • (1 : C(K, ℝ)) := by
      intro t
      change f t ≤ ‖f‖ * 1
      simpa only [mul_one] using (le_abs_self (f t)).trans (f.norm_coe_le_norm t)
    have hl : -‖f‖ • (1 : C(K, ℝ)) ≤ f := by
      intro t
      change -‖f‖ * 1 ≤ f t
      have h := (neg_le_abs (f t)).trans (f.norm_coe_le_norm t)
      simpa only [mul_one, neg_neg] using (neg_le_neg h)
    have hu' : Λ f ≤ Λ (‖f‖ • (1 : C(K, ℝ))) := P.monotone hu
    have hl' : Λ (-‖f‖ • (1 : C(K, ℝ))) ≤ Λ f := P.monotone hl
    simp only [map_smul, smul_eq_mul] at hu' hl'
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  apply le_antisymm (ContinuousLinearMap.opNorm_le_bound Λ hpos hbound)
  have hone : ‖(1 : C(K, ℝ))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    simp
  exact (le_abs_self (Λ 1)).trans ((Λ.le_opNorm 1).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (norm_nonneg Λ)))

theorem continuousMapPositiveValue_one_bound (μ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapPositiveValue μ 1 ≤ (‖μ‖ + μ 1) / 2 := by
  have h1 : 0 ≤ (1 : C(K, ℝ)) := fun _ => zero_le_one
  apply csSup_le (continuousMap_positive_image_nonempty μ h1)
  rintro y ⟨g, hg, rfl⟩
  have hgNorm : ‖(2 : ℝ) • g - 1‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    change |2 * g t - 1| ≤ 1
    have h0 : 0 ≤ g t := hg.1 t
    have hle : g t ≤ 1 := hg.2 t
    rw [abs_le]
    constructor <;> linarith
  have h := (le_abs_self (μ ((2 : ℝ) • g - 1))).trans
    ((μ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hgNorm (norm_nonneg μ)))
  simp only [map_sub, map_smul, smul_eq_mul, mul_one] at h
  linarith

theorem continuousMap_jordan_norm (μ : C(K, ℝ) →L[ℝ] ℝ) :
    ‖continuousMapPositivePart μ‖ + ‖continuousMapNegativePart μ‖ = ‖μ‖ := by
  have hp := norm_positive_continuousMap_functional (continuousMapPositivePart μ)
    (fun _ h => continuousMapPositivePart_nonneg μ h)
  have hn := norm_positive_continuousMap_functional (continuousMapNegativePart μ)
    (fun _ h => continuousMapNegativePart_nonneg μ h)
  apply le_antisymm
  · rw [hp, hn]
    change continuousMapPositivePart μ 1 + (continuousMapPositivePart μ 1 - μ 1) ≤ ‖μ‖
    rw [continuousMapPositivePart_apply_nonneg μ (show 0 ≤ (1 : C(K, ℝ)) from fun _ => zero_le_one)]
    have h := continuousMapPositiveValue_one_bound μ
    linarith
  · have h := norm_sub_le (continuousMapPositivePart μ) (continuousMapNegativePart μ)
    rwa [continuousMap_jordan_decomposition] at h

end ThesisCommon
