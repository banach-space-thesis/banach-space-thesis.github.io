import PL1CD.HaarEntropyContraction

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1CD.Entropy
open PL1.Walsh

theorem integrable_phi_of_ae_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Lp ℝ 1 μ) (C : ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 C) : Integrable (fun x => phi (f x)) μ := by
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).image
    Real.continuous_mul_log).isBounded.exists_norm_le
  exact (MemLp.of_bound (p := 1)
    (Real.continuous_mul_log.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) B
    (hf.mono (fun x hx => hB _ ⟨f x, hx, rfl⟩))).integrable (by norm_num)

theorem phi_le_mul_log_bound {x C : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C) :
    phi x ≤ x * Real.log C := by
  by_cases hz : x = 0
  · simp [hz, phi]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_of_le_of_ne hx (Ne.symm hz)) hxC) hx

theorem Ent_eq_relativeEntropy (f : Lp ℝ 1 haar) (C : ℝ)
    (hf : ∀ᵐ x ∂haar, f x ∈ Set.Icc 0 C) :
    Ent f = ∫ x, f x * Real.log (f x / (∫ y, f y ∂haar)) ∂haar := by
  have hn : 0 ≤ᵐ[haar] f := hf.mono (fun x hx => hx.1)
  by_cases hq : (∫ x, f x ∂haar) = 0
  · have hz := (integral_eq_zero_iff_of_nonneg_ae hn (L1.integrable_coeFn f)).mp hq
    have hphi : Phi haar f = 0 := by
      unfold Phi
      calc
        _ = ∫ _x : PL1.Walsh.Group, (0 : ℝ) ∂haar := by
          apply integral_congr_ae
          filter_upwards [hz] with x hx
          simp only [hx, Pi.zero_apply, phi, zero_mul]
        _ = 0 := integral_zero _ _
    simp only [Ent, hq, hphi, phi, Real.log_zero, zero_mul, sub_zero,
      div_zero, mul_zero, integral_zero]
  · have he : (fun x => f x * Real.log (f x / (∫ y, f y ∂haar))) =ᵐ[haar]
        (fun x => phi (f x) - f x * Real.log (∫ y, f y ∂haar)) := by
      filter_upwards [hn] with x hx
      by_cases hx0 : f x = 0
      · simp [hx0, phi]
      · rw [Real.log_div hx0 hq]
        unfold phi
        ring
    rw [integral_congr_ae he, integral_sub (integrable_phi_of_ae_bound haar f C hf)
      ((L1.integrable_coeFn f).mul_const _), integral_mul_const]
    rfl

theorem Ent_le_log_bound_add_one (f : Lp ℝ 1 haar) (C : ℝ) (hC : 1 ≤ C)
    (hf : ∀ᵐ x ∂haar, f x ∈ Set.Icc 0 C)
    (hmass : ∫ x, f x ∂haar ≤ 1) : Ent f ≤ Real.log C + 1 := by
  have hq : 0 ≤ ∫ x, f x ∂haar := integral_nonneg_of_ae (hf.mono (fun x hx => hx.1))
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hphi : Phi haar f ≤ (∫ x, f x ∂haar) * Real.log C := by
    unfold Phi
    rw [← integral_mul_const]
    exact integral_mono_ae (integrable_phi_of_ae_bound haar f C hf)
      ((L1.integrable_coeFn f).mul_const _) (hf.mono
        (fun x hx => phi_le_mul_log_bound hx.1 hx.2))
  have hlow := Real.self_sub_one_le_mul_log hq
  have hm := mul_le_mul_of_nonneg_right hmass hlog
  unfold Ent phi
  linarith

theorem Phi_noise_le (rates : ℕ → ℝ≥0) (u a : ℝ≥0) (d : ℕ)
    (hrates : ∀ j, d ≤ j → (a : ℝ) ≤ rates j)
    (f : Lp ℝ 1 haar) (C : ℝ) (hC : 1 ≤ C)
    (hf : ∀ᵐ x ∂haar, f x ∈ Set.Icc 0 C)
    (hmass : ∫ x, f x ∂haar ≤ 1) :
    Phi haar (PL1.Noise.noiseL1 ℝ rates u f) ≤
      (d : ℝ) * Real.log 2 + Real.exp (-(u : ℝ) * a) * (Real.log C + 1) := by
  have h := Ent_noise_le rates u a d hrates f C hf
  have hm : (∫ x, PL1.Noise.noiseL1 ℝ rates u f x ∂haar) = ∫ x, f x ∂haar :=
    integral_convolutionL1 _ f
  have hq : 0 ≤ ∫ x, f x ∂haar := integral_nonneg_of_ae (hf.mono (fun x hx => hx.1))
  have hcorr : phi (∫ x, f x ∂haar) ≤ 0 := Real.mul_log_nonpos hq hmass
  have hhead := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (Nat.cast_nonneg d) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  have hent := mul_le_mul_of_nonneg_left (Ent_le_log_bound_add_one f C hC hf hmass)
    (Real.exp_pos (-(u : ℝ) * a)).le
  unfold Ent at h hent
  rw [hm] at h
  simp only [mul_one] at hhead
  linarith

end PL1CD.Entropy
