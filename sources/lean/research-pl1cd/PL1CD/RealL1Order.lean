import PL1.EnfloMajorant
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace PL1CD.L1Order

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def Nonneg (f : Lp ℝ 1 μ) : Prop := ∀ᵐ x ∂μ, 0 ≤ f x

theorem nonneg_iff_negPart_eq_zero (f : Lp ℝ 1 μ) : Nonneg f ↔ Lp.negPart f = 0 := by
  constructor
  · intro hf
    apply Lp.ext
    filter_upwards [hf, Lp.coeFn_negPart_eq_max f, Lp.coeFn_zero ℝ 1 μ] with x hx hn hz
    rw [hn, hz, Pi.zero_apply, max_eq_right (by linarith)]
  · intro hf
    have he := Lp.coeFn_negPart_eq_max f
    rw [hf] at he
    filter_upwards [he, Lp.coeFn_zero ℝ 1 μ] with x hx hz
    rw [hz, Pi.zero_apply] at hx
    have h := le_max_left (-f x) 0
    linarith

theorem nonneg_of_tendsto (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hf : ∀ n, Nonneg (f n)) (hfg : Tendsto f atTop (𝓝 g)) : Nonneg g := by
  rw [nonneg_iff_negPart_eq_zero]
  have ht := (Lp.continuous_negPart.tendsto g).comp hfg
  have hz (n : ℕ) := (nonneg_iff_negPart_eq_zero (f n)).mp (hf n)
  exact (tendsto_nhds_unique ht (by simpa only [Function.comp_def, hz] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp ℝ 1 μ)) atTop (𝓝 0))))

def absL1 (f : Lp ℝ 1 μ) : Lp ℝ 1 μ := Lp.posPart f + Lp.negPart f

theorem coeFn_absL1 (f : Lp ℝ 1 μ) : absL1 f =ᵐ[μ] fun x => |f x| := by
  filter_upwards [Lp.coeFn_add (Lp.posPart f) (Lp.negPart f),
    Lp.coeFn_posPart f, Lp.coeFn_negPart_eq_max f] with x ha hp hn
  change (Lp.posPart f + Lp.negPart f) x = |f x|
  rw [ha, Pi.add_apply, hp, hn]
  by_cases h : 0 ≤ f x
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith),
      abs_of_nonpos (le_of_not_ge h), zero_add]

theorem absL1_nonneg (f : Lp ℝ 1 μ) : Nonneg (absL1 f) :=
  (coeFn_absL1 f).mono (fun x hx => hx.symm ▸ abs_nonneg _)

theorem norm_absL1 (f : Lp ℝ 1 μ) : ‖absL1 f‖ = ‖f‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [coeFn_absL1 f] with x hx
  simp only [hx, Real.norm_eq_abs, abs_abs]

theorem exists_L1_limit_of_monotone (f : ℕ → Lp ℝ 1 μ)
    (hf : ∀ n, Nonneg (f n))
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => f n x)) (C : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ C) :
    ∃ g : Lp ℝ 1 μ, Nonneg g ∧ Tendsto f atTop (𝓝 g) ∧
      (∀ n, ∀ᵐ x ∂μ, f n x ≤ g x) ∧ ‖g‖ ≤ C := by
  let v : ℕ → Ω → ℝ := fun n x => max (f n x) 0
  have hv (n : ℕ) : v n =ᵐ[μ] f n :=
    (hf n).mono (fun x hx => max_eq_left hx)
  have hi (n : ℕ) : Integrable (v n) μ := (L1.integrable_coeFn (f n)).congr (hv n).symm
  have hpos (n : ℕ) (x : Ω) : 0 ≤ v n x := le_max_right _ _
  have hm : ∀ᵐ x ∂μ, Monotone (fun n => v n x) :=
    hmono.mono (fun x hx n m hnm => max_le_max (hx hnm) le_rfl)
  have hb (n : ℕ) : ∫ x, v n x ∂μ ≤ C := by
    calc
      _ = ‖f n‖ := by
        rw [L1.norm_eq_integral_norm]
        apply integral_congr_ae
        filter_upwards [hv n, hf n] with x hx hn
        exact hx.trans (Real.norm_of_nonneg hn).symm
      _ ≤ C := hbound n
  obtain ⟨b, hib, hb0, hvb⟩ := PL1.EnfloBush.exists_integrable_majorant_of_monotone
    v hi hpos hm hb
  let F : Ω → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (v n x)
  have hF : AEMeasurable F μ := AEMeasurable.iSup (fun n => (hi n).aemeasurable.ennreal_ofReal)
  have hFt : ∀ᵐ x ∂μ, F x ≠ ∞ := hvb.mono (fun x hx =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le (fun n => ENNReal.ofReal_le_ofReal (hx n))))
  have hFb : ∀ᵐ x ∂μ, (F x).toReal ≤ b x := by
    filter_upwards [hvb, hFt] with x hx ht
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (iSup_le (fun n => ENNReal.ofReal_le_ofReal (hx n)))
    simpa only [ENNReal.toReal_ofReal (hb0 x)] using h
  have hIF : Integrable (fun x => (F x).toReal) μ := hib.mono'
    hF.ennreal_toReal.aestronglyMeasurable
    (hFb.mono (fun x hx => by
      have he : |(F x).toReal| = (F x).toReal := abs_of_nonneg ENNReal.toReal_nonneg
      simpa only [Real.norm_eq_abs, he] using hx))
  let g := hIF.toL1 (fun x => (F x).toReal)
  have hg : Nonneg g := hIF.coeFn_toL1.mono (fun x hx => hx.symm ▸ ENNReal.toReal_nonneg)
  have hvg : ∀ n, ∀ᵐ x ∂μ, v n x ≤ (F x).toReal := by
    intro n
    filter_upwards [hFt] with x hx
    have h := ENNReal.toReal_mono hx (le_iSup (fun n => ENNReal.ofReal (v n x)) n)
    simpa only [ENNReal.toReal_ofReal (hpos n x)] using h
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 ((F x).toReal)) := by
    filter_upwards [hm, hFt] with x hx ht
    have h := (ENNReal.continuousAt_toReal ht).tendsto.comp
      (tendsto_atTop_iSup (fun n m hnm => ENNReal.ofReal_le_ofReal (hx hnm)))
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hpos _ x)] using h
  have hnorm : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0) := by
    have he (n : ℕ) : ‖f n - g‖ = ∫ x, |v n x - (F x).toReal| ∂μ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (f n) g, hv n, hIF.coeFn_toL1] with x hs hv hg
      rw [hs, Pi.sub_apply, ← hv, hg, Real.norm_eq_abs]
    simp_rw [he]
    have ht := tendsto_integral_of_dominated_convergence b
      (fun n => ((hi n).aestronglyMeasurable.sub hIF.aestronglyMeasurable).norm)
      hib (fun n => by
        filter_upwards [hvb, hvg n, hFb] with x hx hg hb
        change ‖‖v n x - (F x).toReal‖‖ ≤ b x
        rw [norm_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hg)]
        linarith [hpos n x])
      (hpoint.mono (fun x hx => by
        simpa only [Pi.sub_apply, sub_self, norm_zero, Real.norm_eq_abs] using
          (hx.sub_const ((F x).toReal)).norm))
    simpa only [Pi.sub_apply, Real.norm_eq_abs, integral_zero] using ht
  have ht : Tendsto f atTop (𝓝 g) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  refine ⟨g, hg, ht, ?_, le_of_tendsto ht.norm (Eventually.of_forall hbound)⟩
  intro n
  filter_upwards [hv n, hvg n, hIF.coeFn_toL1] with x hv hg he
  rwa [hv, ← he] at hg

end PL1CD.L1Order
