import PL1CD.PositiveKernelAverages
import PL1.L1Masks
import PL1.EnfloTruncation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace PL1CD.PositiveHaarOperators
open PL1.Walsh

def cutoffSet (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) : Set PL1.Walsh.Group :=
  {x | B oneL1 x ≤ b}

theorem measurableSet_cutoffSet (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) :
    MeasurableSet (cutoffSet B b) :=
  measurableSet_le (Lp.stronglyMeasurable (B oneL1)).measurable measurable_const

def cutoff (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) : HaarL1 →L[ℝ] HaarL1 :=
  (PL1.L1Masks.mask haar (cutoffSet B b) (measurableSet_cutoffSet B b)).comp B

def tail (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) : HaarL1 →L[ℝ] HaarL1 :=
  (PL1.L1Masks.mask haar (cutoffSet B b)ᶜ (measurableSet_cutoffSet B b).compl).comp B

theorem cutoff_add_tail (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) :
    cutoff B b + tail B b = B := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (cutoff B b f) (tail B b f),
    PL1.L1Masks.coeFn_mask haar (cutoffSet B b) (measurableSet_cutoffSet B b) (B f),
    PL1.L1Masks.coeFn_mask haar (cutoffSet B b)ᶜ
      (measurableSet_cutoffSet B b).compl (B f)] with x ha hb hc
  change (cutoff B b f + tail B b f) x = B f x
  change cutoff B b f x = (cutoffSet B b).indicator (B f) x at hb
  change tail B b f x = (cutoffSet B b)ᶜ.indicator (B f) x at hc
  rw [ha, Pi.add_apply, hb, hc]
  by_cases hx : x ∈ cutoffSet B b <;> simp [hx]

theorem mask_positive (A : Set PL1.Walsh.Group) (hA : MeasurableSet A) :
    IsPositive (PL1.L1Masks.mask haar A hA) := by
  intro f hf
  filter_upwards [hf, PL1.L1Masks.coeFn_mask haar A hA f] with x hx he
  rw [he]
  exact Set.indicator_nonneg (fun x _ => hx) x

theorem cutoff_positive (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (b : ℝ) :
    IsPositive (cutoff B b) := hB.comp (mask_positive _ _)

theorem tail_positive (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (b : ℝ) :
    IsPositive (tail B b) := hB.comp (mask_positive _ _)

theorem norm_cutoff_le (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) : ‖cutoff B b‖ ≤ ‖B‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (PL1.L1Masks.norm_mask_le_one haar (cutoffSet B b) (measurableSet_cutoffSet B b))
      (norm_nonneg B))

theorem cutoff_one_bound (B : HaarL1 →L[ℝ] HaarL1) (b : ℝ) (hb : 0 ≤ b) :
    ∀ᵐ x ∂haar, cutoff B b oneL1 x ≤ b := by
  filter_upwards [PL1.L1Masks.coeFn_mask haar (cutoffSet B b)
    (measurableSet_cutoffSet B b) (B oneL1)] with x he
  change PL1.L1Masks.mask haar (cutoffSet B b)
    (measurableSet_cutoffSet B b) (B oneL1) x ≤ b
  rw [he]
  by_cases hx : x ∈ cutoffSet B b
  · rw [Set.indicator_of_mem hx]
    exact hx
  · rwa [Set.indicator_of_notMem hx]

theorem tail_one_norm_tendsto_zero (B : HaarL1 →L[ℝ] HaarL1) :
    Tendsto (fun n : ℕ => ‖tail B (2 * (n : ℝ) + 2) oneL1‖) atTop (𝓝 0) := by
  let h := B oneL1
  let g : PL1.Walsh.Group → ℝ := fun x => ‖h x‖
  have hg : Integrable g haar := (L1.integrable_coeFn h).norm
  have hg0 : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  have hbound (n : ℕ) : ‖tail B (2 * (n : ℝ) + 2) oneL1‖ ≤
      2 * ∫ x, max (g x - (n : ℝ)) 0 ∂haar := by
    have hi : Integrable (fun x => max (g x - (n : ℝ)) 0) haar := by
      apply hg.mono'
      · exact (hg.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
          aestronglyMeasurable_const
      · exact ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (hg0 x))
    rw [L1.norm_eq_integral_norm, ← integral_const_mul]
    apply integral_mono_ae (L1.integrable_coeFn _).norm (hi.const_mul 2)
    filter_upwards [PL1.L1Masks.coeFn_mask haar
      (cutoffSet B (2 * (n : ℝ) + 2))ᶜ
      (measurableSet_cutoffSet B (2 * (n : ℝ) + 2)).compl h] with x he
    change ‖PL1.L1Masks.mask haar (cutoffSet B (2 * (n : ℝ) + 2))ᶜ
      (measurableSet_cutoffSet B (2 * (n : ℝ) + 2)).compl h x‖ ≤
        2 * max (g x - (n : ℝ)) 0
    rw [he]
    by_cases hx : x ∈ cutoffSet B (2 * (n : ℝ) + 2)
    · simp only [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx), norm_zero]
      positivity
    · rw [Set.indicator_of_mem (Set.mem_compl hx)]
      have hx' : 2 * (n : ℝ) + 2 < h x := lt_of_not_ge hx
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hh : 0 ≤ h x := by linarith
      change g x ≤ 2 * max (g x - (n : ℝ)) 0
      have hge : h x ≤ g x := by simp only [g, Real.norm_eq_abs]; exact le_abs_self _
      nlinarith [le_max_left (g x - (n : ℝ)) 0]
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa only [mul_zero] using
    (PL1.EnfloBush.integral_tail_tendsto_zero g hg hg0).const_mul 2

end PL1CD.PositiveHaarOperators
