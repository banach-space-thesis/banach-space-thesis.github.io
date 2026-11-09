import PL1.EnfloMaxMass
import PL1.ResolventAlmostInvariant

/-! Stability of actual dyadic maximum decay and the resolvent consequence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal NNReal

namespace PL1.EnfloBush

section General
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem maxMass_smul_le (n : ℕ) (f : ℕ → Lp ℝ 1 μ) (c : ℝ) :
    maxMass n (fun j => c • f j) ≤ |c| * maxMass n f := by
  rw [maxMass, maxMass, ← integral_const_mul]
  apply integral_mono_ae (integrable_maxAbs n _) ((integrable_maxAbs n f).const_mul |c|)
  filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_smul c (f j))] with x hx
  apply maxAbs_le (mul_nonneg (abs_nonneg c) (maxAbs_nonneg n _))
  intro j hj
  rw [hx j, Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_le_maxAbs (fun j => f j x) hj) (abs_nonneg c)

theorem DyadicVanishing.add {T S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ}
    (hT : DyadicVanishing T) (hS : DyadicVanishing S) : DyadicVanishing (T + S) := by
  apply squeeze_zero (dyadicMaxMass_nonneg (T + S))
    (fun n => maxMass_add_le (2 ^ n)
      (fun j => T (DyadicTrace.dyadicVector n j))
      (fun j => S (DyadicTrace.dyadicVector n j)))
  simpa only [dyadicMaxMass, add_zero] using Filter.Tendsto.add hT hS

theorem DyadicVanishing.smul {T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ}
    (hT : DyadicVanishing T) (c : ℝ) : DyadicVanishing (c • T) := by
  apply squeeze_zero (dyadicMaxMass_nonneg (c • T))
    (fun n => maxMass_smul_le (2 ^ n) (fun j => T (DyadicTrace.dyadicVector n j)) c)
  simpa only [dyadicMaxMass, mul_zero] using hT.const_mul |c|

theorem DyadicVanishing.sub {T S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ}
    (hT : DyadicVanishing T) (hS : DyadicVanishing S) : DyadicVanishing (T - S) := by
  have he : T - S = T + (-1 : ℝ) • S := by
    exact (sub_eq_add_neg T S).trans
      (congrArg (fun A => T + A) (neg_one_smul ℝ S).symm)
  rw [he]
  exact hT.add (hS.smul (-1))

theorem dyadicVanishing_of_approximation (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ,
      DyadicVanishing S ∧ ‖T - S‖ < ε) : DyadicVanishing T := by
  rw [DyadicVanishing, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS, hnorm⟩ := h (ε / 2) (half_pos hε)
  have hs := Metric.tendsto_nhds.mp hS (ε / 2) (half_pos hε)
  filter_upwards [hs] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dyadicMaxMass_nonneg T n)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dyadicMaxMass_nonneg S n)] at hn
  exact (dyadicMaxMass_le_add_norm_sub T S n).trans_lt (by linarith)

theorem dyadicVanishing_of_opNorm_tendsto
    (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    (S : ℕ → IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    (hS : ∀ n, DyadicVanishing (S n))
    (ht : Tendsto (fun n => ‖S n - T‖) atTop (𝓝 0)) : DyadicVanishing T := by
  apply dyadicVanishing_of_approximation T
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  exact ⟨S n, hS n, by simpa only [norm_sub_rev] using hn⟩

end General

open Walsh Noise

theorem dyadicVanishing_resolvent_of_noise (rates : ℕ → ℝ≥0)
    (hnoise : ∀ (u : ℝ≥0), 0 < u →
      ∀ S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar,
        DyadicVanishing ((noiseL1 ℝ rates u).comp S))
    (t : PositiveTime) (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar) :
    DyadicVanishing ((resolventL1 ℝ rates t).comp S) := by
  let u : ℕ → ℝ≥0 := fun n => ⟨(1 / 2 : ℝ) ^ n, by positivity⟩
  let A := (resolventL1 ℝ rates t).comp S
  let B : ℕ → IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar :=
    fun n => (noiseL1 ℝ rates (u n)).comp A
  apply dyadicVanishing_of_opNorm_tendsto A B
  · intro n
    exact hnoise (u n) (by change 0 < (1 / 2 : ℝ) ^ n; positivity) A
  · have hb (n : ℕ) : ‖B n - A‖ ≤ (2 * (u n : ℝ) / (t : ℝ)) * ‖S‖ := by
      have he : B n - A =
          ((noiseL1 ℝ rates (u n)).comp (resolventL1 ℝ rates t) -
            resolventL1 ℝ rates t).comp S := by
        apply ContinuousLinearMap.ext
        intro f
        rfl
      rw [he]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right
          (norm_noise_comp_resolvent_sub_le_time ℝ rates t (u n)) (norm_nonneg S))
    apply squeeze_zero (fun n => norm_nonneg _) hb
    have hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using ((hu.const_mul 2).div_const (t : ℝ)).mul_const ‖S‖

end PL1.EnfloBush
