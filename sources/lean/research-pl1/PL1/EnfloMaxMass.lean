import PL1.EnfloBush

/-! # Actual finite maxima and their dyadic operator seminorms -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PL1.EnfloBush

theorem maxAbs_le {n : ℕ} {a : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j < n, |a j| ≤ M) : maxAbs n a ≤ M := by
  induction n with
  | zero => exact hM
  | succ n ih => exact max_le (ih (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

theorem maxAbs_le_sum (n : ℕ) (a : ℕ → ℝ) :
    maxAbs n a ≤ ∑ j ∈ Finset.range n, |a j| :=
  maxAbs_le (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (fun _j hj => Finset.single_le_sum (f := fun i => |a i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hj))

theorem maxAbs_add_le (n : ℕ) (a b : ℕ → ℝ) :
    maxAbs n (fun j => a j + b j) ≤ maxAbs n a + maxAbs n b := by
  apply maxAbs_le (add_nonneg (maxAbs_nonneg n a) (maxAbs_nonneg n b))
  intro j hj
  exact (abs_add_le _ _).trans (add_le_add (abs_le_maxAbs a hj) (abs_le_maxAbs b hj))

theorem maxAbs_congr {n : ℕ} {a b : ℕ → ℝ} (h : ∀ j < n, a j = b j) :
    maxAbs n a = maxAbs n b := by
  apply le_antisymm
  · apply maxAbs_le (maxAbs_nonneg n b)
    intro j hj
    rw [h j hj]
    exact abs_le_maxAbs b hj
  · apply maxAbs_le (maxAbs_nonneg n a)
    intro j hj
    rw [← h j hj]
    exact abs_le_maxAbs a hj

section General
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def maxMass (n : ℕ) (f : ℕ → Lp ℝ 1 μ) : ℝ :=
  ∫ x, maxAbs n (fun j => f j x) ∂μ

theorem maxMass_nonneg (n : ℕ) (f : ℕ → Lp ℝ 1 μ) : 0 ≤ maxMass n f :=
  integral_nonneg (fun _ => maxAbs_nonneg n _)

theorem maxMass_le_sum_norm (n : ℕ) (f : ℕ → Lp ℝ 1 μ) :
    maxMass n f ≤ ∑ j ∈ Finset.range n, ‖f j‖ := by
  have h := integral_mono (integrable_maxAbs n f)
    (integrable_finsetSum _ (fun j _ => (L1.integrable_coeFn (f j)).abs))
    (fun x => maxAbs_le_sum n (fun j => f j x))
  rw [integral_finsetSum _ (fun j _ => (L1.integrable_coeFn (f j)).abs)] at h
  have he (j : ℕ) : (∫ x, |f j x| ∂μ) = ‖f j‖ := by
    simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm (f j)).symm
  simpa only [maxMass, he] using h

theorem maxMass_add_le (n : ℕ) (f g : ℕ → Lp ℝ 1 μ) :
    maxMass n (fun j => f j + g j) ≤ maxMass n f + maxMass n g := by
  rw [maxMass, maxMass, maxMass, ← integral_add (integrable_maxAbs n f) (integrable_maxAbs n g)]
  apply integral_mono_ae (integrable_maxAbs n _) ((integrable_maxAbs n f).add (integrable_maxAbs n g))
  filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_add (f j) (g j))] with x hx
  simpa only [hx, Pi.add_apply] using maxAbs_add_le n (fun j => f j x) (fun j => g j x)

theorem maxMass_le_add_sum_norm_sub (n : ℕ) (f g : ℕ → Lp ℝ 1 μ) :
    maxMass n f ≤ maxMass n g + ∑ j ∈ Finset.range n, ‖f j - g j‖ := by
  have h := maxMass_add_le n g (fun j => f j - g j)
  simp only [add_sub_cancel] at h
  exact h.trans (add_le_add le_rfl (maxMass_le_sum_norm n (fun j => f j - g j)))

end General

section Dyadic
open DyadicTrace
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def dyadicSumMass (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ n), ‖T (dyadicVector (𝕜 := ℝ) n j)‖

def dyadicMaxMass (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) : ℝ :=
  maxMass (2 ^ n) (fun j => T (dyadicVector (𝕜 := ℝ) n j))

theorem dyadicSumMass_nonneg (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    0 ≤ dyadicSumMass T n := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem dyadicSumMass_le (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    dyadicSumMass T n ≤ ‖T‖ := by
  calc
    _ ≤ ∑ j ∈ Finset.range (2 ^ n), ‖T‖ * ‖dyadicVector (𝕜 := ℝ) n j‖ :=
      Finset.sum_le_sum (fun j _ => T.le_opNorm _)
    _ = ‖T‖ := by rw [← Finset.mul_sum, sum_norm_dyadicVector, mul_one]

theorem dyadicMaxMass_nonneg (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    0 ≤ dyadicMaxMass T n := maxMass_nonneg _ _

theorem dyadicMaxMass_le_sum (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    dyadicMaxMass T n ≤ dyadicSumMass T n := maxMass_le_sum_norm _ _

theorem dyadicMaxMass_le (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    dyadicMaxMass T n ≤ ‖T‖ := (dyadicMaxMass_le_sum T n).trans (dyadicSumMass_le T n)

theorem dyadicMaxMass_le_add_norm_sub (T S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    dyadicMaxMass T n ≤ dyadicMaxMass S n + ‖T - S‖ := by
  have h := maxMass_le_add_sum_norm_sub (2 ^ n) (fun j => T (dyadicVector n j))
    (fun j => S (dyadicVector n j))
  exact h.trans (add_le_add le_rfl (dyadicSumMass_le (T - S) n))

def DyadicVanishing (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) : Prop :=
  Tendsto (dyadicMaxMass T) atTop (𝓝 0)

theorem not_boundedBelow_of_dyadicVanishing {T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ}
    (h : DyadicVanishing T) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ f : IntervalL1 ℝ, c * ‖f‖ ≤ ‖T f‖) : False := by
  have he : Tendsto (fun n => dyadicMaxMass T n * ‖T‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using h.mul_const ‖T‖
  have hle : c ^ 2 ≤ 0 := ge_of_tendsto he (Filter.Eventually.of_forall
    (fun n => dyadic_max_integral_mul_norm T hc.le hlower n))
  nlinarith

end Dyadic

#print axioms not_boundedBelow_of_dyadicVanishing
end PL1.EnfloBush
