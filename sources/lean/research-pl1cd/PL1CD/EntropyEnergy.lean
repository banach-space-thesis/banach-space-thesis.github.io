import PL1CD.Variation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology BigOperators

namespace PL1CD.EntropyEnergy

def average (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, v n

theorem energy_sum_le (v H : ℕ → ℝ)
    (hstep : ∀ n, v n ^ 2 ≤ 4 * (H (n + 1) - H n)) (N : ℕ) :
    ∑ n ∈ Finset.range N, v n ^ 2 ≤ 4 * (H N - H 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]

theorem average_sq_le (v H : ℕ → ℝ)
    (hstep : ∀ n, v n ^ 2 ≤ 4 * (H (n + 1) - H n)) {N : ℕ} (hN : 0 < N) :
    average v N ^ 2 ≤ 4 * (H N - H 0) / (N : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) v (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hcs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have henergy := energy_sum_le v H hstep N
  have h : (∑ n ∈ Finset.range N, v n) ^ 2 ≤
      (N : ℝ) * (4 * (H N - H 0)) := by
    calc
      _ ≤ (∑ n ∈ Finset.range N, v n ^ 2) * N := hcs
      _ ≤ (4 * (H N - H 0)) * N := mul_le_mul_of_nonneg_right henergy hN'.le
      _ = _ := mul_comm _ _
  dsimp [average]
  apply (le_div_iff₀ hN').mpr
  have hdiv := mul_le_mul_of_nonneg_left h (sq_nonneg (N : ℝ)⁻¹)
  field_simp at hdiv ⊢
  nlinarith

theorem average_le_sqrt (v H : ℕ → ℝ)
    (hstep : ∀ n, v n ^ 2 ≤ 4 * (H (n + 1) - H n)) {N : ℕ} (hN : 0 < N) :
    average v N ≤ Real.sqrt (4 * (H N - H 0) / (N : ℝ)) := by
  have hsq := average_sq_le v H hstep hN
  have hnonneg : 0 ≤ 4 * (H N - H 0) / (N : ℝ) := (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hnonneg
  nlinarith [Real.sqrt_nonneg (4 * (H N - H 0) / (N : ℝ))]

theorem average_tendsto_zero (v H : ℕ → ℝ) (N : ℕ → ℕ)
    (l : Filter ℕ) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, v n ^ 2 ≤ 4 * (H (n + 1) - H n))
    (hN : ∀ᶠ s in l, 0 < N s)
    (henergy : Tendsto (fun s => (H (N s) - H 0) / (N s : ℝ)) l (𝓝 0)) :
    Tendsto (fun s => average v (N s)) l (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun s => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun n _ => hv n))))
    (hN.mono (fun s hs => average_le_sqrt v H hstep hs))
  have ht := (Real.continuous_sqrt.tendsto (4 * (0 : ℝ))).comp
    ((tendsto_const_nhds (x := (4 : ℝ))).mul henergy)
  simpa only [Function.comp_def, mul_zero, Real.sqrt_zero, mul_div_assoc] using ht

end PL1CD.EntropyEnergy

namespace PL1CD.Variation

variable (𝕜 Z : Type*) [RCLike 𝕜]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem averagedVariation_eq_zero_of_entropy
    (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (T : HaarL1 𝕜 →L[𝕜] Z) (entropy : ℕ → ℝ)
    (hstep : ∀ n, (levelSeminorm 𝕜 Z M n T) ^ 2 ≤
      4 * (entropy (n + 1) - entropy n))
    (hN : ∀ᶠ s in atTop ⊓ 𝓟 H, 0 < N s)
    (henergy : Tendsto (fun s => (entropy (N s) - entropy 0) / (N s : ℝ))
      (atTop ⊓ 𝓟 H) (𝓝 0)) :
    averagedVariation 𝕜 Z M N H hH T = 0 := by
  let := alongInfinite_neBot hH
  apply PL1CD.limsupSeminorm_eq_zero_of_tendsto
  have ht := EntropyEnergy.average_tendsto_zero
    (fun n => levelSeminorm 𝕜 Z M n T) entropy N (atTop ⊓ 𝓟 H)
    (fun n => apply_nonneg _ _) hstep hN henergy
  simpa only [endpointSeminorm, averageSeminorm_apply, EntropyEnergy.average] using ht

end PL1CD.Variation
