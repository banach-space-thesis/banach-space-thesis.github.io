import PL1.DyadicTrace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Integrable envelopes and domination under L1 approximation

The target measure is arbitrary; in particular it may have infinite mass.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.TraceDomination

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- A monotone sequence of nonnegative integrable functions whose integrals
are uniformly bounded has an integrable common upper bound. -/
theorem exists_integrable_envelope (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Integrable (g n) μ) (hpos : ∀ n x, 0 ≤ g n x)
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => g n x))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ∫ x, g n x ∂μ ≤ C) :
    ∃ G : Ω → ℝ, Integrable G μ ∧ (∀ x, 0 ≤ G x) ∧
      (∫ x, G x ∂μ) ≤ C ∧ ∀ n, g n ≤ᵐ[μ] G := by
  let genv : Ω → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (g n x)
  have hgmeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (g n x)) μ :=
    (hg n).aemeasurable.ennreal_ofReal
  have hGmeas : AEMeasurable genv μ := .iSup hgmeas
  have hGeq : (∫⁻ x, genv x ∂μ) = ⨆ n, ∫⁻ x, ENNReal.ofReal (g n x) ∂μ := by
    apply lintegral_iSup' hgmeas
    exact hmono.mono (fun x hx n m hnm => ENNReal.ofReal_le_ofReal (hx hnm))
  have hGbound : (∫⁻ x, genv x ∂μ) ≤ ENNReal.ofReal C := by
    rw [hGeq]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hg n) (ae_of_all _ (hpos n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hGfinite : (∫⁻ x, genv x ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hGbound
  have hGae : ∀ᵐ x ∂μ, genv x < ∞ := ae_lt_top' hGmeas hGfinite
  refine ⟨fun x => (genv x).toReal, integrable_toReal_of_lintegral_ne_top hGmeas hGfinite,
    fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [integral_toReal hGmeas hGae]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGbound
    simpa only [ENNReal.toReal_ofReal hC] using h
  · intro n
    filter_upwards [hGae] with x hx
    have h := ENNReal.toReal_mono hx.ne (le_iSup (fun m => ENNReal.ofReal (g m x)) n)
    simpa only [ENNReal.toReal_ofReal (hpos n x)] using h

/-- A common almost-everywhere norm bound passes through convergence in L1. -/
theorem ae_norm_le_of_tendsto_L1 {𝕜 : Type*} [RCLike 𝕜]
    (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ) (G : Ω → ℝ)
    (hf : Tendsto f atTop (𝓝 g)) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ G x) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ G x := by
  obtain ⟨φ, hφ, ht⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  filter_upwards [ht, ae_all_iff.2 hbound] with x hx hb
  exact le_of_tendsto hx.norm (Eventually.of_forall (fun n => hb (φ n)))

private theorem sum_pairs (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N), f k) =
      ∑ i ∈ Finset.range N, (f (2 * i) + f (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ]
    simp only [show 2 * N + 2 = (2 * N + 1) + 1 by omega,
      Finset.sum_range_succ, ih]
    ring

section BinaryApproximation

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (e : ℕ → ℕ → E) (B : E →L[𝕜] Lp 𝕜 1 μ)

def binaryEnvelope (n : ℕ) (x : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ n), ‖B (e n i) x‖

theorem binaryEnvelope_nonneg (n : ℕ) (x : Ω) : 0 ≤ binaryEnvelope μ e B n x :=
  Finset.sum_nonneg (fun _i _ => norm_nonneg _)

theorem integrable_binaryEnvelope (n : ℕ) : Integrable (binaryEnvelope μ e B n) μ :=
  integrable_finsetSum _ (fun i _ => (L1.integrable_coeFn (B (e n i))).norm)

theorem integral_binaryEnvelope_le (hmass : ∀ n, ∑ i ∈ Finset.range (2 ^ n), ‖e n i‖ ≤ 1)
    (n : ℕ) : (∫ x, binaryEnvelope μ e B n x ∂μ) ≤ ‖B‖ := by
  unfold binaryEnvelope
  rw [integral_finsetSum _ (fun i _ => (L1.integrable_coeFn (B (e n i))).norm)]
  simp only [← L1.norm_eq_integral_norm]
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n), ‖B‖ * ‖e n i‖ := Finset.sum_le_sum (fun i _ => B.le_opNorm _)
    _ = ‖B‖ * ∑ i ∈ Finset.range (2 ^ n), ‖e n i‖ := by rw [Finset.mul_sum]
    _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left (hmass n) (norm_nonneg _)
    _ = ‖B‖ := mul_one _

theorem binaryEnvelope_monotone
    (hrefine : ∀ n i, i < 2 ^ n → e n i = e (n + 1) (2 * i) + e (n + 1) (2 * i + 1)) :
    ∀ᵐ x ∂μ, Monotone (fun n => binaryEnvelope μ e B n x) := by
  have href (n i : ℕ) : ∀ᵐ x ∂μ, i < 2 ^ n →
      B (e n i) x = B (e (n + 1) (2 * i)) x + B (e (n + 1) (2 * i + 1)) x := by
    by_cases hi : i < 2 ^ n
    · rw [hrefine n i hi, map_add]
      filter_upwards [Lp.coeFn_add (B (e (n + 1) (2 * i)))
        (B (e (n + 1) (2 * i + 1)))] with x hx
      exact fun _ => hx
    · exact ae_of_all _ (fun _ h => (hi h).elim)
  filter_upwards [ae_all_iff.2 (fun n => ae_all_iff.2 (href n))] with x hx
  apply monotone_nat_of_le_succ
  intro n
  unfold binaryEnvelope
  rw [pow_succ, Nat.mul_comm (2 ^ n) 2, sum_pairs]
  apply Finset.sum_le_sum
  intro i hi
  rw [hx n i (Finset.mem_range.mp hi)]
  exact norm_add_le _ _

theorem ae_norm_linearCombination_le_binaryEnvelope (n : ℕ) (c : ℕ → 𝕜)
    (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∀ᵐ x ∂μ, ‖B (∑ i ∈ Finset.range (2 ^ n), c i • e n i) x‖ ≤ binaryEnvelope μ e B n x := by
  simp only [map_sum, map_smul]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (2 ^ n))
    (fun i => c i • B (e n i)), ae_all_iff.2 (fun i => Lp.coeFn_smul (c i) (B (e n i)))]
    with x hsum hsmul
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n), ‖(c i • B (e n i)) x‖ := norm_sum_le _ _
    _ ≤ binaryEnvelope μ e B n x := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsmul i]
      change ‖c i • B (e n i) x‖ ≤ _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans_eq (one_mul _)

/-- An operator on a source with binary bounded step approximations admits
one integrable envelope for the specified bounded subset. No finiteness
assumption is imposed on the target measure. -/
theorem exists_dominator_of_binary_approximation
    (hrefine : ∀ n i, i < 2 ^ n → e n i = e (n + 1) (2 * i) + e (n + 1) (2 * i + 1))
    (hmass : ∀ n, ∑ i ∈ Finset.range (2 ^ n), ‖e n i‖ ≤ 1)
    (U : Set E)
    (happrox : ∀ f ∈ U, ∃ c : ℕ → ℕ → 𝕜,
      (∀ n i, ‖c n i‖ ≤ 1) ∧ Tendsto
        (fun n => ∑ i ∈ Finset.range (2 ^ n), c n i • e n i) atTop (𝓝 f)) :
    ∃ G : Ω → ℝ, Integrable G μ ∧ (∀ x, 0 ≤ G x) ∧
      (∫ x, G x ∂μ) ≤ ‖B‖ ∧ ∀ f ∈ U, ∀ᵐ x ∂μ, ‖B f x‖ ≤ G x := by
  obtain ⟨G, hG, hGpos, hGint, hGbound⟩ := exists_integrable_envelope μ
    (binaryEnvelope μ e B) (integrable_binaryEnvelope μ e B) (binaryEnvelope_nonneg μ e B)
    (binaryEnvelope_monotone μ e B hrefine) ‖B‖ (norm_nonneg _)
    (integral_binaryEnvelope_le μ e B hmass)
  refine ⟨G, hG, hGpos, hGint, ?_⟩
  intro f hf
  obtain ⟨c, hc, hcf⟩ := happrox f hf
  apply ae_norm_le_of_tendsto_L1 μ
    (fun n => B (∑ i ∈ Finset.range (2 ^ n), c n i • e n i))
    (B f) G (B.continuous.tendsto f |>.comp hcf)
  intro n
  filter_upwards [ae_norm_linearCombination_le_binaryEnvelope μ e B n (c n) (hc n),
    hGbound n] with x hx hy
  exact hx.trans hy

end BinaryApproximation

end PL1.TraceDomination

