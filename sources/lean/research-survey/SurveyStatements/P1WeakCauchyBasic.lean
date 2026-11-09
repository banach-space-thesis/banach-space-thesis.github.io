import SurveyStatements.P1KernelSelection
import SurveyStatements.P1BasicRescaling

/-! The basic-subsequence conclusion for an actual nontrivial weak-Cauchy
sequence. Kernel norming, finite families and the summable evaluation budget
are proved in the imported modules; no basic-selection theorem is assumed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem unitNormalize_functional_tendsto_zero
    (s : ℕ → X) {r : ℝ} (hr : 0 < r) (hlower : ∀ n, r ≤ ‖s n‖)
    (f : StrongDual ℂ X) (hf : Tendsto (fun n => f (s n)) atTop (𝓝 0)) :
    Tendsto (fun n => f (unitNormalize (s n))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hupper (n : ℕ) : ‖f (unitNormalize (s n))‖ ≤ r⁻¹ * ‖f (s n)‖ := by
    simp only [unitNormalize, map_smul, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (inv_le_inv₀ (lt_of_lt_of_le hr (hlower n)) hr).mpr (hlower n)
  have hnorm : Tendsto (fun n => r⁻¹ * ‖f (s n)‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hf.norm.const_mul r⁻¹
  exact squeeze_zero (fun n => norm_nonneg _) hupper hnorm

theorem nontrivial_weakCauchy_eventually_norm_bounded_below
    (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (hnot : ¬ ∃ x : X, ∀ f : StrongDual ℂ X,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n, N ≤ n → r ≤ ‖s n‖ := by
  classical
  let ξ := weakCauchyLimitBidual s hs
  have hξ : ξ ≠ 0 := by
    intro hz
    change weakCauchyLimitBidual s hs = 0 at hz
    apply hnot
    refine ⟨0, ?_⟩
    intro f
    simpa only [hz, ContinuousLinearMap.zero_apply, map_zero] using
      weakCauchyLimitBidual_tendsto s hs f
  have hex : ∃ f : StrongDual ℂ X, ξ f ≠ 0 := by
    by_contra! h
    apply hξ
    ext f
    exact h f
  obtain ⟨f, hf⟩ := hex
  have hfnz : f ≠ 0 := by
    intro h
    apply hf
    rw [h, map_zero]
  have hfp : 0 < ‖f‖ := norm_pos_iff.mpr hfnz
  have hξfp : 0 < ‖ξ f‖ := norm_pos_iff.mpr hf
  have ht := (weakCauchyLimitBidual_tendsto s hs f).norm
  have hhalf : ‖ξ f‖ / 2 < ‖ξ f‖ := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_nhds hhalf))
  refine ⟨‖ξ f‖ / (2 * ‖f‖), by positivity, N, ?_⟩
  intro n hn
  apply (div_le_iff₀ (show 0 < 2 * ‖f‖ by positivity)).mpr
  have h := f.le_opNorm (s n)
  have hsmall := hN n hn
  dsimp [ξ] at hsmall ⊢
  nlinarith

theorem nontrivial_weakCauchy_exists_basic_subsequence [CompleteSpace X]
    (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (hnot : ¬ ∃ x : X, ∀ f : StrongDual ℂ X,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ IsBasicSequence (s ∘ ν) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ N M, N ≤ M → ∀ a : ℕ → ℂ,
        c * ‖sequencePartialSum (s ∘ ν) a N‖ ≤
          ‖sequencePartialSum (s ∘ ν) a M‖ := by
  obtain ⟨q, hqp, hq⟩ := nontrivial_weakCauchy_kernel_norms s hs hnot
  obtain ⟨r, hr, L, hL⟩ := nontrivial_weakCauchy_eventually_norm_bounded_below s hs hnot
  let y : ℕ → X := fun n => s (n + L)
  have hynz (n : ℕ) : y n ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hr (hL (n + L) (by omega)))
  let z : ℕ → X := fun n => unitNormalize (y n)
  have hznorm (n : ℕ) : ‖z n‖ = 1 := norm_unitNormalize (hynz n)
  let ξ := weakCauchyLimitBidual s hs
  have hzker : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (z n)) atTop (𝓝 0) := by
    intro f hf
    apply unitNormalize_functional_tendsto_zero y hr
      (fun n => hL (n + L) (by omega)) f
    exact (weakCauchy_kernel_evaluations_tendsto_zero s hs f hf).comp
      (tendsto_add_atTop_nat L)
  obtain ⟨ν, hν, hb, hbound⟩ :=
    normalized_kernelNull_exists_basic_subsequence z hznorm ξ hzker hqp hq
  let η : ℕ → ℕ := fun n => ν n + L
  have hη : StrictMono η := by
    intro i j hij
    exact Nat.add_lt_add_right (hν hij) L
  let a : ℕ → ℂ := fun n => (‖y (ν n)‖ : ℂ)
  have ha (n : ℕ) : a n ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hynz (ν n)))
  have hscale : (fun n => a n • (z ∘ ν) n) = s ∘ η := by
    funext n
    exact norm_smul_unitNormalize (y (ν n))
  refine ⟨η, hη, ?_, q / 4, by positivity, ?_⟩
  · rw [← hscale]
    exact basicSequence_smul_nonzero hb a ha
  · intro N M hNM b
    rw [← hscale, sequencePartialSum_smul, sequencePartialSum_smul]
    exact hbound N M hNM (fun n => b n * a n)

end SurveyStatements.P1
