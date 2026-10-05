import ThesisCommon.Analysis.IntervalKernelLocalizationData
import ThesisCommon.Analysis.ContinuousMapMultiplierFactorization

/-! The local compression and Neumann estimate, with its precise factor bound four.
The extension operator is an explicit input of this reusable analytic step. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K]

def intervalLocalizedExtension (φ : C(UnitInterval, ℝ)) (hφ : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (E : C(K, 𝕜) →L[𝕜] IntervalContinuous 𝕜) : C(K, 𝕜) →L[𝕜] IntervalContinuous 𝕜 :=
  (continuousMapCutoff φ hφ).comp E

theorem norm_intervalLocalizedExtension_le (φ : C(UnitInterval, ℝ))
    (hφ : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (E : C(K, 𝕜) →L[𝕜] IntervalContinuous 𝕜) (hE : ‖E‖ ≤ 1) :
    ‖intervalLocalizedExtension φ hφ E‖ ≤ 1 :=
  ((continuousMapCutoff (𝕜 := 𝕜) φ hφ).opNorm_comp_le E).trans
    (mul_le_one₀ (norm_continuousMapCutoff_le (𝕜 := 𝕜) φ hφ) (norm_nonneg E) hE)

theorem intervalKernel_compression_error
    (Q : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ)
    (e : C(K, UnitInterval)) (a : C(K, 𝕜)) (ha : ∀ x, a x = intervalOperatorAtom Q (e x))
    (φ : C(UnitInterval, ℝ)) (hφ : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (hφone : ∀ x, φ (e x) = 1)
    (hφzero : ∀ x t, t ∉ Metric.ball (e x) (1 / (n + 1 : ℝ)) → φ t = 0)
    (hres : ∀ x, intervalKernelResidualMass Q n (e x) < 1 / 4)
    (E : C(K, 𝕜) →L[𝕜] IntervalContinuous 𝕜) (hnE : ‖E‖ ≤ 1)
    (hE : ∀ g x, E g (e x) = g x) :
    ‖((continuousMapPullback e).comp Q).comp (intervalLocalizedExtension φ hφ E) -
      ContinuousLinearMap.mul 𝕜 C(K, 𝕜) a‖ ≤ 1 / 4 := by
  let J := intervalLocalizedExtension φ hφ E
  have hnJ : ‖J‖ ≤ 1 := norm_intervalLocalizedExtension_le φ hφ E hnE
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro g
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖Q (J g) (e x) - a x * g x‖ ≤ (1 / 4) * ‖g‖
  have hJ : J g (e x) = g x := by
    change (φ (e x) : 𝕜) * E g (e x) = g x
    rw [hφone, RCLike.ofReal_one, one_mul, hE]
  have hsupport : ∀ t ∉ Metric.ball (e x) (1 / (n + 1 : ℝ)), J g t = 0 := by
    intro t ht
    change (φ t : 𝕜) * E g t = 0
    rw [hφzero x t ht, RCLike.ofReal_zero, zero_mul]
  have herr := intervalKernelResidual_local_bound Q (e x) n (J g) hsupport
  rw [hJ, ← ha x] at herr
  have hg : ‖J g‖ ≤ ‖g‖ := (J.le_opNorm g).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnJ (norm_nonneg g))
  exact herr.trans ((mul_le_mul hg (hres x).le
    (intervalKernelResidualMass_nonneg Q n (e x)) (norm_nonneg g)).trans_eq (mul_comm _ _))

theorem intervalKernel_factors_four_of_extension [CompleteSpace C(K, 𝕜)]
    (Q : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ)
    (e : C(K, UnitInterval)) (a : C(K, 𝕜)) (ha : ∀ x, a x = intervalOperatorAtom Q (e x))
    (hlarge : ∀ x, 1 / 2 ≤ ‖a x‖)
    (φ : C(UnitInterval, ℝ)) (hφ : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (hφone : ∀ x, φ (e x) = 1)
    (hφzero : ∀ x t, t ∉ Metric.ball (e x) (1 / (n + 1 : ℝ)) → φ t = 0)
    (hres : ∀ x, intervalKernelResidualMass Q n (e x) < 1 / 4)
    (E : C(K, 𝕜) →L[𝕜] IntervalContinuous 𝕜) (hnE : ‖E‖ ≤ 1)
    (hE : ∀ g x, E g (e x) = g x) : FactorsIdentityWith Q C(K, 𝕜) 4 := by
  let R := continuousMapPullback (𝕜 := 𝕜) e
  let J := intervalLocalizedExtension φ hφ E
  let F := (R.comp Q).comp J
  let D := ContinuousLinearMap.mul 𝕜 C(K, 𝕜) a
  have herr : ‖F - D‖ ≤ 1 / 4 :=
    intervalKernel_compression_error Q n e a ha φ hφ hφone hφzero hres E hnE hE
  have hsmall : 2 * ‖F - D‖ ≤ 1 / 2 := by linarith
  have hfac := (continuousMap_multiplier_factors_two a hlarge).perturb_fraction
    (S := F) (r := 1 / 2) (by norm_num) hsmall
  have hfour : FactorsIdentityWith F C(K, 𝕜) 4 := by norm_num at hfac ⊢; exact hfac
  have hnR : ‖R‖ ≤ 1 := norm_continuousMapPullback_le e
  have hnJ : ‖J‖ ≤ 1 := norm_intervalLocalizedExtension_le φ hφ E hnE
  have hnRJ : ‖R‖ * ‖J‖ ≤ 1 := mul_le_one₀ hnR (norm_nonneg J) hnJ
  exact (hfour.of_compression R J).mono (by nlinarith)

end ThesisCommon
