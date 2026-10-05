import ThesisCommon.Analysis.LpHaarNestedMeans
import ThesisCommon.Analysis.LebesgueLpSupportedNorm

/-! Localised high-pass operators on actual interval Lp. Multiplication
by a measurable indicator is contractive, so each Haar subtree operator
has norm at most two without any unconditionality assumption. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

def lebesgueLpLocalize (s : Set α) (hs : MeasurableSet s) : Lp E p μ →L[𝕜] Lp E p μ :=
  (lebesgueLpExtend (𝕜 := 𝕜) s hs).toContinuousLinearMap.comp
    (lebesgueLpRestrict (𝕜 := 𝕜) s)

theorem lebesgueLpLocalize_norm_le (s : Set α) (hs : MeasurableSet s) (f : Lp E p μ) :
    ‖lebesgueLpLocalize (𝕜 := 𝕜) s hs f‖ ≤ ‖f‖ := by
  change ‖lebesgueLpExtend (𝕜 := 𝕜) s hs (lebesgueLpRestrict (𝕜 := 𝕜) s f)‖ ≤ _
  rw [(lebesgueLpExtend (𝕜 := 𝕜) s hs).norm_map]
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f p μ s)

theorem norm_lebesgueLpLocalize_le (s : Set α) (hs : MeasurableSet s) :
    ‖lebesgueLpLocalize (𝕜 := 𝕜) (E := E) (p := p) (μ := μ) s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using lebesgueLpLocalize_norm_le s hs f

theorem lebesgueLpLocalize_of_supported (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p μ) (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    lebesgueLpLocalize (𝕜 := 𝕜) s hs f = f :=
  lebesgueLpExtend_restrict_of_supported s hs f hf

theorem lebesgueLpLocalize_coe (s : Set α) (hs : MeasurableSet s) (f : Lp E p μ) :
    lebesgueLpLocalize (𝕜 := 𝕜) s hs f =ᵐ[μ] s.indicator f := by
  have hr := (ae_restrict_iff' hs).mp (lebesgueLpRestrict_coe (𝕜 := 𝕜) s f)
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) s hs (lebesgueLpRestrict (𝕜 := 𝕜) s f),
    hr] with x he hr
  change lebesgueLpExtend (𝕜 := 𝕜) s hs (lebesgueLpRestrict (𝕜 := 𝕜) s f) x = _
  rw [he]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, hr hx]
  · simp only [indicator_of_notMem hx]

theorem lebesgueLpLocalize_zero_on (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p μ) (hf : ∀ᵐ x ∂μ, x ∈ s → f x = 0) :
    lebesgueLpLocalize (𝕜 := 𝕜) s hs f = 0 := by
  apply Lp.ext
  filter_upwards [lebesgueLpLocalize_coe (𝕜 := 𝕜) s hs f,
    Lp.coeFn_zero E p μ, hf] with x he hz hf
  rw [he, hz]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, hf hx, Pi.zero_apply]
  · simp only [indicator_of_notMem hx, Pi.zero_apply]

variable (𝕜 : Type*) [RCLike 𝕜] (q : BanachExponent) (hq : q.val ≠ ∞)

def lpHaarSubtreeProjection (n k : ℕ) : IntervalLp 𝕜 q →L[𝕜] IntervalLp 𝕜 q :=
  (lebesgueLpLocalize (𝕜 := 𝕜) (lpHaarCell n k) measurableSet_Ioc).comp
    (ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 q) - lpHaarDyadicMean 𝕜 q hq n)

theorem lpHaarSubtreeProjection_apply (n k : ℕ) (f : IntervalLp 𝕜 q) :
    lpHaarSubtreeProjection 𝕜 q hq n k f =
      lebesgueLpLocalize (𝕜 := 𝕜) (lpHaarCell n k) measurableSet_Ioc
        (f - lpHaarDyadicMean 𝕜 q hq n f) := rfl

theorem norm_lpHaarSubtreeProjection_le (n k : ℕ) :
    ‖lpHaarSubtreeProjection 𝕜 q hq n k‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [lpHaarSubtreeProjection_apply]
  have hav : ‖lpHaarDyadicMean 𝕜 q hq n f‖ ≤ ‖f‖ := by
    have h := mul_le_mul_of_nonneg_right (lpHaarDyadicMean_norm_le 𝕜 q hq n) (norm_nonneg f)
    rw [one_mul] at h
    exact ((lpHaarDyadicMean 𝕜 q hq n).le_opNorm f).trans h
  exact (lebesgueLpLocalize_norm_le (𝕜 := 𝕜) _ _ _).trans
    ((norm_sub_le _ _).trans (by linarith))

theorem lpHaarSubtreeProjection_kill_earlier (n k m j : ℕ) (hj : j < 2 ^ m) (hmn : m < n) :
    lpHaarSubtreeProjection 𝕜 q hq n k (lpHaarDyadic 𝕜 q m j) = 0 := by
  rw [lpHaarSubtreeProjection_apply,
    lpHaarDyadicMean_fix_earlier_haar 𝕜 q hq m n j hj hmn, sub_self, map_zero]

theorem lpHaarSubtreeProjection_fix_contained (n k m j : ℕ) (hj : j < 2 ^ m)
    (hnm : n ≤ m) (hsub : lpHaarCell m j ⊆ lpHaarCell n k) :
    lpHaarSubtreeProjection 𝕜 q hq n k (lpHaarDyadic 𝕜 q m j) = lpHaarDyadic 𝕜 q m j := by
  rw [lpHaarSubtreeProjection_apply,
    lpHaarDyadicMean_kill_later_haar 𝕜 q hq m n j hj hnm, sub_zero]
  apply lebesgueLpLocalize_of_supported
  filter_upwards [lpHaarDyadic_zero_off 𝕜 q m j] with x hx
  intro hxn
  exact hx (fun hxm => hxn (hsub hxm))

theorem lpHaarSubtreeProjection_kill_disjoint (n k m j : ℕ) (hj : j < 2 ^ m)
    (hnm : n ≤ m) (hd : Disjoint (lpHaarCell n k) (lpHaarCell m j)) :
    lpHaarSubtreeProjection 𝕜 q hq n k (lpHaarDyadic 𝕜 q m j) = 0 := by
  rw [lpHaarSubtreeProjection_apply,
    lpHaarDyadicMean_kill_later_haar 𝕜 q hq m n j hj hnm, sub_zero]
  apply lebesgueLpLocalize_zero_on
  filter_upwards [lpHaarDyadic_zero_off 𝕜 q m j] with x hx
  intro hxn
  exact hx (fun hxm => Set.disjoint_left.mp hd hxn hxm)

end ThesisCommon
