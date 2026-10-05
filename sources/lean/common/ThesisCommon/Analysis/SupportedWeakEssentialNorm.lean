import ThesisCommon.WeakCompact
import ThesisCommon.LpCut

/-! Distance to genuine weakly compact operators whose range vanishes
outside a prescribed measurable part of the output. No representation,
attainment, or measure-finiteness assumption is built into the definition. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MeasurableSpace Y] {ν : Measure Y}

def L1OperatorSupportedOn (Θ : Set Y) (W : E →L[𝕜] Lp 𝕜 1 ν) : Prop :=
  ∀ f, W f =ᵐ[ν.restrict Θᶜ] 0

theorem l1OperatorSupportedOn_zero (Θ : Set Y) :
    L1OperatorSupportedOn Θ (0 : E →L[𝕜] Lp 𝕜 1 ν) := by
  intro f
  exact ae_restrict_of_ae (Lp.coeFn_zero 𝕜 1 ν)

theorem L1OperatorSupportedOn.mono {Θ Λ : Set Y} {W : E →L[𝕜] Lp 𝕜 1 ν}
    (hW : L1OperatorSupportedOn Θ W) (hsub : Θ ⊆ Λ) : L1OperatorSupportedOn Λ W :=
  fun f => (hW f).filter_mono (ae_mono (Measure.restrict_mono (compl_subset_compl.mpr hsub) le_rfl))

theorem L1OperatorSupportedOn.neg {Θ : Set Y} {W : E →L[𝕜] Lp 𝕜 1 ν}
    (hW : L1OperatorSupportedOn Θ W) : L1OperatorSupportedOn Θ (-W) := by
  intro f
  filter_upwards [hW f, ae_restrict_of_ae (Lp.coeFn_neg (W f))] with y hy hn
  change (-W f) y = 0
  simp only [hn, Pi.neg_apply, hy, Pi.zero_apply, neg_zero]

theorem l1OperatorSupportedOn_iff_cut_compl_eq_zero
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (W : E →L[𝕜] Lp 𝕜 1 ν) :
    L1OperatorSupportedOn Θ W ↔ (lpCutL Θᶜ hΘ.compl).comp W = 0 := by
  constructor
  · intro hW
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    have h := (ae_restrict_iff' hΘ.compl).mp (hW f)
    filter_upwards [h, lpCut_coe Θᶜ hΘ.compl (W f), Lp.coeFn_zero 𝕜 1 ν] with y hy hc hz
    change lpCut Θᶜ hΘ.compl (W f) y = (0 : Lp 𝕜 1 ν) y
    rw [hc, hz]
    by_cases hyΘ : y ∈ Θᶜ <;> simp [hyΘ, hy]
  · intro h f
    have hae := Lp.ext_iff.mp (DFunLike.congr_fun h f)
    change ∀ᵐ y ∂ν.restrict Θᶜ, W f y = 0
    rw [ae_restrict_iff' hΘ.compl]
    filter_upwards [hae, lpCut_coe Θᶜ hΘ.compl (W f), Lp.coeFn_zero 𝕜 1 ν] with y hy hc hz
    intro hyΘ
    change lpCut Θᶜ hΘ.compl (W f) y = (0 : Lp 𝕜 1 ν) y at hy
    simpa only [hc, hz, indicator_of_mem hyΘ, Pi.zero_apply] using hy

def supportedWeakEssentialNorm (Θ : Set Y) (T : E →L[𝕜] Lp 𝕜 1 ν) : ℝ :=
  sInf {r : ℝ | ∃ W : E →L[𝕜] Lp 𝕜 1 ν,
    IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧ r = ‖T - W‖}

theorem supportedWeakEssentialNorm_nonneg (Θ : Set Y) (T : E →L[𝕜] Lp 𝕜 1 ν) :
    0 ≤ supportedWeakEssentialNorm Θ T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, l1OperatorSupportedOn_zero Θ, rfl⟩
  · rintro r ⟨W, _, _, rfl⟩
    exact norm_nonneg _

theorem supportedWeakEssentialNorm_le (Θ : Set Y) (T : E →L[𝕜] Lp 𝕜 1 ν)
    {W : E →L[𝕜] Lp 𝕜 1 ν} (hW : IsWeaklyCompactOperator W) (hs : L1OperatorSupportedOn Θ W) :
    supportedWeakEssentialNorm Θ T ≤ ‖T - W‖ := by
  apply csInf_le
  · exact ⟨0, by rintro r ⟨V, _, _, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨W, hW, hs, rfl⟩

theorem supportedWeakEssentialNorm_le_norm (Θ : Set Y) (T : E →L[𝕜] Lp 𝕜 1 ν) :
    supportedWeakEssentialNorm Θ T ≤ ‖T‖ := by
  simpa only [sub_zero] using
    supportedWeakEssentialNorm_le Θ T weaklyCompact_zero (l1OperatorSupportedOn_zero Θ)

theorem weakEssentialNorm_le_supported (Θ : Set Y) (T : E →L[𝕜] Lp 𝕜 1 ν) :
    weakEssentialNorm T ≤ supportedWeakEssentialNorm Θ T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, l1OperatorSupportedOn_zero Θ, rfl⟩
  · rintro r ⟨W, hW, _, rfl⟩
    exact weakEssentialNorm_le T hW

theorem supportedWeakEssentialNorm_antitone (T : E →L[𝕜] Lp 𝕜 1 ν)
    {Θ Λ : Set Y} (hsub : Θ ⊆ Λ) :
    supportedWeakEssentialNorm Λ T ≤ supportedWeakEssentialNorm Θ T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, l1OperatorSupportedOn_zero Θ, rfl⟩
  · rintro r ⟨W, hW, hs, rfl⟩
    exact supportedWeakEssentialNorm_le Λ T hW (hs.mono hsub)

theorem supportedWeakEssentialNorm_univ (T : E →L[𝕜] Lp 𝕜 1 ν) :
    supportedWeakEssentialNorm univ T = weakEssentialNorm T := by
  apply le_antisymm _ (weakEssentialNorm_le_supported univ T)
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    apply supportedWeakEssentialNorm_le univ T hW
    intro f
    change ∀ᵐ y ∂ν.restrict univᶜ, W f y = 0
    simp

end ThesisCommon
