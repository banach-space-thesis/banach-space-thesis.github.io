import ThesisCommon.Analysis.ComplexLpCoordinates
import ThesisCommon.Analysis.ContinuousMapDualCoordinates

/-! An onto order-preserving real isometry from continuous functions to
actual real Lp extends to an onto complex linear isometry. The proof uses
the phase supremum of the pointwise modulus; no representation or norm
identity is assumed for the complex map. This includes p = infinity. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {K X : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def cmImCLM : C(K, ℂ) →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := continuousMapImagPart
      map_add' := fun f g => by ext t; exact Complex.add_im _ _
      map_smul' := fun c f => by ext t; simp [continuousMapImagPart] }
    1 (fun f => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro t
      exact (Complex.abs_im_le_norm _).trans (f.norm_coe_le_norm t))

private theorem cmRe_smul (c : ℂ) (f : C(K, ℂ)) :
    continuousMapReCLM (c • f) = c.re • continuousMapReCLM f - c.im • cmImCLM f := by
  ext t
  exact Complex.mul_re c (f t)

private theorem cmIm_smul (c : ℂ) (f : C(K, ℂ)) :
    cmImCLM (c • f) = c.re • cmImCLM f + c.im • continuousMapReCLM f := by
  ext t
  exact Complex.mul_im c (f t)

private theorem cmIm_ofReal (f : C(K, ℝ)) :
    cmImCLM (continuousMapOfReal (𝕜 := ℂ) f) = 0 := by ext t; rfl

private def cmModulus (f : C(K, ℂ)) : C(K, ℝ) := ⟨fun t => ‖f t‖, f.continuous.norm⟩

private theorem cmModulus_isLUB (f : C(K, ℂ)) :
    IsLUB {g | ∃ c : ℂ, ‖c‖ = 1 ∧ g = continuousMapReCLM (c • f)} (cmModulus f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩ t
    change (c * f t).re ≤ ‖f t‖
    exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans (by rw [norm_mul, hc, one_mul])
  · intro g hg t
    obtain ⟨c, hc, he⟩ := Complex.exists_norm_eq_mul_self (f t)
    have h := hg ⟨c, hc, rfl⟩ t
    change (c * f t).re ≤ g t at h
    rw [← he] at h
    exact h

private theorem norm_cmModulus (f : C(K, ℂ)) : ‖cmModulus f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro t
    simpa only [cmModulus, ContinuousMap.coe_mk, norm_norm] using f.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg (cmModulus f))).mpr
    intro t
    simpa only [cmModulus, ContinuousMap.coe_mk, norm_norm] using (cmModulus f).norm_coe_le_norm t

variable (e : C(K, ℝ) ≃ₗᵢ[ℝ] Lp ℝ p μ)

private def cmLpComplexificationReal : C(K, ℂ) →L[ℝ] Lp ℂ p μ :=
  (complexLpOfReal μ).comp (e.toContinuousLinearEquiv.toContinuousLinearMap.comp continuousMapReCLM) +
    Complex.I • (complexLpOfReal μ).comp (e.toContinuousLinearEquiv.toContinuousLinearMap.comp cmImCLM)

private theorem cmLpReal_apply (f : C(K, ℂ)) :
    cmLpComplexificationReal e f = complexLpOfReal μ (e (continuousMapReCLM f)) +
      Complex.I • complexLpOfReal μ (e (cmImCLM f)) := rfl

private theorem cmLpReal_re (f : C(K, ℂ)) :
    complexLpRe μ (cmLpComplexificationReal e f) = e (continuousMapReCLM f) := by
  simp [cmLpReal_apply, complexLpRe_smul]

private theorem cmLpReal_im (f : C(K, ℂ)) :
    complexLpIm μ (cmLpComplexificationReal e f) = e (cmImCLM f) := by
  simp [cmLpReal_apply, complexLpIm_smul]

def continuousMapLpComplexification : C(K, ℂ) →L[ℂ] Lp ℂ p μ where
  toFun := cmLpComplexificationReal e
  map_add' := map_add (cmLpComplexificationReal e)
  map_smul' := by
    intro c f
    apply complexLp_ext
    · simp only [cmLpReal_re, cmLpReal_im, complexLpRe_smul, cmRe_smul,
        map_sub, map_smul, RingHom.id_apply]
    · simp only [cmLpReal_re, cmLpReal_im, complexLpIm_smul, cmIm_smul,
        map_add, map_smul, RingHom.id_apply]
  cont := (cmLpComplexificationReal e).continuous

private theorem cmLp_re (f : C(K, ℂ)) :
    complexLpRe μ (continuousMapLpComplexification e f) = e (continuousMapReCLM f) :=
  cmLpReal_re e f

private theorem cmLp_im (f : C(K, ℂ)) :
    complexLpIm μ (continuousMapLpComplexification e f) = e (cmImCLM f) :=
  cmLpReal_im e f

theorem continuousMapLpComplexification_surjective :
    Function.Surjective (continuousMapLpComplexification e) := by
  intro f
  refine ⟨continuousMapOfReal (e.symm (complexLpRe μ f)) +
    Complex.I • continuousMapOfReal (e.symm (complexLpIm μ f)), ?_⟩
  apply complexLp_ext
  · rw [cmLp_re, map_add, cmRe_smul]
    simp [continuousMapReCLM_ofReal, cmIm_ofReal]
  · rw [cmLp_im, map_add, cmIm_smul]
    simp [continuousMapReCLM_ofReal, cmIm_ofReal]

private theorem cmLp_order_iff (he : ∀ f, 0 ≤ e f ↔ 0 ≤ f) (f g : C(K, ℝ)) :
    e f ≤ e g ↔ f ≤ g := by
  rw [← sub_nonneg, ← map_sub, he, sub_nonneg]

private theorem cmLp_modulus (he : ∀ f, 0 ≤ e f ↔ 0 ≤ f) (f : C(K, ℂ)) :
    complexLpModulus (continuousMapLpComplexification e f) = e (cmModulus f) := by
  apply le_antisymm
  · apply (complexLpModulus_isLUB _).2
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_smul, cmLp_re]
    exact (cmLp_order_iff e he _ _).mpr ((cmModulus_isLUB f).1 ⟨c, hc, rfl⟩)
  · have h : cmModulus f ≤ e.symm (complexLpModulus (continuousMapLpComplexification e f)) := by
      apply (cmModulus_isLUB f).2
      rintro _ ⟨c, hc, rfl⟩
      apply (cmLp_order_iff e he _ _).mp
      rw [LinearIsometryEquiv.apply_symm_apply, ← cmLp_re, map_smul]
      exact complexLpRe_phase_le _ c hc.le
    simpa only [LinearIsometryEquiv.apply_symm_apply] using (cmLp_order_iff e he _ _).mpr h

theorem norm_continuousMapLpComplexification
    (he : ∀ f, 0 ≤ e f ↔ 0 ≤ f) (f : C(K, ℂ)) :
    ‖continuousMapLpComplexification e f‖ = ‖f‖ := by
  rw [← norm_complexLpModulus, cmLp_modulus e he, e.norm_map, norm_cmModulus]

def continuousMapLpComplexificationEquiv (he : ∀ f, 0 ≤ e f ↔ 0 ≤ f) :
    C(K, ℂ) ≃ₗᵢ[ℂ] Lp ℂ p μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (continuousMapLpComplexification e).toLinearMap
      norm_map' := norm_continuousMapLpComplexification e he }
    (continuousMapLpComplexification_surjective e)

end ThesisCommon
