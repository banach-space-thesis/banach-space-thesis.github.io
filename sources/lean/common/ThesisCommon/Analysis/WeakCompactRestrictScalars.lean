import ThesisCommon.WeakCompact
import Mathlib.Analysis.Normed.Module.RCLike.Extend

/-! The real and real-or-complex weak topologies agree. Consequently
restriction of scalars preserves and reflects genuine weak compactness. -/
noncomputable section
open Set
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

theorem continuous_weakSpace_to_real :
    @Continuous (WeakSpace 𝕜 E) (WeakSpace ℝ E) _ _ (fun x => x) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ E).flip
  intro φ
  have h := RCLike.continuous_re.comp
    (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (φ.extendTo𝕜' : E →L[𝕜] 𝕜))
  change Continuous (fun x : WeakSpace 𝕜 E => RCLike.re ((φ.extendTo𝕜' : E →L[𝕜] 𝕜) x)) at h
  change Continuous (fun x : WeakSpace 𝕜 E => φ x)
  convert h using 1
  funext x
  exact (LinearMap.extendTo𝕜'_apply_re (𝕜 := 𝕜) φ.toLinearMap x).symm

theorem continuous_weakSpace_from_real :
    @Continuous (WeakSpace ℝ E) (WeakSpace 𝕜 E) _ _ (fun x => x) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing 𝕜 E).flip
  intro φ
  have hr := WeakBilin.eval_continuous (topDualPairing ℝ E).flip
    (RCLike.reCLM.comp (φ.restrictScalars ℝ))
  have hi := WeakBilin.eval_continuous (topDualPairing ℝ E).flip
    (RCLike.imCLM.comp (φ.restrictScalars ℝ))
  have h := (RCLike.continuous_ofReal.comp hr).add
    ((RCLike.continuous_ofReal.comp hi).mul (continuous_const : Continuous (fun _ : WeakSpace ℝ E => (RCLike.I : 𝕜))))
  change Continuous (fun x : WeakSpace ℝ E => (RCLike.re (φ x) : 𝕜) + (RCLike.im (φ x) : 𝕜) * RCLike.I) at h
  simpa only [RCLike.re_add_im] using h

def weakSpaceRealHomeomorph : WeakSpace 𝕜 E ≃ₜ WeakSpace ℝ E where
  toEquiv := Equiv.refl E
  continuous_toFun := continuous_weakSpace_to_real (𝕜 := 𝕜) (E := E)
  continuous_invFun := continuous_weakSpace_from_real (𝕜 := 𝕜) (E := E)

theorem IsWeaklyCompactOperator.restrictScalars_real {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) : IsWeaklyCompactOperator (T.restrictScalars ℝ) := by
  obtain ⟨K, hK, hTK⟩ := hT
  refine ⟨(weakSpaceRealHomeomorph (𝕜 := 𝕜) (E := F)) '' K, hK.image (weakSpaceRealHomeomorph (𝕜 := 𝕜) (E := F)).continuous, ?_⟩
  intro x hx
  exact ⟨toWeakSpace 𝕜 F (T x), hTK x hx, rfl⟩

theorem IsWeaklyCompactOperator.of_restrictScalars_real {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator (T.restrictScalars ℝ)) : IsWeaklyCompactOperator T := by
  obtain ⟨K, hK, hTK⟩ := hT
  refine ⟨(weakSpaceRealHomeomorph (𝕜 := 𝕜) (E := F)).symm '' K, hK.image (weakSpaceRealHomeomorph (𝕜 := 𝕜) (E := F)).symm.continuous, ?_⟩
  intro x hx
  exact ⟨toWeakSpace ℝ F (T x), hTK x hx, rfl⟩

theorem weaklyCompact_restrictScalars_real_iff (T : E →L[𝕜] F) :
    IsWeaklyCompactOperator (T.restrictScalars ℝ) ↔ IsWeaklyCompactOperator T :=
  ⟨IsWeaklyCompactOperator.of_restrictScalars_real, IsWeaklyCompactOperator.restrictScalars_real⟩

end ThesisCommon
