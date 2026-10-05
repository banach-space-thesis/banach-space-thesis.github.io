import Sigma.ComplexJLDual
import ThesisCommon.Analysis.SigmaComplexClosedSpanDual

/-! Complex compactum evaluations and uniqueness from the closed-span generators. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

theorem complexJLFunctional_ext {B : Set (Set Point)} (φ ψ : ComplexJL B →L[ℂ] ℂ)
    (hp : ∀ p, φ ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩ =
      ψ ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩)
    (hb : ∀ b : B, φ ⟨complexCharacteristic b.val,complexCharacteristic_mem_ComplexJL b.property⟩ =
      ψ ⟨complexCharacteristic b.val,complexCharacteristic_mem_ComplexJL b.property⟩)
    (h1 : φ ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL B⟩ =
      ψ ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL B⟩) : φ = ψ := by
  apply ThesisCommon.complexClosedSpan_dual_ext _ φ ψ
  rintro x ((⟨p,rfl⟩ | ⟨b,hb',rfl⟩) | rfl)
  · exact hp p
  · exact hb ⟨b,hb'⟩
  · exact h1

def complexJLEvaluation {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : AUCompactum B) : ComplexJL B →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ p).comp
    (complexJLContinuousEquiv hB hInf).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem complexJLEvaluation_apply {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : AUCompactum B) (f : ComplexJL B) :
    complexJLEvaluation hB hInf p f = complexJLContinuousEquiv hB hInf f p := rfl

theorem complexJLEvaluation_base {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : Point) (f : ComplexJL B) :
    complexJLEvaluation hB hInf (↑(Sum.inl p : MrowkaBase B)) f = f.val p :=
  congrArg (fun g : ComplexJL B => g.val p) ((complexJLContinuousEquiv hB hInf).symm_apply_apply f)

theorem complexJLContinuous_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : Point) :
    complexJLContinuousEquiv hB hInf
      ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩ =
      complexLiftRealContinuous (singletonFunction hB p) := by
  have h := complexJLContinuousEquiv_restrict hB hInf
    (complexLiftRealContinuous (singletonFunction hB p)) (complexRestrictToBase_mem hB _)
  simpa only [complexRestrict_lift_real,restrict_singletonFunction,complexAmbientOfReal_characteristic] using h

theorem complexJLContinuous_family {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (b : B) :
    complexJLContinuousEquiv hB hInf ⟨complexCharacteristic b.val,complexCharacteristic_mem_ComplexJL b.property⟩ =
      complexLiftRealContinuous (tailFunction hB b) := by
  have h := complexJLContinuousEquiv_restrict hB hInf
    (complexLiftRealContinuous (tailFunction hB b)) (complexRestrictToBase_mem hB _)
  simpa only [complexRestrict_lift_real,restrict_tailFunction,complexAmbientOfReal_characteristic] using h

@[simp] theorem complexCharacteristic_univ : complexCharacteristic Set.univ = 1 := by
  ext p
  simp

theorem complexJLContinuous_one {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    complexJLContinuousEquiv hB hInf ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL B⟩ = 1 := by
  simpa only [map_one,complexCharacteristic_univ] using complexJLContinuousEquiv_restrict hB hInf
    1 (complexRestrictToBase_mem hB _)

@[simp] theorem complexLiftRealContinuous_apply {K : Type*} [TopologicalSpace K]
    (f : C(K,ℝ)) (p : K) : complexLiftRealContinuous f p = (f p : ℂ) := rfl

end SigmaNonprimarity

