import ThesisCommon.Analysis.ComplexBanachLatticeCoordinates
import ThesisCommon.Analysis.WeakCompactRestrictScalars

/-! Complexification of genuine bounded maps between the real forms of
abstract complex Banach lattices. Composition and weak compactness are
preserved without a representation or a positivity hypothesis. -/
noncomputable section
namespace ThesisCommon
namespace BanachLatticeModel
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
variable (B : BanachLatticeModel ℂ E) (C : BanachLatticeModel ℂ F)

def operatorExtensionReal (T : B.realForm →L[ℝ] C.realForm) : E →L[ℝ] F :=
  C.realForm.subtypeL.comp (T.comp B.realPart) +
    Complex.I • C.realForm.subtypeL.comp (T.comp B.imagPart)

theorem operatorExtensionReal_apply (T : B.realForm →L[ℝ] C.realForm) (z : E) :
    B.operatorExtensionReal C T z = (T (B.realPart z) : F) +
      Complex.I • (T (B.imagPart z) : F) := rfl

theorem realPart_operatorExtensionReal (T : B.realForm →L[ℝ] C.realForm) (z : E) :
    C.realPart (B.operatorExtensionReal C T z) = T (B.realPart z) := by
  simp only [operatorExtensionReal_apply, map_add, C.realPart_coe,
    realPart_I_eq_neg_imagPart, imagPart_coe, neg_zero, add_zero]

theorem imagPart_operatorExtensionReal (T : B.realForm →L[ℝ] C.realForm) (z : E) :
    C.imagPart (B.operatorExtensionReal C T z) = T (B.imagPart z) := by
  simp only [operatorExtensionReal_apply, map_add, imagPart_coe, imagPart_I,
    C.realPart_coe, zero_add]

def operatorExtension (T : B.realForm →L[ℝ] C.realForm) : E →L[ℂ] F where
  toFun := B.operatorExtensionReal C T
  map_add' := map_add (B.operatorExtensionReal C T)
  map_smul' := by
    intro c z
    apply C.ext_real_imag
    · simp only [realPart_operatorExtensionReal, realPart_smul,
        imagPart_operatorExtensionReal, map_sub, map_smul, RingHom.id_apply]
    · simp only [imagPart_operatorExtensionReal, imagPart_smul,
        realPart_operatorExtensionReal, map_add, map_smul, RingHom.id_apply]
  cont := (B.operatorExtensionReal C T).continuous

theorem operatorExtension_apply (T : B.realForm →L[ℝ] C.realForm) (z : E) :
    B.operatorExtension C T z = (T (B.realPart z) : F) +
      Complex.I • (T (B.imagPart z) : F) := rfl

@[simp] theorem realPart_operatorExtension (T : B.realForm →L[ℝ] C.realForm) (z : E) :
    C.realPart (B.operatorExtension C T z) = T (B.realPart z) :=
  B.realPart_operatorExtensionReal C T z

@[simp] theorem imagPart_operatorExtension (T : B.realForm →L[ℝ] C.realForm) (z : E) :
    C.imagPart (B.operatorExtension C T z) = T (B.imagPart z) :=
  B.imagPart_operatorExtensionReal C T z

@[simp] theorem operatorExtension_coe (T : B.realForm →L[ℝ] C.realForm) (x : B.realForm) :
    B.operatorExtension C T (x : E) = (T x : F) := by
  simp [operatorExtension_apply, B.realPart_coe, imagPart_coe]

@[simp] theorem operatorExtension_zero : B.operatorExtension C 0 = 0 := by
  ext z
  apply C.ext_real_imag <;> simp

@[simp] theorem operatorExtension_add (T U : B.realForm →L[ℝ] C.realForm) :
    B.operatorExtension C (T + U) = B.operatorExtension C T + B.operatorExtension C U := by
  ext z
  apply C.ext_real_imag <;> simp

@[simp] theorem operatorExtension_sub (T U : B.realForm →L[ℝ] C.realForm) :
    B.operatorExtension C (T - U) = B.operatorExtension C T - B.operatorExtension C U := by
  ext z
  apply C.ext_real_imag <;> simp

@[simp] theorem operatorExtension_id :
    B.operatorExtension B (ContinuousLinearMap.id ℝ B.realForm) = ContinuousLinearMap.id ℂ E := by
  ext z
  apply B.ext_real_imag <;> simp

@[simp] theorem operatorExtension_comp (D : BanachLatticeModel ℂ G)
    (S : C.realForm →L[ℝ] D.realForm) (T : B.realForm →L[ℝ] C.realForm) :
    B.operatorExtension D (S.comp T) = (C.operatorExtension D S).comp (B.operatorExtension C T) := by
  ext z
  apply D.ext_real_imag <;> simp

theorem weaklyCompact_operatorExtension_iff (T : B.realForm →L[ℝ] C.realForm) :
    IsWeaklyCompactOperator (B.operatorExtension C T) ↔ IsWeaklyCompactOperator T := by
  constructor
  · intro h
    have hh := (h.restrictScalars_real.comp_right B.realForm.subtypeL).comp_left C.realPart
    have heq : C.realPart.comp ((B.operatorExtension C T).restrictScalars ℝ |>.comp
        B.realForm.subtypeL) = T := by
      ext x
      simp [C.realPart_coe]
    rwa [heq] at hh
  · intro h
    apply IsWeaklyCompactOperator.of_restrictScalars_real
    change IsWeaklyCompactOperator (B.operatorExtensionReal C T)
    have hr := (h.comp_right B.realPart).comp_left C.realForm.subtypeL
    have hi := (h.comp_right B.imagPart).comp_left C.realForm.subtypeL
    have his : IsWeaklyCompactOperator
        (Complex.I • C.realForm.subtypeL.comp (T.comp B.imagPart)) := by
      simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using
        hi.comp_left (Complex.I • ContinuousLinearMap.id ℝ F)
    exact hr.add his

theorem exists_orthogonal_selfCopies_of_realForm
    (J P : ℕ → B.realForm →L[ℝ] B.realForm)
    (hd : ∀ n, (P n).comp (J n) = ContinuousLinearMap.id ℝ B.realForm)
    (ho : ∀ n k, n ≠ k → (P n).comp (J k) = 0) :
    ∃ U V : ℕ → E →L[ℂ] E,
      (∀ n, (V n).comp (U n) = ContinuousLinearMap.id ℂ E) ∧
      (∀ n k, n ≠ k → (V n).comp (U k) = 0) := by
  refine ⟨fun n => B.operatorExtension B (J n), fun n => B.operatorExtension B (P n), ?_, ?_⟩
  · intro n
    rw [← operatorExtension_comp, hd, operatorExtension_id]
  · intro n k hnk
    rw [← operatorExtension_comp, ho n k hnk, operatorExtension_zero]

theorem exists_cornerCopies_of_realForm
    (Q : B.realForm →L[ℝ] B.realForm) (J P : ℕ → B.realForm →L[ℝ] B.realForm)
    (hd : ∀ n, (P n).comp (J n) = Q)
    (ho : ∀ n k, n ≠ k → (P n).comp (J k) = 0)
    (hr : IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ B.realForm - Q)) :
    ∃ R : E →L[ℂ] E, ∃ U V : ℕ → E →L[ℂ] E,
      (∀ n, (V n).comp (U n) = R) ∧
      (∀ n k, n ≠ k → (V n).comp (U k) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id ℂ E - R) := by
  refine ⟨B.operatorExtension B Q, fun n => B.operatorExtension B (J n),
    fun n => B.operatorExtension B (P n), ?_, ?_, ?_⟩
  · intro n
    rw [← operatorExtension_comp, hd]
  · intro n k hnk
    rw [← operatorExtension_comp, ho n k hnk, operatorExtension_zero]
  · have hh := (B.weaklyCompact_operatorExtension_iff B _).mpr hr
    simpa only [operatorExtension_sub, operatorExtension_id] using hh

end BanachLatticeModel
end ThesisCommon
