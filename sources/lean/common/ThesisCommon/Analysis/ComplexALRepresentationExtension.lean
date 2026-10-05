import ThesisCommon.Analysis.ComplexBanachLatticeCoordinates
import ThesisCommon.Analysis.ComplexL1Coordinates

/-! Extend an actual lattice isometry of the real form to complex L1.
Complex linearity and surjectivity are constructed from the coordinates;
the phase-supremum characterization proves exact modulus and norm transport.
This extension imposes no finiteness condition on the representing measure. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
namespace BanachLatticeModel
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace X] {μ : Measure X}
variable (B : BanachLatticeModel ℂ E) (e : B.realForm ≃ₗᵢ[ℝ] Lp ℝ 1 μ)

def complexL1RepresentationReal : E →L[ℝ] Lp ℂ 1 μ :=
  (complexL1OfReal μ).comp (e.toContinuousLinearEquiv.toContinuousLinearMap.comp B.realPart) +
    Complex.I • (complexL1OfReal μ).comp
      (e.toContinuousLinearEquiv.toContinuousLinearMap.comp B.imagPart)

theorem complexL1RepresentationReal_apply (z : E) :
    B.complexL1RepresentationReal e z = complexL1OfReal μ (e (B.realPart z)) +
      Complex.I • complexL1OfReal μ (e (B.imagPart z)) := rfl

theorem complexL1Re_representationReal (z : E) :
    complexL1Re μ (B.complexL1RepresentationReal e z) = e (B.realPart z) := by
  simp [complexL1RepresentationReal_apply, complexL1Re_smul]

theorem complexL1Im_representationReal (z : E) :
    complexL1Im μ (B.complexL1RepresentationReal e z) = e (B.imagPart z) := by
  simp [complexL1RepresentationReal_apply, complexL1Im_smul]

def complexL1Representation : E →L[ℂ] Lp ℂ 1 μ where
  toFun := B.complexL1RepresentationReal e
  map_add' := map_add (B.complexL1RepresentationReal e)
  map_smul' := by
    intro c z
    apply complexL1_ext
    · simp only [complexL1Re_representationReal, complexL1Im_representationReal,
        complexL1Re_smul, realPart_smul, map_sub, map_smul, RingHom.id_apply]
    · simp only [complexL1Re_representationReal, complexL1Im_representationReal,
        complexL1Im_smul, imagPart_smul, map_add, map_smul, RingHom.id_apply]
  cont := (B.complexL1RepresentationReal e).continuous

theorem complexL1Re_representation (z : E) :
    complexL1Re μ (B.complexL1Representation e z) = e (B.realPart z) :=
  B.complexL1Re_representationReal e z

theorem complexL1Im_representation (z : E) :
    complexL1Im μ (B.complexL1Representation e z) = e (B.imagPart z) :=
  B.complexL1Im_representationReal e z

theorem complexL1Representation_coe (z : B.realForm) :
    B.complexL1Representation e (z : E) = complexL1OfReal μ (e z) := by
  change B.complexL1RepresentationReal e (z : E) = _
  simp [complexL1RepresentationReal_apply, B.realPart_coe, imagPart_coe]

theorem complexL1Representation_surjective : Function.Surjective (B.complexL1Representation e) := by
  intro f
  refine ⟨(e.symm (complexL1Re μ f) : E) + Complex.I • (e.symm (complexL1Im μ f) : E), ?_⟩
  apply complexL1_ext
  · rw [complexL1Re_representation, map_add]
    have hI : B.realPart (Complex.I • (e.symm (complexL1Im μ f) : E)) = 0 :=
      B.realPart_I _
    rw [B.realPart_coe, hI, add_zero, LinearIsometryEquiv.apply_symm_apply]
  · rw [complexL1Im_representation, map_add, imagPart_coe, imagPart_I,
      B.realPart_coe, zero_add, LinearIsometryEquiv.apply_symm_apply]

theorem realForm_representation_le_iff
    (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) (x y : B.realForm) : e x ≤ e y ↔ x ≤ y := by
  rw [← sub_nonneg, ← map_sub, he, sub_nonneg]

theorem complexL1Representation_modulus
    (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) (z : E) :
    complexL1Modulus (B.complexL1Representation e z) = e (B.modulus z) := by
  apply le_antisymm
  · apply (complexL1Modulus_isLUB _).2
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_smul, complexL1Re_representation]
    exact (B.realForm_representation_le_iff e he _ _).mpr
      ((B.modulus_lub z).1 ⟨c, hc, rfl⟩)
  · have h : B.modulus z ≤ e.symm (complexL1Modulus (B.complexL1Representation e z)) := by
      apply (B.modulus_lub z).2
      rintro _ ⟨c, hc, rfl⟩
      apply (B.realForm_representation_le_iff e he _ _).mp
      rw [LinearIsometryEquiv.apply_symm_apply, ← complexL1Re_representation, map_smul]
      exact complexL1Re_phase_le _ c hc.le
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (B.realForm_representation_le_iff e he _ _).mpr h

theorem norm_complexL1Representation
    (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) (z : E) : ‖B.complexL1Representation e z‖ = ‖z‖ := by
  rw [← norm_complexL1Modulus, B.complexL1Representation_modulus e he,
    e.norm_map, B.norm_modulus]

def complexL1RepresentationIsometry (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) : E →ₗᵢ[ℂ] Lp ℂ 1 μ where
  toLinearMap := (B.complexL1Representation e).toLinearMap
  norm_map' := B.norm_complexL1Representation e he

def complexL1RepresentationEquiv (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) : E ≃ₗᵢ[ℂ] Lp ℂ 1 μ :=
  LinearIsometryEquiv.ofSurjective (B.complexL1RepresentationIsometry e he)
    (B.complexL1Representation_surjective e)

theorem complexL1RepresentationEquiv_apply
    (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) (z : E) :
    B.complexL1RepresentationEquiv e he z = complexL1OfReal μ (e (B.realPart z)) +
      Complex.I • complexL1OfReal μ (e (B.imagPart z)) := rfl

theorem complexL1RepresentationEquiv_modulus
    (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) (z : E) :
    complexL1Modulus (B.complexL1RepresentationEquiv e he z) = e (B.modulus z) :=
  B.complexL1Representation_modulus e he z

end BanachLatticeModel
end ThesisCommon
