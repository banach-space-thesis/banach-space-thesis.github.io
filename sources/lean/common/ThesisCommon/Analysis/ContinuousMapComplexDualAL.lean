import ThesisCommon.Analysis.ContinuousMapComplexModulusPhase

/-! The actual complex continuous dual of C(K) is an intrinsic AL-space.
Its closed real form is isometric to the actual real dual; its modulus is
the constructed Riesz–Kantorovich functional, not a representation input. -/
noncomputable section
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem continuousMapDualOfReal_re_of_im_eq_zero (φ : C(K, ℂ) →L[ℂ] ℂ)
    (hφ : continuousMapDualIm φ = 0) :
    continuousMapDualOfReal (continuousMapDualRe φ) = φ := by
  have h := continuousMapDual_decomposition φ
  rw [hφ, map_zero] at h
  have hz : Complex.I • (0 : C(K, ℂ) →L[ℂ] ℂ) = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change Complex.I * (0 : ℂ) = 0
    exact mul_zero _
  rw [hz, add_zero] at h
  exact h

def continuousMapDualRealForm : Submodule ℝ (C(K, ℂ) →L[ℂ] ℂ) :=
  LinearMap.ker (continuousMapDualIm (K := K))

theorem continuousMapDualRealForm_closed :
    IsClosed (continuousMapDualRealForm (K := K) : Set (C(K, ℂ) →L[ℂ] ℂ)) :=
  ContinuousLinearMap.isClosed_ker (continuousMapDualIm (K := K))

local instance continuousMapDualRealForm_normedAddCommGroup :
    NormedAddCommGroup (continuousMapDualRealForm (K := K)) := inferInstance

local instance continuousMapDualRealForm_normedSpace :
    NormedSpace ℝ (continuousMapDualRealForm (K := K)) := inferInstance

def continuousMapDualRealFormEquiv :
    continuousMapDualRealForm (K := K) ≃ₗᵢ[ℝ] (C(K, ℝ) →L[ℝ] ℝ) where
  toFun φ := continuousMapDualRe φ
  invFun ψ := ⟨continuousMapDualOfReal ψ, continuousMapDualIm_ofReal ψ⟩
  left_inv φ := Subtype.ext (continuousMapDualOfReal_re_of_im_eq_zero
    (φ : C(K, ℂ) →L[ℂ] ℂ) φ.property)
  right_inv := continuousMapDualRe_ofReal
  map_add' φ ψ := (continuousMapDualRe (K := K)).map_add
    (φ : C(K, ℂ) →L[ℂ] ℂ) (ψ : C(K, ℂ) →L[ℂ] ℂ)
  map_smul' c φ := (continuousMapDualRe (K := K)).map_smul c (φ : C(K, ℂ) →L[ℂ] ℂ)
  norm_map' φ := by
    change ‖continuousMapDualRe (φ : C(K, ℂ) →L[ℂ] ℂ)‖ = ‖(φ : C(K, ℂ) →L[ℂ] ℂ)‖
    rw [← norm_continuousMapDualOfReal (continuousMapDualRe (φ : C(K, ℂ) →L[ℂ] ℂ)),
      continuousMapDualOfReal_re_of_im_eq_zero (φ : C(K, ℂ) →L[ℂ] ℂ) φ.property]

def continuousMapDualRealFormLattice : Lattice (continuousMapDualRealForm (K := K)) where
  __ := PartialOrder.lift (continuousMapDualRealFormEquiv (K := K)) (continuousMapDualRealFormEquiv (K := K)).injective
  sup φ ψ := (continuousMapDualRealFormEquiv (K := K)).symm
    ((continuousMapDualRealFormEquiv (K := K)) φ ⊔ (continuousMapDualRealFormEquiv (K := K)) ψ)
  inf φ ψ := (continuousMapDualRealFormEquiv (K := K)).symm
    ((continuousMapDualRealFormEquiv (K := K)) φ ⊓ (continuousMapDualRealFormEquiv (K := K)) ψ)
  le_sup_left φ ψ := by change _ ≤ (continuousMapDualRealFormEquiv (K := K)) _; simp
  le_sup_right φ ψ := by change _ ≤ (continuousMapDualRealFormEquiv (K := K)) _; simp
  sup_le φ ψ χ hφχ hψχ := by
    change (continuousMapDualRealFormEquiv (K := K)) _ ≤ _
    simpa only [LinearIsometryEquiv.apply_symm_apply] using sup_le hφχ hψχ
  inf_le_left φ ψ := by change (continuousMapDualRealFormEquiv (K := K)) _ ≤ _; simp
  inf_le_right φ ψ := by change (continuousMapDualRealFormEquiv (K := K)) _ ≤ _; simp
  le_inf φ ψ χ hφψ hφχ := by
    change _ ≤ (continuousMapDualRealFormEquiv (K := K)) _
    simpa only [LinearIsometryEquiv.apply_symm_apply] using le_inf hφψ hφχ

attribute [local instance] continuousMapDualRealFormLattice

def continuousMapDualRealFormOrderedAdd : IsOrderedAddMonoid (continuousMapDualRealForm (K := K)) where
  add_le_add_left φ ψ h χ := by
    change (continuousMapDualRealFormEquiv (K := K)) (χ + φ) ≤ (continuousMapDualRealFormEquiv (K := K)) (χ + ψ)
    rw [map_add, map_add]
    exact add_le_add_left (show (continuousMapDualRealFormEquiv (K := K)) φ ≤ (continuousMapDualRealFormEquiv (K := K)) ψ from h) _

attribute [local instance] continuousMapDualRealFormOrderedAdd

def continuousMapDualRealFormOrderedModule : IsOrderedModule ℝ (continuousMapDualRealForm (K := K)) :=
  IsOrderedModule.of_smul_nonneg fun c hc φ hφ => by
    change 0 ≤ continuousMapDualRe (c • (φ : C(K, ℂ) →L[ℂ] ℂ))
    rw [map_smul]
    exact smul_nonneg hc (show 0 ≤ continuousMapDualRe (φ : C(K, ℂ) →L[ℂ] ℂ) from hφ)

theorem continuousMapDualRealFormEquiv_abs (φ : continuousMapDualRealForm (K := K)) :
    (continuousMapDualRealFormEquiv (K := K)) |φ| = |(continuousMapDualRealFormEquiv (K := K)) φ| := by
  change (continuousMapDualRealFormEquiv (K := K)) ((continuousMapDualRealFormEquiv (K := K)).symm
    ((continuousMapDualRealFormEquiv (K := K)) φ ⊔ (continuousMapDualRealFormEquiv (K := K)) (-φ))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

def continuousMapDualRealFormSolidNorm : HasSolidNorm (continuousMapDualRealForm (K := K)) where
  solid {φ ψ} h := by
    rw [← (continuousMapDualRealFormEquiv (K := K)).norm_map φ, ← (continuousMapDualRealFormEquiv (K := K)).norm_map ψ]
    apply norm_le_norm_of_abs_le_abs (α := C(K, ℝ) →L[ℝ] ℝ)
    change (continuousMapDualRealFormEquiv (K := K)) |φ| ≤ (continuousMapDualRealFormEquiv (K := K)) |ψ| at h
    simpa only [continuousMapDualRealFormEquiv_abs] using h

def continuousMapDualRealPart :
    (C(K, ℂ) →L[ℂ] ℂ) →L[ℝ] continuousMapDualRealForm (K := K) :=
  (continuousMapDualRealFormEquiv (K := K)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp continuousMapDualRe

theorem continuousMapDualRealPart_coe (φ : C(K, ℂ) →L[ℂ] ℂ) :
    (continuousMapDualRealPart φ : C(K, ℂ) →L[ℂ] ℂ) = continuousMapDualOfReal (continuousMapDualRe φ) := rfl

theorem continuousMapDualRealFormEquiv_realPart (φ : C(K, ℂ) →L[ℂ] ℂ) :
    (continuousMapDualRealFormEquiv (K := K)) (continuousMapDualRealPart φ) = continuousMapDualRe φ :=
  (continuousMapDualRealFormEquiv (K := K)).apply_symm_apply _

def continuousMapComplexDualBanachLatticeModel : BanachLatticeModel ℂ (C(K, ℂ) →L[ℂ] ℂ) where
  realForm := continuousMapDualRealForm
  closed_realForm := continuousMapDualRealForm_closed
  realPart := continuousMapDualRealPart
  realPart_coe φ := (continuousMapDualRealFormEquiv (K := K)).symm_apply_apply φ
  realPart_I φ := by
    apply (continuousMapDualRealFormEquiv (K := K)).injective
    rw [continuousMapDualRealFormEquiv_realPart]
    change continuousMapDualRe (Complex.I • (φ : C(K, ℂ) →L[ℂ] ℂ)) = 0
    have hφ : continuousMapDualIm (φ : C(K, ℂ) →L[ℂ] ℂ) = 0 := φ.property
    apply ContinuousLinearMap.ext
    intro f
    have him := congrArg (fun ψ : C(K, ℝ) →L[ℝ] ℝ => ψ f) hφ
    change ((φ : C(K, ℂ) →L[ℂ] ℂ) (continuousMapOfReal f)).im = 0 at him
    change (Complex.I * (φ : C(K, ℂ) →L[ℂ] ℂ) (continuousMapOfReal f)).re = 0
    simp [him]
  decomposition φ := by
    simp only [continuousMapDualRealPart_coe]
    change φ = continuousMapDualOfReal (continuousMapDualRe φ) +
      Complex.I • continuousMapDualOfReal (continuousMapDualRe (-Complex.I • φ))
    have hr : continuousMapDualRe (-Complex.I • φ) = continuousMapDualIm φ := by
      apply ContinuousLinearMap.ext
      intro f
      change ((-Complex.I) * φ (continuousMapOfReal f)).re = (φ (continuousMapOfReal f)).im
      simp
    rw [hr]
    exact (continuousMapDual_decomposition φ).symm
  lattice := continuousMapDualRealFormLattice
  orderedAdd := continuousMapDualRealFormOrderedAdd
  orderedModule := continuousMapDualRealFormOrderedModule
  solidNorm := continuousMapDualRealFormSolidNorm
  modulus φ := (continuousMapDualRealFormEquiv (K := K)).symm (continuousMapComplexModulus φ)
  modulus_lub φ := by
    constructor
    · rintro _ ⟨c, hc, rfl⟩
      change (continuousMapDualRealFormEquiv (K := K)) (continuousMapDualRealPart (c • φ)) ≤
        (continuousMapDualRealFormEquiv (K := K)) ((continuousMapDualRealFormEquiv (K := K)).symm (continuousMapComplexModulus φ))
      rw [continuousMapDualRealFormEquiv_realPart, LinearIsometryEquiv.apply_symm_apply]
      exact continuousMapDualRe_phase_le φ c hc.le
    · intro b hb
      change (continuousMapDualRealFormEquiv (K := K)) ((continuousMapDualRealFormEquiv (K := K)).symm (continuousMapComplexModulus φ)) ≤
        (continuousMapDualRealFormEquiv (K := K)) b
      rw [LinearIsometryEquiv.apply_symm_apply]
      apply (continuousMapComplexModulus_isLUB φ).2
      rintro _ ⟨c, hc, rfl⟩
      have h := hb ⟨c, hc, rfl⟩
      change (continuousMapDualRealFormEquiv (K := K)) (continuousMapDualRealPart (c • φ)) ≤ _ at h
      simpa only [continuousMapDualRealFormEquiv_realPart] using h
  norm_modulus φ := ((continuousMapDualRealFormEquiv (K := K)).symm.norm_map _).trans (norm_continuousMapComplexModulus φ)

theorem continuousMap_complex_dual_isALSpace : IsALSpace ℂ (C(K, ℂ) →L[ℂ] ℂ) := by
  refine ⟨continuousMapComplexDualBanachLatticeModel, ?_⟩
  intro φ ψ hφ hψ
  rw [← (continuousMapDualRealFormEquiv (K := K)).norm_map (φ + ψ),
    ← (continuousMapDualRealFormEquiv (K := K)).norm_map φ, ← (continuousMapDualRealFormEquiv (K := K)).norm_map ψ, map_add]
  apply continuousMapDual_norm_add_of_nonneg
  · exact hφ
  · exact hψ

end ThesisCommon
