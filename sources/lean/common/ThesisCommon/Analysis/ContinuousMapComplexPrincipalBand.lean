import ThesisCommon.Analysis.ContinuousMapComplexDensityCoordinates
import ThesisCommon.Analysis.ContinuousMapComplexModulusPhase
import ThesisCommon.Analysis.SigmaComplexLatticeModulus

/-! The actual complexification of a real principal band in C(K)*.
Membership is also characterised by the constructed dual modulus. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

def continuousMapComplexPrincipalBand (e : C(K, ℝ) →L[ℝ] ℝ) :
    Submodule ℂ (C(K, ℂ) →L[ℂ] ℂ) where
  carrier := {φ | continuousMapDualRe φ ∈ principalBand e ∧
    continuousMapDualIm φ ∈ principalBand e}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ
    simpa only [map_add] using
      And.intro ((principalBand e).add_mem hφ.1 hψ.1)
        ((principalBand e).add_mem hφ.2 hψ.2)
  smul_mem' := by
    intro c φ hφ
    change continuousMapDualRe (c • φ) ∈ principalBand e ∧
      continuousMapDualIm (c • φ) ∈ principalBand e
    rw [continuousMapDualRe_smul, continuousMapDualIm_smul]
    exact ⟨(principalBand e).sub_mem ((principalBand e).smul_mem c.re hφ.1)
      ((principalBand e).smul_mem c.im hφ.2),
      (principalBand e).add_mem ((principalBand e).smul_mem c.re hφ.2)
        ((principalBand e).smul_mem c.im hφ.1)⟩

instance continuousMapComplexPrincipalBand_normedAddCommGroup
    (e : C(K, ℝ) →L[ℝ] ℝ) : NormedAddCommGroup (continuousMapComplexPrincipalBand e) :=
  inferInstanceAs (NormedAddCommGroup ↥(continuousMapComplexPrincipalBand e))

instance continuousMapComplexPrincipalBand_normedSpace
    (e : C(K, ℝ) →L[ℝ] ℝ) : NormedSpace ℂ (continuousMapComplexPrincipalBand e) :=
  inferInstanceAs (NormedSpace ℂ ↥(continuousMapComplexPrincipalBand e))

theorem abs_continuousMapDualRe_le_modulus (φ : C(K, ℂ) →L[ℂ] ℂ) :
    |continuousMapDualRe φ| ≤ continuousMapComplexModulus φ := by
  apply sup_le
  · simpa using continuousMapDualRe_phase_le φ 1 (by simp)
  · have hh : continuousMapDualRe ((-1 : ℂ) • φ) = -continuousMapDualRe φ := by
      ext g
      change ((-1 : ℂ) * φ (continuousMapOfReal g)).re = -(φ (continuousMapOfReal g)).re
      simp
    simpa only [hh] using continuousMapDualRe_phase_le φ (-1) (by simp)

theorem abs_continuousMapDualIm_le_modulus (φ : C(K, ℂ) →L[ℂ] ℂ) :
    |continuousMapDualIm φ| ≤ continuousMapComplexModulus φ := by
  apply sup_le
  · have hh : continuousMapDualRe (-Complex.I • φ) = continuousMapDualIm φ := by
      ext g
      change ((-Complex.I) * φ (continuousMapOfReal g)).re = (φ (continuousMapOfReal g)).im
      simp
    simpa only [hh] using continuousMapDualRe_phase_le φ (-Complex.I) (by simp)
  · simpa [continuousMapDualRe_smul] using
      continuousMapDualRe_phase_le φ Complex.I (by simp)

theorem continuousMapComplexModulus_le_abs_re_add_abs_im
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapComplexModulus φ ≤ |continuousMapDualRe φ| + |continuousMapDualIm φ| := by
  apply (continuousMapComplexModulus_isLUB φ).2
  rintro _ ⟨c, hc, rfl⟩
  rw [continuousMapDualRe_smul]
  exact complexLatticePhase_le_abs_add (continuousMapDualRe φ) (continuousMapDualIm φ) c hc.le

theorem continuousMapComplexPrincipalBand_mem_iff_modulus
    (e : C(K, ℝ) →L[ℝ] ℝ) (φ : C(K, ℂ) →L[ℂ] ℂ) :
    φ ∈ continuousMapComplexPrincipalBand e ↔ continuousMapComplexModulus φ ∈ principalBand e := by
  let hI := principalBand_orderClosed e
  constructor
  · rintro ⟨hr, hi⟩
    exact hI.nonneg_le_mem ((principalBand e).add_mem (hI.abs_mem hr) (hI.abs_mem hi))
      (continuousMapComplexModulus_nonneg φ) (continuousMapComplexModulus_le_abs_re_add_abs_im φ)
  · intro h
    constructor
    · apply hI.solid h
      simpa only [abs_of_nonneg (α := C(K, ℝ) →L[ℝ] ℝ) (continuousMapComplexModulus_nonneg φ)] using
        abs_continuousMapDualRe_le_modulus φ
    · apply hI.solid h
      simpa only [abs_of_nonneg (α := C(K, ℝ) →L[ℝ] ℝ) (continuousMapComplexModulus_nonneg φ)] using
        abs_continuousMapDualIm_le_modulus φ

end ThesisCommon
