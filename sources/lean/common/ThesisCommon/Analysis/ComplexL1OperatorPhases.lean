import ThesisCommon.Analysis.ComplexL1Regularity
import ThesisCommon.Analysis.L1OperatorLattice

/-! The actual complex operator modulus is the lattice supremum of real
operator phases. This connects the construction to real band projections. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def complexL1OperatorRe (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (complexL1Re ν).comp (complexL1OperatorRealRestriction T)

def complexL1OperatorIm (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (complexL1Im ν).comp (complexL1OperatorRealRestriction T)

theorem complexL1Operator_ext {T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hr : complexL1OperatorRe T = complexL1OperatorRe U)
    (hi : complexL1OperatorIm T = complexL1OperatorIm U) : T = U := by
  apply complexL1Operator_ext_ofReal
  intro f
  exact complexL1_ext (DFunLike.congr_fun hr f) (DFunLike.congr_fun hi f)

@[simp] theorem complexL1OperatorRe_add (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorRe (T+U) = complexL1OperatorRe T + complexL1OperatorRe U := by
  ext1 f
  simp [complexL1OperatorRe,complexL1OperatorRealRestriction]

@[simp] theorem complexL1OperatorIm_add (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorIm (T+U) = complexL1OperatorIm T + complexL1OperatorIm U := by
  ext1 f
  simp [complexL1OperatorIm,complexL1OperatorRealRestriction]

theorem complexL1OperatorRe_smul (c : ℂ) (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorRe (c • T) = c.re • complexL1OperatorRe T - c.im • complexL1OperatorIm T := by
  ext1 f
  exact complexL1Re_smul c _

theorem complexL1OperatorIm_smul (c : ℂ) (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorIm (c • T) = c.re • complexL1OperatorIm T + c.im • complexL1OperatorRe T := by
  ext1 f
  exact complexL1Im_smul c _

@[simp] theorem complexL1OperatorRe_extension (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    complexL1OperatorRe (complexL1Extension S) = S := by
  ext1 f
  change complexL1Re ν (complexL1Extension S (complexL1OfReal μ f)) = S f
  rw [complexL1Extension_ofReal,complexL1Re_ofReal]

@[simp] theorem complexL1OperatorIm_extension (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    complexL1OperatorIm (complexL1Extension S) = 0 := by
  ext1 f
  change complexL1Im ν (complexL1Extension S (complexL1OfReal μ f)) = 0
  rw [complexL1Extension_ofReal,complexL1Im_ofReal]

def complexL1OperatorPhase (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (c : ℂ) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν := c.re • complexL1OperatorRe T - c.im • complexL1OperatorIm T

theorem complexL1OperatorPhase_apply (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (c : ℂ) (f : Lp ℝ 1 μ) :
    complexL1OperatorPhase T c f = complexL1Re ν (c • T (complexL1OfReal μ f)) :=
  (complexL1Re_smul c _).symm

theorem complexL1OperatorModulus_phase_isLUB (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsLUB {A | ∃ c : ℂ, ‖c‖ = 1 ∧ A = complexL1OperatorPhase T c} (complexL1OperatorModulus T) := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨c,hc,rfl⟩ f hf
    rw [complexL1OperatorPhase_apply]
    exact (complexL1Re_phase_le _ c hc.le).trans
      (complexOperatorModulus_dominates_nonneg (complexL1OperatorRealRestriction T) f hf)
  · intro R hR
    apply complexL1OperatorModulus_least T R
    intro f hf
    apply (complexL1Modulus_isLUB _).2
    rintro _ ⟨c,hc,rfl⟩
    simpa only [complexL1OperatorPhase_apply] using hR ⟨c,hc,rfl⟩ f hf

end ThesisCommon
