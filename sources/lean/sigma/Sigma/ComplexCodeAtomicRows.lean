import Sigma.ComplexAdmissibleCodes
import Sigma.ComplexConstructionState
import Sigma.CodeAtomicRows
import ThesisCommon.Analysis.LpOperators

/-! Reading the complex atomic rows of a full coefficient code is the existing
scalar-generic restriction contraction. -/
noncomputable section
open ThesisCommon
namespace SigmaNonprimarity

def complexCodeAtomicRows (side : Bool) (c : ComplexFullCoefficientRows) : ComplexAtomicRows :=
  fun n => lpRestrict (𝕜 := ℂ) 1 (baseAtomEmbedding side) (c n)

@[simp] theorem complexCodeAtomicRows_apply (side : Bool) (c : ComplexFullCoefficientRows)
    (n : ℕ) (p : Point) :
    complexCodeAtomicRows side c n p = c n (side,Sum.inl p) := rfl

theorem complexCodeAtomicRows_admissible (side : Bool) (c : ComplexFullCoefficientRows)
    (hc : ComplexFullCodeAdmissible side c) : ComplexAdmissible (complexCodeAtomicRows side c) := by
  refine ⟨?_,hc.2.1,hc.2.2.2.2⟩
  intro n
  calc
    ‖complexCodeAtomicRows side c n‖ = ∑' p, ‖c n (baseAtomEmbedding side p)‖ :=
      JLMS.ellOneOn_norm_eq_tsum _
    _ ≤ ∑' p, ‖c n p‖ :=
      tsum_comp_le_tsum_of_inj (JLMS.ellOneOn_summable_norm (c n))
        (fun _ => norm_nonneg _) (baseAtomEmbedding side).injective
    _ = ‖c n‖ := (JLMS.ellOneOn_norm_eq_tsum (c n)).symm
    _ ≤ 1 := hc.1 n

end SigmaNonprimarity

