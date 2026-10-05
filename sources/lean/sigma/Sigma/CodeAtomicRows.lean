import Sigma.AdmissibleCodes
import ThesisCommon.Analysis.LpOneComap

/-! Extract the actual admissible atomic rows from a full coefficient code. -/
noncomputable section
open ThesisCommon
namespace SigmaNonprimarity

def baseAtomEmbedding (side : Bool) : Point ↪ FullAtom where
  toFun p := (side,Sum.inl p)
  inj' := by intro p q h; exact Sum.inl_injective (congrArg Prod.snd h)

def codeAtomicRows (side : Bool) (c : FullCoefficientRows) : AtomicRows :=
  fun n => lpOneComap (baseAtomEmbedding side) (c n)

@[simp] theorem codeAtomicRows_apply (side : Bool) (c : FullCoefficientRows) (n : ℕ) (p : Point) :
    codeAtomicRows side c n p = c n (side,Sum.inl p) := rfl

theorem codeAtomicRows_admissible (side : Bool) (c : FullCoefficientRows)
    (hc : FullCodeAdmissible side c) : Admissible (codeAtomicRows side c) :=
  ⟨fun n => (lpOneComap_norm_le _ _).trans (hc.1 n), hc.2.1, hc.2.2.2.2⟩

end SigmaNonprimarity
