import BanachIsometric.QuaternionicCompletion

/-! The completion conclusion in quaternionic Corollary B, with the
functional theorem retained as an explicit hypothesis. -/

namespace BanachIsometric.Quaternionic

open UniformSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]

theorem functionalStatement_implies_completion_corollaryB
    (hA : FunctionalStatement (E := V)) (n : ℕ) (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ V)
    (hmetric : MetricSubspaceHomogeneity (V := V) n) :
    IsHilbertForNorm (V := Completion V) :=
  completion_isHilbertForNorm ((functionalStatement_implies_corollaryB hA n) hn hdim hmetric)

end
end BanachIsometric.Quaternionic
