import PFP.JamesStatements
import ThesisCommon.Analysis.JamesQuasiReflexiveOne
import ThesisCommon.Analysis.JamesHyperplanes
import ThesisCommon.Analysis.QuasiReflexivePrimaryDual

/-! Full proof of the conditional general-p clause of Appendix B.4 on the
actual James sequence space. Quasi-reflexivity of order one, the complemented
lp copy and both hyperplane hypotheses have all been proved independently.
The separate unconditional classical clause still needs primariness of J2.
-/
noncomputable section
namespace PFP
open ThesisCommon
open scoped ENNReal

theorem theorem_B_4_general (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    Theorem_B_4_general 𝕜 p := by
  intro hpl hp hprimary
  have hpl' : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by simp) hp).mpr hpl
  exact primary_dual_of_quasi_reflexive_orderOne
    (jamesSequence_quasiReflexive_orderOne (𝕜 := 𝕜) p hp hpl') hprimary
    (jamesSequence_everyHyperplane p hp) (jamesSequence_dual_everyHyperplane p hp)

end PFP
