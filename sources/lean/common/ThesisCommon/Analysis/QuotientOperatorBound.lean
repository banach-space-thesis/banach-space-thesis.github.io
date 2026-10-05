import ThesisCommon.QuotientOperator
import Mathlib.Tactic

noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_quotientOperator_le (p : Submodule 𝕜 E) (q : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (h : p ≤ q.comap T.toLinearMap) :
    quotientOperatorNorm p q T h ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro ξ
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (‖T‖ + 1)
  have hpos : 0 < ‖T‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hpos
  obtain ⟨x, hx, hnx⟩ := Submodule.Quotient.norm_mk_lt ξ hδ
  have hd : ‖T‖ * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  calc
    ‖quotientOperator p q T h ξ‖ = ‖(Submodule.Quotient.mk (T x) : F ⧸ q)‖ := by rw [← hx]; rfl
    _ ≤ ‖T x‖ := Submodule.Quotient.norm_mk_le q (T x)
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ ≤ ‖T‖ * (‖ξ‖ + δ) := mul_le_mul_of_nonneg_left hnx.le (norm_nonneg T)
    _ = ‖T‖ * ‖ξ‖ + ‖T‖ * δ := mul_add _ _ _
    _ ≤ ‖T‖ * ‖ξ‖ + ε := add_le_add_left hd _

end ThesisCommon
