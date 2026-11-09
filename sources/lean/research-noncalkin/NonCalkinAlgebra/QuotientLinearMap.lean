import SurveyStatements.P2InvariantQuotient

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem quotientLinearMap_bound (N : Submodule ℂ E) (M : Submodule ℂ F)
    (T : E →L[ℂ] F) (hT : N ≤ (M.comap T.toLinearMap))
    (y : E ⧸ N) : ‖N.mapQ M T.toLinearMap hT y‖ ≤ ‖T‖ * ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hdenom : 0 < ‖T‖ + 1 := by positivity
  have hδ : 0 < ε / (‖T‖ + 1) := div_pos hε hdenom
  obtain ⟨x, hx, hnx⟩ := Submodule.Quotient.norm_mk_lt y hδ
  have hbound : ‖N.mapQ M T.toLinearMap hT y‖ ≤ ‖T‖ * ‖x‖ := by
    rw [← hx]
    exact (Submodule.Quotient.norm_mk_le M (T x)).trans (T.le_opNorm x)
  have hδeq : ε / (‖T‖ + 1) * (‖T‖ + 1) = ε := div_mul_cancel₀ ε hdenom.ne'
  nlinarith [norm_nonneg T]

/-- A bounded map respecting two subspaces descends to their actual normed
quotients. The norm bound follows from near-minimal representatives. -/
def quotientLinearMap (N : Submodule ℂ E) (M : Submodule ℂ F)
    (T : E →L[ℂ] F) (hT : N ≤ M.comap T.toLinearMap) :
    (E ⧸ N) →L[ℂ] (F ⧸ M) :=
  (N.mapQ M T.toLinearMap hT).mkContinuous ‖T‖ (quotientLinearMap_bound N M T hT)

@[simp] theorem quotientLinearMap_mk (N : Submodule ℂ E) (M : Submodule ℂ F)
    (T : E →L[ℂ] F) (hT : N ≤ M.comap T.toLinearMap) (x : E) :
    quotientLinearMap N M T hT (N.mkQ x) = M.mkQ (T x) := rfl

end NonCalkinAlgebra
