import NonCalkinAlgebra.QuotientLinearMap

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem normedQuotientMap_bound (N : Submodule 𝕜 E) (M : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (hT : N ≤ M.comap T.toLinearMap)
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

/-- A scalar-generic version of the quotient map, with the actual quotient
norms. It also applies to restrictions of complex submodules to real scalars. -/
def normedQuotientMap (N : Submodule 𝕜 E) (M : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (hT : N ≤ M.comap T.toLinearMap) :
    (E ⧸ N) →L[𝕜] (F ⧸ M) :=
  (N.mapQ M T.toLinearMap hT).mkContinuous ‖T‖ (normedQuotientMap_bound N M T hT)

@[simp] theorem normedQuotientMap_mk (N : Submodule 𝕜 E) (M : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (hT : N ≤ M.comap T.toLinearMap) (x : E) :
    normedQuotientMap N M T hT (N.mkQ x) = M.mkQ (T x) := rfl

end NonCalkinAlgebra
