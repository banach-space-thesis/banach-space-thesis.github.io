import NonCalkinAlgebra.OperatorIdeals

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem finiteRank_mul_left (S T : BoundedOperators X) (hT : HasFiniteRank X T) :
    HasFiniteRank X (S * T) := by
  letI : FiniteDimensional ℂ (LinearMap.range T.toLinearMap) := hT
  let f : (LinearMap.range T.toLinearMap) →ₗ[ℂ] X :=
    S.toLinearMap.comp (LinearMap.range T.toLinearMap).subtype
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f)
  rintro y ⟨x, rfl⟩
  exact ⟨⟨T x, ⟨x, rfl⟩⟩, rfl⟩

theorem finiteRank_mul_right (S T : BoundedOperators X) (hS : HasFiniteRank X S) :
    HasFiniteRank X (S * T) := by
  letI : FiniteDimensional ℂ (LinearMap.range S.toLinearMap) := hS
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range S.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact ⟨T x, rfl⟩

theorem approximable_mul_left (S T : BoundedOperators X) (hT : T ∈ approximableOperators X) :
    S * T ∈ approximableOperators X := by
  have hmap : Set.MapsTo (fun U : BoundedOperators X => S * U)
      (finiteRankOperators X) (finiteRankOperators X) :=
    fun U hU => finiteRank_mul_left X S U hU
  exact hmap.closure (continuous_const.mul continuous_id) hT

theorem approximable_mul_right (S T : BoundedOperators X) (hS : S ∈ approximableOperators X) :
    S * T ∈ approximableOperators X := by
  have hmap : Set.MapsTo (fun U : BoundedOperators X => U * T)
      (finiteRankOperators X) (finiteRankOperators X) :=
    fun U hU => finiteRank_mul_right X U T hU
  exact hmap.closure (continuous_id.mul continuous_const) hS

theorem operatorIdeal_mul_left (convention : QuotientConvention)
    (S T : BoundedOperators X) (hT : T ∈ operatorIdeal X convention) :
    S * T ∈ operatorIdeal X convention := by
  cases convention
  · exact approximable_mul_left X S T hT
  · exact hT.clm_comp S

theorem operatorIdeal_mul_right (convention : QuotientConvention)
    (S T : BoundedOperators X) (hS : S ∈ operatorIdeal X convention) :
    S * T ∈ operatorIdeal X convention := by
  cases convention
  · exact approximable_mul_right X S T hS
  · exact hS.comp_clm T

end NonCalkinAlgebra
