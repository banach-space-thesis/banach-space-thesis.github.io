import NonCalkinAlgebra.RealOperatorIdeals

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem realFiniteRank_mul_left (S T : X →L[ℝ] X) (hT : T ∈ realFiniteRankMaps X X) :
    S * T ∈ realFiniteRankMaps X X := by
  letI : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hT
  let f : (LinearMap.range T.toLinearMap) →ₗ[ℝ] X :=
    S.toLinearMap.comp (LinearMap.range T.toLinearMap).subtype
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f)
  rintro y ⟨x, rfl⟩
  exact ⟨⟨T x, ⟨x, rfl⟩⟩, rfl⟩

theorem realFiniteRank_mul_right (S T : X →L[ℝ] X) (hS : S ∈ realFiniteRankMaps X X) :
    S * T ∈ realFiniteRankMaps X X := by
  letI : FiniteDimensional ℝ (LinearMap.range S.toLinearMap) := hS
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range S.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact ⟨T x, rfl⟩

theorem realApproximable_mul_left (S T : X →L[ℝ] X) (hT : T ∈ realApproximableMaps X X) :
    S * T ∈ realApproximableMaps X X := by
  have hmap : Set.MapsTo (fun U : X →L[ℝ] X => S * U)
      (realFiniteRankMaps X X) (realFiniteRankMaps X X) :=
    fun U hU => realFiniteRank_mul_left X S U hU
  exact hmap.closure (continuous_const.mul continuous_id) hT

theorem realApproximable_mul_right (S T : X →L[ℝ] X) (hS : S ∈ realApproximableMaps X X) :
    S * T ∈ realApproximableMaps X X := by
  have hmap : Set.MapsTo (fun U : X →L[ℝ] X => U * T)
      (realFiniteRankMaps X X) (realFiniteRankMaps X X) :=
    fun U hU => realFiniteRank_mul_right X U T hU
  exact hmap.closure (continuous_id.mul continuous_const) hS

variable [CompleteSpace X]

theorem realOperatorIdeal_mul_left (k : QuotientConvention)
    (S T : X →L[ℝ] X) (hT : T ∈ realOperatorIdeal X k) :
    S * T ∈ realOperatorIdeal X k := by
  cases k
  · exact realApproximable_mul_left X S T hT
  · exact hT.clm_comp S

theorem realOperatorIdeal_mul_right (k : QuotientConvention)
    (S T : X →L[ℝ] X) (hS : S ∈ realOperatorIdeal X k) :
    S * T ∈ realOperatorIdeal X k := by
  cases k
  · exact realApproximable_mul_right X S T hS
  · exact hS.comp_clm T

end NonCalkinAlgebra
