import NonCalkinAlgebra.BoundedRetraction

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v
namespace BoundedRetraction
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  (s : BoundedRetraction X Y)

theorem finiteRank_extend {T : BoundedOperators Y} (hT : HasFiniteRank Y T) :
    HasFiniteRank X (s.extendOperators T) :=
  finiteDimensional_range_comp_left s.inclusion (T.comp s.projection)
    (finiteDimensional_range_comp_right T s.projection hT)

theorem finiteRank_compress {T : BoundedOperators X} (hT : HasFiniteRank X T) :
    HasFiniteRank Y (s.compressOperators T) :=
  finiteDimensional_range_comp_left s.projection (T.comp s.inclusion)
    (finiteDimensional_range_comp_right T s.inclusion hT)

theorem approximable_extend {T : BoundedOperators Y} (hT : T ∈ approximableOperators Y) :
    s.extendOperators T ∈ approximableOperators X := by
  have hmap : Set.MapsTo s.extendOperators (finiteRankOperators Y) (finiteRankOperators X) :=
    fun T hT => s.finiteRank_extend hT
  exact hmap.closure s.extendOperators.continuous hT

theorem approximable_compress {T : BoundedOperators X} (hT : T ∈ approximableOperators X) :
    s.compressOperators T ∈ approximableOperators Y := by
  have hmap : Set.MapsTo s.compressOperators (finiteRankOperators X) (finiteRankOperators Y) :=
    fun T hT => s.finiteRank_compress hT
  exact hmap.closure s.compressOperators.continuous hT

theorem compact_extend {T : BoundedOperators Y} (hT : IsCompactOperator T) :
    IsCompactOperator (s.extendOperators T) :=
  (hT.comp_clm s.projection).clm_comp s.inclusion

theorem compact_compress {T : BoundedOperators X} (hT : IsCompactOperator T) :
    IsCompactOperator (s.compressOperators T) :=
  (hT.comp_clm s.inclusion).clm_comp s.projection

variable [CompleteSpace X] [CompleteSpace Y]

theorem operatorIdeal_extend (convention : QuotientConvention)
    {T : BoundedOperators Y} (hT : T ∈ operatorIdeal Y convention) :
    s.extendOperators T ∈ operatorIdeal X convention := by
  cases convention
  · exact s.approximable_extend hT
  · exact s.compact_extend hT

theorem operatorIdeal_compress (convention : QuotientConvention)
    {T : BoundedOperators X} (hT : T ∈ operatorIdeal X convention) :
    s.compressOperators T ∈ operatorIdeal Y convention := by
  cases convention
  · exact s.approximable_compress hT
  · exact s.compact_compress hT

end BoundedRetraction
end NonCalkinAlgebra
