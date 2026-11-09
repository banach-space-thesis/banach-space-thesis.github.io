import NonCalkinAlgebra.ComplexificationOperatorParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u v
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem compact_extract (z : ℂ)
    (U : BanachComplexification X →L[ℂ] BanachComplexification Y)
    (hU : IsCompactOperator U) : IsCompactOperator (extractOperator X z U) := by
  exact (hU.comp_clm (embedding X)).clm_comp (evaluation Y z)

/-- The full complex compact ideal is precisely the complexification of the
real compact ideal, not merely a collection of complexified real operators. -/
theorem compact_operatorParts_iff
    (U : BanachComplexification X →L[ℂ] BanachComplexification Y) :
    IsCompactOperator U ↔ IsCompactOperator (extractOperator X 1 U) ∧
      IsCompactOperator (extractOperator X Complex.I U) := by
  constructor
  · intro hU
    exact ⟨compact_extract X 1 U hU, compact_extract X Complex.I U hU⟩
  · rintro ⟨hS, hT⟩
    have heq : U = map X (extractOperator X 1 U) +
        Complex.I • map X (-extractOperator X Complex.I U) :=
      (from_to_operatorParts X U).symm
    rw [heq]
    exact (compact_map X _ hS).add ((compact_map X _ hT.neg).smul Complex.I)

/-- The analogous statement for approximable operators uses norm closures;
it does not assume that approximable and compact operators coincide. -/
theorem approximable_operatorParts_iff
    (U : BanachComplexification X →L[ℂ] BanachComplexification X) :
    U ∈ approximableOperators (BanachComplexification X) ↔
      extractOperator X 1 U ∈ realApproximableMaps X X ∧
      extractOperator X Complex.I U ∈ realApproximableMaps X X := by
  constructor
  · intro hU
    exact ⟨approximable_extract X 1 U hU, approximable_extract X Complex.I U hU⟩
  · rintro ⟨hS, hT⟩
    have heq : U = map X (extractOperator X 1 U) +
        Complex.I • map X (-extractOperator X Complex.I U) :=
      (from_to_operatorParts X U).symm
    rw [heq]
    exact (approximableOperators (BanachComplexification X)).add_mem
      (approximable_map X _ hS)
      ((approximableOperators (BanachComplexification X)).smul_mem Complex.I
        (approximable_map X _ ((realApproximableMaps X X).neg_mem hT)))

/-- Both selected operator ideals have exactly the real-coordinate
description asserted in the paper's complexification argument. -/
theorem operatorIdeal_operatorParts_iff [CompleteSpace X] (k : QuotientConvention)
    (U : BanachComplexification X →L[ℂ] BanachComplexification X) :
    U ∈ operatorIdeal (BanachComplexification X) k ↔
      extractOperator X 1 U ∈ realOperatorIdeal X k ∧
      extractOperator X Complex.I U ∈ realOperatorIdeal X k := by
  cases k
  · exact approximable_operatorParts_iff X U
  · exact compact_operatorParts_iff X U

end NonCalkinAlgebra.BanachComplexification
