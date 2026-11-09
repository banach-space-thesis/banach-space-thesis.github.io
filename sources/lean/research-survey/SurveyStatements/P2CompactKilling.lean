import SurveyStatements.P2MetricCardinality
import SurveyStatements.P2SeparableRange

/-! Exact annihilation of countably many compact operators at cardinality above the continuum. -/

noncomputable section
set_option autoImplicit false
open TopologicalSpace

namespace SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Compact ranges have cardinality at most the continuum. -/
theorem mk_range_compactOperator_le_continuum (T : BoundedOperators X)
    (hT : IsCompactOperator T) : Cardinal.mk (Set.range T) ≤ Cardinal.continuum := by
  letI : SeparableSpace (Set.range T) := (compactOperator_range_isSeparable hT).separableSpace
  exact mk_le_continuum_of_separable_metric (Set.range T)

/-- At this size, the countable family has a nonzero common kernel. -/
theorem exists_ne_zero_common_kernel_compacts (hX : Cardinal.continuum < Cardinal.mk X)
    (K : ℕ → BoundedOperators X) (hK : ∀ n, IsCompactOperator (K n)) :
    ∃ x : X, x ≠ 0 ∧ ∀ n, K n x = 0 := by
  classical
  let R : Type v := (Cardinal.continuum : Cardinal.{v}).out
  have hcard : ∀ n, Cardinal.mk (Set.range (K n)) ≤ Cardinal.mk R := by
    intro n
    simpa [R] using mk_range_compactOperator_le_continuum X (K n) (hK n)
  let e : ∀ n, Set.range (K n) ↪ R := fun n =>
    Classical.choice ((Cardinal.le_def _ _).mp (hcard n))
  let f : X → ℕ → R := fun x n => e n ⟨K n x, ⟨x, rfl⟩⟩
  have hf : ¬ Function.Injective f := by
    intro hinj
    have hle := Cardinal.mk_le_of_injective hinj
    have htarget : Cardinal.mk (ℕ → R) = Cardinal.continuum := by
      simp [R, Cardinal.mk_arrow, Cardinal.continuum_power_aleph0]
    exact not_le_of_gt hX (hle.trans_eq htarget)
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hf
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  intro n
  have hcoord := congrFun hxy n
  have hvalue : K n x = K n y := congrArg Subtype.val ((e n).injective hcoord)
  simpa only [map_sub, hvalue, sub_self]

/-- The compact errors in the source can all be killed exactly by one unit vector. -/
theorem exists_unit_common_kernel_compacts (hX : Cardinal.continuum < Cardinal.mk X)
    (K : ℕ → BoundedOperators X) (hK : ∀ n, IsCompactOperator (K n)) :
    ∃ x : X, ‖x‖ = 1 ∧ ∀ n, K n x = 0 := by
  obtain ⟨z, hz, hKz⟩ := exists_ne_zero_common_kernel_compacts X hX K hK
  refine ⟨((‖z‖ : ℂ)⁻¹) • z, ?_, ?_⟩
  · simp [norm_smul, Complex.norm_real, norm_nonneg, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · intro n
    simp only [map_smul, hKz n, smul_zero]

end SurveyStatements.P2
