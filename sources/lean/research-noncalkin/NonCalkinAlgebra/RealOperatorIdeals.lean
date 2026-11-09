import NonCalkinAlgebra.OperatorIdeals

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v
variable (X : Type u) (Y : Type v)
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The real finite-rank maps, using finite dimension over ℝ. -/
def realFiniteRankMaps : Submodule ℝ (X →L[ℝ] Y) where
  carrier := {T | FiniteDimensional ℝ (LinearMap.range T.toLinearMap)}
  zero_mem' := by
    change FiniteDimensional ℝ (LinearMap.range (0 : X →ₗ[ℝ] Y))
    rw [LinearMap.range_zero]
    infer_instance
  add_mem' := by
    intro S T hS hT
    letI : FiniteDimensional ℝ (LinearMap.range S.toLinearMap) := hS
    letI : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hT
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le S.toLinearMap T.toLinearMap)
  smul_mem' := by
    intro r T hT
    letI : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hT
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T.toLinearMap)
    rintro y ⟨x, rfl⟩
    exact (LinearMap.range T.toLinearMap).smul_mem r ⟨x, rfl⟩

/-- Approximable maps are the actual operator-norm closure of real finite-rank maps. -/
def realApproximableMaps : Submodule ℝ (X →L[ℝ] Y) :=
  (realFiniteRankMaps X Y).topologicalClosure

instance realApproximableMaps_isClosed : IsClosed (realApproximableMaps X Y : Set (X →L[ℝ] Y)) :=
  Submodule.isClosed_topologicalClosure _

theorem real_finiteRank_isCompact (T : X →L[ℝ] Y)
    (hT : T ∈ realFiniteRankMaps X Y) : IsCompactOperator T := by
  letI : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hT
  letI : ProperSpace (LinearMap.range T.toLinearMap) :=
    FiniteDimensional.proper ℝ (LinearMap.range T.toLinearMap)
  let U : X →L[ℝ] (LinearMap.range T.toLinearMap) :=
    T.codRestrict (LinearMap.range T.toLinearMap) (fun x => ⟨x, rfl⟩)
  have hU : IsCompactOperator U := by
    apply (isCompactOperator_iff_image_closedBall_subset_compact U.toLinearMap zero_lt_one).mpr
    refine ⟨Metric.closedBall 0 ‖U‖, isCompact_closedBall 0 ‖U‖, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (U.le_opNorm x).trans (by nlinarith [norm_nonneg U])
  exact hU.continuous_comp (LinearMap.range T.toLinearMap).subtypeL.continuous

theorem real_approximable_isCompact [CompleteSpace Y] (T : X →L[ℝ] Y)
    (hT : T ∈ realApproximableMaps X Y) : IsCompactOperator T := by
  have hle : realApproximableMaps X Y ≤ compactOperator (RingHom.id ℝ) X Y := by
    apply Submodule.topologicalClosure_minimal
    · intro T hT
      exact real_finiteRank_isCompact X Y T hT
    · exact isClosed_setOf_isCompactOperator
  exact hle hT

variable [CompleteSpace X]

def realOperatorIdeal (k : QuotientConvention) : Submodule ℝ (X →L[ℝ] X) :=
  match k with
  | .approximable => realApproximableMaps X X
  | .compact => compactOperator (RingHom.id ℝ) X X

instance realOperatorIdeal_isClosed (k : QuotientConvention) :
    IsClosed (realOperatorIdeal X k : Set (X →L[ℝ] X)) := by
  cases k
  · exact realApproximableMaps_isClosed X X
  · exact isClosed_setOf_isCompactOperator

abbrev RealOperatorQuotient (k : QuotientConvention) := (X →L[ℝ] X) ⧸ realOperatorIdeal X k

def realOperatorQuotientMap (k : QuotientConvention) :
    (X →L[ℝ] X) →ₗ[ℝ] RealOperatorQuotient X k := (realOperatorIdeal X k).mkQ

end NonCalkinAlgebra
