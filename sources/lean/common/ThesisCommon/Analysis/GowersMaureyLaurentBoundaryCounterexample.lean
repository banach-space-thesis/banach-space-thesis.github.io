import ThesisCommon.Analysis.GowersMaureyShiftDefects
import ThesisCommon.Analysis.GowersMaureyLaurentOperators

/-! Explicit obstruction to interpreting Laurent representatives as an
operator subalgebra. The unilateral right-left product has diagonal entries
0,1,1,..., whereas every Laurent operator has constant diagonal. Consequently
the multiplicative identification in the source must use the quotient. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem matrixEntry_right_left_zero (D : ConstructionData 𝕜) :
    matrixEntry D 0 0 ((completedSpread D 0 1).comp (completedSpread D 1 0)) = 0 := by
  have h := congrArg (matrixEntry D 0 0) (completedSpread_right_left_defect D)
  simp only [map_sub, matrixEntry_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, completedCoordinate_basisVector,
    ite_true, one_smul] at h
  exact sub_eq_self.mp h

theorem matrixEntry_right_left_succ (D : ConstructionData 𝕜) (n : ℕ) :
    matrixEntry D (n+1) (n+1)
      ((completedSpread D 0 1).comp (completedSpread D 1 0)) = 1 := by
  have h := congrArg (matrixEntry D (n+1) (n+1)) (completedSpread_right_left_defect D)
  simp only [map_sub, matrixEntry_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, completedCoordinate_basisVector,
    ite_true, Nat.zero_ne_add_one, if_false, zero_smul, map_zero] at h
  exact (sub_eq_zero.mp h).symm

theorem completedSpread_right_left_ne_id (D : ConstructionData 𝕜) :
    (completedSpread D 0 1).comp (completedSpread D 1 0) ≠
      ContinuousLinearMap.id 𝕜 (ShiftSpace D) := by
  intro h
  have he := congrArg (matrixEntry D 0 0) h
  rw [matrixEntry_right_left_zero, matrixEntry_apply, ContinuousLinearMap.id_apply,
    completedCoordinate_basisVector, if_pos rfl] at he
  exact zero_ne_one he

theorem completedSpread_right_left_ne_laurentOperator (D : ConstructionData 𝕜)
    (a : WienerSequences 𝕜) :
    (completedSpread D 0 1).comp (completedSpread D 1 0) ≠ laurentOperator D a := by
  intro h
  have h₀ := congrArg (matrixEntry D 0 0) h
  have h₁ := congrArg (matrixEntry D 1 1) h
  rw [matrixEntry_right_left_zero, matrixEntry_laurentOperator] at h₀
  rw [show (1 : ℕ) = 0+1 from rfl, matrixEntry_right_left_succ,
    matrixEntry_laurentOperator] at h₁
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, sub_self] at h₀ h₁
  exact zero_ne_one (h₀.trans h₁.symm)

theorem completedSpread_right_left_not_mem_laurent_range (D : ConstructionData 𝕜) :
    (completedSpread D 0 1).comp (completedSpread D 1 0) ∉ Set.range (laurentOperator D) := by
  rintro ⟨a, ha⟩
  exact completedSpread_right_left_ne_laurentOperator D a ha.symm

theorem exists_laurent_product_not_laurent (D : ConstructionData 𝕜) :
    ∃ a b : WienerSequences 𝕜, ∀ c : WienerSequences 𝕜,
      (laurentOperator D a).comp (laurentOperator D b) ≠ laurentOperator D c := by
  refine ⟨lp.single 1 1 1, lp.single 1 (-1) 1, ?_⟩
  intro c
  rw [laurentOperator_single, laurentOperator_single]
  exact completedSpread_right_left_ne_laurentOperator D c

end ThesisCommon.GowersMaurey
