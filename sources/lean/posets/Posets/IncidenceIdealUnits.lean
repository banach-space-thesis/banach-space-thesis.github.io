import Posets.FiniteIncidenceAlgebra
import Posets.IdealCounts
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators

/-! Matrix-unit identities for classifying ideals of a finite incidence algebra. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P]
  [LocallyFiniteOrder P] [Fintype P]

abbrev PosetInterval (P : Type) [PartialOrder P] := {st : P × P // st.1 ≤ st.2}

def incidenceUnit (i : PosetInterval P) : IncidenceAlgebra 𝕜 P where
  toFun s t := if s = i.val.1 ∧ t = i.val.2 then 1 else 0
  eq_zero_of_not_le' s t h := by
    split_ifs with he
    · exact False.elim (h (he.1 ▸ he.2 ▸ i.property))
    · rfl

omit [LocallyFiniteOrder P] [Fintype P] in
@[simp] theorem incidenceUnit_apply (i : PosetInterval P) (s t : P) :
    incidenceUnit (𝕜 := 𝕜) i s t = if s = i.val.1 ∧ t = i.val.2 then 1 else 0 := rfl

theorem incidenceUnit_mul_apply (i : PosetInterval P) (f : IncidenceAlgebra 𝕜 P) (s t : P) :
    (incidenceUnit (𝕜 := 𝕜) i * f) s t = if s = i.val.1 then f i.val.2 t else 0 := by
  rw [incidence_mul_univ]
  by_cases hs : s = i.val.1 <;> simp [hs]

theorem mul_incidenceUnit_apply (f : IncidenceAlgebra 𝕜 P) (i : PosetInterval P) (s t : P) :
    (f * incidenceUnit (𝕜 := 𝕜) i) s t = if t = i.val.2 then f s i.val.1 else 0 := by
  rw [incidence_mul_univ]
  by_cases ht : t = i.val.2 <;> simp [ht]

theorem incidence_diagonal_sandwich (f : IncidenceAlgebra 𝕜 P) (i : PosetInterval P) :
    incidenceUnit ⟨(i.val.1, i.val.1), le_rfl⟩ * f *
      incidenceUnit ⟨(i.val.2, i.val.2), le_rfl⟩ = f i.val.1 i.val.2 • incidenceUnit i := by
  ext s t hst
  rw [mul_incidenceUnit_apply, incidenceUnit_mul_apply, IncidenceAlgebra.constSMul_apply]
  by_cases hs : s = i.val.1 <;> by_cases ht : t = i.val.2 <;> simp [hs, ht]

theorem incidence_enlarge_unit (i j : PosetInterval P)
    (hs : j.val.1 ≤ i.val.1) (ht : i.val.2 ≤ j.val.2) :
    incidenceUnit (𝕜 := 𝕜) ⟨(j.val.1, i.val.1), hs⟩ * incidenceUnit i *
      incidenceUnit ⟨(i.val.2, j.val.2), ht⟩ = incidenceUnit j := by
  ext s t hst
  rw [mul_incidenceUnit_apply, incidenceUnit_mul_apply]
  by_cases hsj : s = j.val.1 <;> by_cases htj : t = j.val.2 <;> simp [hsj, htj]

def incidenceEvaluation (s t : P) : IncidenceAlgebra 𝕜 P →ₗ[𝕜] 𝕜 where
  toFun f := f s t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyFiniteOrder P] [Fintype P] in
theorem incidence_sum_apply {ι : Type*} (F : Finset ι) (f : ι → IncidenceAlgebra 𝕜 P) (s t : P) :
    (∑ i ∈ F, f i) s t = ∑ i ∈ F, f i s t :=
  map_sum (incidenceEvaluation (𝕜 := 𝕜) s t) f F

theorem incidence_unit_expansion (f : IncidenceAlgebra 𝕜 P) :
    f = ∑ i : PosetInterval P, f i.val.1 i.val.2 • incidenceUnit i := by
  ext s t hst
  rw [incidence_sum_apply]
  rw [Finset.sum_eq_single (⟨(s, t), hst⟩ : PosetInterval P)]
  · simp [IncidenceAlgebra.constSMul_apply]
  · intro i _ hi
    have hn : ¬ (s = i.val.1 ∧ t = i.val.2) := by
      rintro ⟨hs, ht⟩
      exact hi (Subtype.ext (Prod.ext hs.symm ht.symm))
    simp [IncidenceAlgebra.constSMul_apply, hn]
  · simp

omit [Fintype P] in
theorem incidenceIdeal_smul_mem (I : TwoSidedIdeal (IncidenceAlgebra 𝕜 P))
    (c : 𝕜) {f : IncidenceAlgebra 𝕜 P} (hf : f ∈ I) : c • f ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ _ hf

theorem incidenceUnit_mem_of_coefficient_ne_zero (I : TwoSidedIdeal (IncidenceAlgebra 𝕜 P))
    {f : IncidenceAlgebra 𝕜 P} (hf : f ∈ I) (i : PosetInterval P)
    (hne : f i.val.1 i.val.2 ≠ 0) : incidenceUnit (𝕜 := 𝕜) i ∈ I := by
  have hs : f i.val.1 i.val.2 • incidenceUnit i ∈ I := by
    rw [← incidence_diagonal_sandwich]
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hf)
  have h := incidenceIdeal_smul_mem I (f i.val.1 i.val.2)⁻¹ hs
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using h

end Posets
