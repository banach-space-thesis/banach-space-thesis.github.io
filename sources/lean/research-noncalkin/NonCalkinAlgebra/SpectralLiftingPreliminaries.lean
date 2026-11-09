import NonCalkinAlgebra.QuotientAlgebra
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 Set
universe u v

/-- The scalar polynomial occurring in the defect T²-T has finite fibres. -/
theorem idempotentDefect_fibre_finite (w : ℂ) :
    {z : ℂ | z * (z - 1) = w}.Finite := by
  classical
  by_cases h : ({z : ℂ | z * (z - 1) = w} : Set ℂ).Nonempty
  · obtain ⟨z₀, hz₀⟩ := h
    change z₀ * (z₀ - 1) = w at hz₀
    apply (Set.Finite.insert z₀ (Set.finite_singleton (1 - z₀))).subset
    intro z hz
    change z * (z - 1) = w at hz
    have hfac : (z - z₀) * (z + z₀ - 1) = 0 := by linear_combination hz - hz₀
    rcases mul_eq_zero.mp hfac with hleft | hright
    · exact Set.mem_insert_iff.mpr (Or.inl (sub_eq_zero.mp hleft))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
        (eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hright))))
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

theorem countable_idempotentDefect_preimage {S : Set ℂ} (hS : S.Countable) :
    {z : ℂ | z * (z - 1) ∈ S}.Countable := by
  have hc : (⋃ w ∈ S, {z : ℂ | z * (z - 1) = w}).Countable :=
    hS.biUnion (fun w hw => (idempotentDefect_fibre_finite w).countable)
  apply hc.mono
  intro z hz
  exact Set.mem_iUnion.mpr ⟨z * (z - 1), Set.mem_iUnion.mpr ⟨hz, rfl⟩⟩

/-- The needed implication of polynomial spectral mapping, with no
assumption of countability hidden in the operator or quotient definitions. -/
theorem spectrum_countable_of_defect_spectrum_countable
    {A : Type u} [Ring A] [Algebra ℂ A] (T : A)
    (h : (spectrum ℂ (T * T - T)).Countable) : (spectrum ℂ T).Countable := by
  apply (countable_idempotentDefect_preimage h).mono
  intro z hz
  have hm := spectrum.subset_polynomial_aeval T
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℂ) ⟨z, hz, rfl⟩
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X,
    map_sub, Polynomial.aeval_X, map_pow, map_mul, pow_two, mul_sub, mul_one] using hm

/-- A countable complex set misses a circle of radius strictly between 0 and 1. -/
theorem exists_circle_missing_countable_set {S : Set ℂ} (hS : S.Countable) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ S, ‖z‖ ≠ r := by
  classical
  by_contra! h
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ norm '' S := by
    intro r hr
    obtain ⟨z, hz, heq⟩ := h r hr.1 hr.2
    exact ⟨z, hz, heq⟩
  have hc := (hS.image norm).mono hsub
  exact (not_le.mpr (zero_lt_one : (0 : ℝ) < 1)) (Cardinal.Real.Ioo_countable_iff.mp hc)

theorem spectrum_of_nontrivial_idempotent {A : Type u} [Ring A] [Algebra ℂ A]
    (e : A) (he : e * e = e) (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    spectrum ℂ e = {0, 1} := by
  apply le_antisymm (IsIdempotentElem.spectrum_subset ℂ he)
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · apply (spectrum.zero_mem_iff ℂ).mpr
    intro hu
    exact hne1 ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he)
  · have hz1 : z = 1 := Set.mem_singleton_iff.mp hz
    subst z
    rw [spectrum.mem_iff]
    intro hu
    have hmul : (algebraMap ℂ A 1 - e) * e = 0 := by
      rw [map_one, sub_mul, one_mul, he, sub_self]
    obtain ⟨b, hb⟩ := hu.exists_left_inv
    have hz : e = 0 := by
      calc
        e = (b * (algebraMap ℂ A 1 - e)) * e := by rw [hb, one_mul]
        _ = 0 := by rw [mul_assoc, hmul, mul_zero]
    exact hne0 hz

variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

theorem lift_idempotent_of_mem_operatorIdeal (T : BoundedOperators X)
    (hT : T ∈ operatorIdeal X convention) :
    ∃ P : BoundedOperators X, P * P = P ∧ P - T ∈ operatorIdeal X convention := by
  refine ⟨0, by simp, ?_⟩
  simpa only [zero_sub] using (operatorIdeal X convention).neg_mem hT

theorem lift_idempotent_of_one_sub_mem_operatorIdeal (T : BoundedOperators X)
    (hT : 1 - T ∈ operatorIdeal X convention) :
    ∃ P : BoundedOperators X, P * P = P ∧ P - T ∈ operatorIdeal X convention :=
  ⟨1, one_mul 1, hT⟩

end NonCalkinAlgebra
