import SurveyStatements.P1WitnessMassTrim
import SurveyStatements.P1FiniteCoefficientTails

/-! Actual finite witnesses for failure of unit-modulus suppression. The
functional comes from Hahn--Banach, the two phases belong to one fixed finite
cover, and trimming bounds the mass by the first retained coordinate. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def HasUnitModulusSuppressionOn (e : ℕ → X) (K : ℝ) (M : Set ℕ) : Prop :=
  ∀ a : ℕ →₀ ℂ, (a.support : Set ℕ) ⊆ M →
    (∀ i ∈ a.support, ‖a i‖ = 1) → ∀ S : Finset ℕ, S ⊆ a.support →
      ‖∑ i ∈ S, a i • e i‖ ≤ K * ‖Finsupp.linearCombination ℂ e a‖

structure UnitSuppressionWitness (e : ℕ → X) (A : Finset ℂ) where
  coefficients : ℕ →₀ ℂ
  functional : StrongDual ℂ X
  selected : Finset ℕ
  phaseCoeff : ℂ
  phaseValue : ℂ
  coefficients_unit : ∀ i ∈ coefficients.support, ‖coefficients i‖ = 1
  functional_bound : ‖functional‖ ≤ 1
  selected_subset : selected ⊆ coefficients.support
  selected_nonempty : selected.Nonempty
  phaseCoeff_mem : phaseCoeff ∈ A
  phaseValue_mem : phaseValue ∈ A
  coefficient_near : ∀ i ∈ selected, ‖coefficients i - phaseCoeff‖ ≤ (1 / 4 : ℝ)
  functional_near : ∀ i ∈ selected,
    ‖functional (e i) - (‖functional (e i)‖ : ℂ) * phaseValue‖ ≤
      (1 / 4 : ℝ) * ‖functional (e i)‖
  first_support : sInf (coefficients.support : Set ℕ) = sInf (selected : Set ℕ)
  mass_large : 20 * ‖Finsupp.linearCombination ℂ e coefficients‖ <
    ∑ i ∈ selected, ‖functional (e i)‖
  mass_bound : (∑ i ∈ selected, ‖functional (e i)‖) ≤
    (witnessMassBudget (sInf (selected : Set ℕ)) : ℝ) + 1

def UnitSuppressionWitness.mass {e : ℕ → X} {A : Finset ℂ}
    (w : UnitSuppressionWitness e A) : ℝ := ∑ i ∈ w.selected, ‖w.functional (e i)‖

theorem UnitSuppressionWitness.mass_gt_five {e : ℕ → X} {A : Finset ℂ}
    (w : UnitSuppressionWitness e A) (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) :
    5 < w.mass := by
  have hne := w.selected_nonempty.mono w.selected_subset
  have hn := finite_unitModulus_linearCombination_norm_lower e he hp
    w.coefficients w.coefficients_unit hne
  have hmass := w.mass_large
  change 5 < ∑ i ∈ w.selected, ‖w.functional (e i)‖
  linarith

theorem exists_unitSuppressionWitness_of_failure
    (e : ℕ → X) (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (A : Finset ℂ) (D : ℕ) (hD : 0 < D)
    (hsector : ∀ F : Finset ℕ, ∀ a b : ℕ → ℂ,
      (∀ i ∈ F, ‖a i‖ = 1) → ∃ α β : ℂ, α ∈ A ∧ β ∈ A ∧
      ∃ S : Finset ℕ, S ⊆ F ∧
        (∑ i ∈ F, ‖b i‖) ≤ (D : ℝ) * ∑ i ∈ S, ‖b i‖ ∧
        (∀ i ∈ S, ‖a i - α‖ ≤ (1 / 4 : ℝ)) ∧
        ∀ i ∈ S, ‖b i - (‖b i‖ : ℂ) * β‖ ≤ (1 / 4 : ℝ) * ‖b i‖)
    (M : Set ℕ) (hfail : ¬ HasUnitModulusSuppressionOn e (120 * D) M) :
    ∃ w : UnitSuppressionWitness e A, (w.coefficients.support : Set ℕ) ⊆ M := by
  classical
  obtain ⟨a, haM, ha, S, hSa, hlarge⟩ := by
    simpa only [HasUnitModulusSuppressionOn, not_forall, _root_.not_imp, not_le,
      exists_prop] using hfail
  let x := Finsupp.linearCombination ℂ e a
  let y := ∑ i ∈ S, a i • e i
  change 120 * (D : ℝ) * ‖x‖ < ‖y‖ at hlarge
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hynz : y ≠ 0 := by
    intro hy
    have hpos : 0 ≤ (120 * (D : ℝ)) * ‖x‖ := by positivity
    rw [hy, norm_zero] at hlarge
    linarith
  obtain ⟨f, hfnorm, hfy⟩ := exists_dual_vector ℂ y hynz
  have hmass : ‖y‖ ≤ ∑ i ∈ S, ‖f (e i)‖ := by
    calc
      _ = ‖f y‖ := by rw [hfy]; simp
      _ = ‖∑ i ∈ S, a i • f (e i)‖ := by simp only [y, map_sum, map_smul]
      _ ≤ ∑ i ∈ S, ‖a i • f (e i)‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, ha i (hSa hi), one_mul]
  obtain ⟨α, β, hα, hβ, T, hTS, hmassT, hcoeff, hvalue⟩ :=
    hsector S a (fun i => f (e i)) (fun i hi => ha i (hSa hi))
  have hratioT : 120 * ‖x‖ < ∑ i ∈ T, ‖f (e i)‖ := by
    apply (mul_lt_mul_left hDreal).mp
    calc
      (D : ℝ) * (120 * ‖x‖) = 120 * D * ‖x‖ := by ring
      _ < ‖y‖ := hlarge
      _ ≤ ∑ i ∈ S, ‖f (e i)‖ := hmass
      _ ≤ (D : ℝ) * ∑ i ∈ T, ‖f (e i)‖ := hmassT
  have hTpos : 0 < ∑ i ∈ T, ‖f (e i)‖ := by
    exact lt_of_le_of_lt (by positivity : 0 ≤ 120 * ‖x‖) hratioT
  have hw1 (i : ℕ) (_ : i ∈ T) : ‖f (e i)‖ ≤ 1 := by
    simpa only [hfnorm, he i, one_mul] using f.le_opNorm (e i)
  obtain ⟨k, U, hU, hUne, hretain, hupper, hkU⟩ :=
    finite_weighted_tail_trim T (fun i => ‖f (e i)‖)
      (fun i _ => norm_nonneg _) hw1 hTpos
  have hUT : U ⊆ T := by rw [hU]; exact Finset.filter_subset _ _
  have hUa : U ⊆ a.support := hUT.trans (hTS.trans hSa)
  let m := sInf (U : Set ℕ)
  let c := a.filter (fun i => m ≤ i)
  have hmU : m ∈ U := Nat.sInf_mem (Finset.coe_nonempty.mpr hUne)
  have hUc : U ⊆ c.support := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨hUa hi, Nat.sInf_le (show i ∈ (U : Set ℕ) from hi)⟩
  have hcunit : ∀ i ∈ c.support, ‖c i‖ = 1 :=
    finite_coefficient_tail_preserves_unitModulus a ha m
  have hcM : (c.support : Set ℕ) ⊆ M := by
    intro i hi
    exact haM (Finset.mem_filter.mp hi).1
  have hcnorm : ‖Finsupp.linearCombination ℂ e c‖ ≤ 3 * ‖x‖ :=
    finite_coefficient_tail_norm_bound e hp a m
  have hratio : 20 * ‖Finsupp.linearCombination ℂ e c‖ < ∑ i ∈ U, ‖f (e i)‖ := by
    linarith
  have hupperm : (∑ i ∈ U, ‖f (e i)‖) ≤ (witnessMassBudget m : ℝ) + 1 := by
    have hkmin : k ≤ m := hkU m hmU
    have hbudget : (witnessMassBudget k : ℝ) ≤ witnessMassBudget m := by
      exact_mod_cast witnessMassBudget_monotone hkmin
    linarith
  refine ⟨{
    coefficients := c
    functional := f
    selected := U
    phaseCoeff := α
    phaseValue := β
    coefficients_unit := hcunit
    functional_bound := hfnorm.le
    selected_subset := hUc
    selected_nonempty := hUne
    phaseCoeff_mem := hα
    phaseValue_mem := hβ
    coefficient_near := ?_
    functional_near := fun i hi => hvalue i (hUT hi)
    first_support := finite_coefficient_tail_first_support a U hUne hUa
    mass_large := hratio
    mass_bound := hupperm }, hcM⟩
  intro i hi
  rw [Finsupp.filter_apply_pos (fun j => m ≤ j) a
    (Nat.sInf_le (show i ∈ (U : Set ℕ) from hi))]
  exact hcoeff i (hUT hi)

end SurveyStatements.P1
