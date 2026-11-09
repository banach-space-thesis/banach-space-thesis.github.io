import SurveyStatements.P5VectorBoundedMultiplication

/-! Finite piecewise families of contractions give contractions on actual
vector-valued Lp. Disjoint outer cells avoid a bound by the number of cells. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem vectorLp_sum_ae {ι : Type*} (F : Finset ι)
    (f : ι → Lp E p unitIntervalMeasure) :
    ⇑(∑ i ∈ F, f i) =ᵐ[unitIntervalMeasure] fun x => ∑ i ∈ F, f i x := by
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero E p unitIntervalMeasure
  | @insert i F hi ih =>
      simpa only [Finset.sum_insert hi, Pi.add_apply] using
        (Lp.coeFn_add (f i) (∑ j ∈ F, f j)).trans
          ((EventuallyEq.refl (ae unitIntervalMeasure) (f i) :
            (f i : ℝ → E) =ᵐ[unitIntervalMeasure] f i).add ih)

def piecewiseOperatorLift {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (L : ι → E →L[𝕜] E) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  ∑ i ∈ F, (vectorIndicatorMultiply (𝕜 := 𝕜) (S i) (hS i)).comp
    ((L i).compLpL p unitIntervalMeasure)

theorem piecewiseOperatorLift_ae {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (L : ι → E →L[𝕜] E)
    (f : Lp E p unitIntervalMeasure) :
    piecewiseOperatorLift F S hS L f =ᵐ[unitIntervalMeasure]
      fun x => ∑ i ∈ F, (S i).indicator (fun x => L i (f x)) x := by
  let g (i : ι) := vectorIndicatorMultiply (𝕜 := 𝕜) (S i) (hS i)
    ((L i).compLpL p unitIntervalMeasure f)
  have hg (i : ι) : g i =ᵐ[unitIntervalMeasure]
      (S i).indicator (fun x => L i (f x)) := by
    filter_upwards [vectorIndicatorMultiply_ae (𝕜 := 𝕜) (S i) (hS i)
      ((L i).compLpL p unitIntervalMeasure f), (L i).coeFn_compLpL f] with x hx hL
    change g i x = _ at hx
    rw [hx]
    by_cases hmem : x ∈ S i <;> simp [hmem, hL]
  filter_upwards [vectorLp_sum_ae F g,
    F.eventually_all.mpr (fun i _ => hg i)] with x hsum hterm
  have heq : piecewiseOperatorLift F S hS L f = ∑ i ∈ F, g i := by
    simp only [piecewiseOperatorLift, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, g]
  rw [heq, hsum]
  exact Finset.sum_congr rfl (fun i hi => hterm i hi)

theorem norm_disjoint_operator_indicators_le {ι : Type*}
    (F : Finset ι) (S : ι → Set ℝ) (L : ι → E →L[𝕜] E)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hL : ∀ i ∈ F, ‖L i‖ ≤ 1) (x : ℝ) (f : ℝ → E) :
    ‖∑ i ∈ F, (S i).indicator (fun x => L i (f x)) x‖ ≤ ‖f x‖ := by
  by_cases hactive : ∃ i ∈ F, x ∈ S i
  · obtain ⟨i, hi, hxi⟩ := hactive
    have hsum : (∑ j ∈ F, (S j).indicator (fun x => L j (f x)) x) =
        (S i).indicator (fun x => L i (f x)) x := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hxj : x ∉ S j := (hdisjoint i hi j hj hji.symm).not_mem_of_mem_left hxi
        simp [hxj]
      · intro hn
        exact (hn hi).elim
    rw [hsum, Set.indicator_of_mem hxi]
    exact ((L i).le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hL i hi) (norm_nonneg _))
  · have hzero : (∑ i ∈ F, (S i).indicator (fun x => L i (f x)) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hxi : x ∉ S i := fun hx => hactive ⟨i, hi, hx⟩
      simp [hxi]
    rw [hzero, norm_zero]
    exact norm_nonneg _

theorem norm_piecewiseOperatorLift_apply_le {ι : Type*}
    (F : Finset ι) (S : ι → Set ℝ) (hS : ∀ i, MeasurableSet (S i))
    (L : ι → E →L[𝕜] E)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hL : ∀ i ∈ F, ‖L i‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    ‖piecewiseOperatorLift F S hS L f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [piecewiseOperatorLift_ae F S hS L f] with x hx
  rw [hx]
  exact norm_disjoint_operator_indicators_le F S L hdisjoint hL x f

theorem norm_piecewiseOperatorLift_le {ι : Type*}
    (F : Finset ι) (S : ι → Set ℝ) (hS : ∀ i, MeasurableSet (S i))
    (L : ι → E →L[𝕜] E)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hL : ∀ i ∈ F, ‖L i‖ ≤ 1) : ‖piecewiseOperatorLift (p := p) F S hS L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_piecewiseOperatorLift_apply_le F S hS L hdisjoint hL f

end SurveyStatements.P5
