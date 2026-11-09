import PL1.Definitions
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Transport and operator consequences of the reviewed RNP definition

This file uses `PL1.HasRadonNikodymProperty` unchanged, with its full
vector-measure quantifiers and explicit source universe.
-/

noncomputable section
universe u v w
open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace PL1.RNPBridge

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Apply a bounded linear map to a countably additive vector measure. -/
def mapVectorMeasure {Ω : Type w} [MeasurableSpace Ω]
    (T : E →L[ℝ] F) (ν : VectorMeasure Ω E) : VectorMeasure Ω F :=
  ν.mapRange T.toLinearMap.toAddMonoidHom T.continuous

@[simp]
theorem mapVectorMeasure_apply {Ω : Type w} [MeasurableSpace Ω]
    (T : E →L[ℝ] F) (ν : VectorMeasure Ω E) (A : Set Ω) :
    mapVectorMeasure T ν A = T (ν A) := rfl

/-- Bounded maps multiply total variation by at most their operator norm. -/
theorem variation_mapVectorMeasure_le {Ω : Type w} [MeasurableSpace Ω]
    (T : E →L[ℝ] F) (ν : VectorMeasure Ω E) :
    (mapVectorMeasure T ν).variation ≤ ‖T‖ₑ • ν.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro A hA
  simp only [mapVectorMeasure_apply, Measure.smul_apply, smul_eq_mul]
  exact (T.le_opENorm (ν A)).trans
    (mul_le_mul_of_nonneg_left (VectorMeasure.enorm_measure_le_variation ν A) zero_le)

theorem mapVectorMeasure_finite_variation {Ω : Type w} [MeasurableSpace Ω]
    (T : E →L[ℝ] F) (ν : VectorMeasure Ω E) (hν : ν.variation univ < ∞) :
    (mapVectorMeasure T ν).variation univ < ∞ := by
  apply lt_of_le_of_lt (variation_mapVectorMeasure_le T ν univ)
  simpa only [Measure.smul_apply, smul_eq_mul] using
    ENNReal.mul_lt_top (by simp : ‖T‖ₑ < ∞) hν

/-- The reviewed RNP is preserved by real Banach-space isomorphism.
The universe of measurable source spaces is independent of both target universes. -/
theorem hasRadonNikodymProperty_of_equiv (e : E ≃L[ℝ] F)
    (hE : HasRadonNikodymProperty.{u, w} E) : HasRadonNikodymProperty.{v, w} F := by
  intro Ω mΩ
  let := mΩ
  intro μ hμ ν hν hAC
  let η : VectorMeasure Ω E := mapVectorMeasure e.symm.toContinuousLinearMap ν
  have hη : η.variation univ < ∞ := mapVectorMeasure_finite_variation _ ν hν
  have hηAC : ∀ A : Set Ω, MeasurableSet A → μ A = 0 → η A = 0 := by
    intro A hA hz
    change e.symm (ν A) = 0
    rw [hAC A hA hz, map_zero]
  obtain ⟨g, hg, hrepr⟩ := hE Ω mΩ μ hμ η hη hηAC
  refine ⟨fun x => e (g x), e.toContinuousLinearMap.integrable_comp hg, ?_⟩
  intro A hA
  rw [e.integral_comp_comm]
  rw [← hrepr A hA]
  exact (e.apply_symm_apply (ν A)).symm

theorem hasRadonNikodymProperty_iff_equiv (e : E ≃L[ℝ] F) :
    HasRadonNikodymProperty.{u, w} E ↔ HasRadonNikodymProperty.{v, w} F :=
  ⟨hasRadonNikodymProperty_of_equiv e, hasRadonNikodymProperty_of_equiv e.symm⟩

theorem not_hasRadonNikodymProperty_of_equiv (e : E ≃L[ℝ] F)
    (hE : ¬ HasRadonNikodymProperty.{u, w} E) : ¬ HasRadonNikodymProperty.{v, w} F :=
  fun hF => hE (hasRadonNikodymProperty_of_equiv e.symm hF)

section IndicatorMeasure

variable {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The genuine `L1` class of a measurable indicator, extended by zero on
nonmeasurable sets to conform to `VectorMeasure`. -/
def indicatorL1 (A : Set Ω) : Lp ℝ 1 μ := by
  classical
  exact if hA : MeasurableSet A then indicatorConstLp 1 hA (measure_ne_top μ A) (1 : ℝ) else 0

theorem indicatorL1_of_measurable {A : Set Ω} (hA : MeasurableSet A) :
    indicatorL1 μ A = indicatorConstLp 1 hA (measure_ne_top μ A) (1 : ℝ) := by
  simp only [indicatorL1, dite_eq_left hA]

theorem indicatorL1_coeFn {A : Set Ω} (hA : MeasurableSet A) :
    (indicatorL1 μ A : Ω → ℝ) =ᵐ[μ] A.indicator (fun _ => (1 : ℝ)) := by
  rw [indicatorL1_of_measurable μ hA]
  exact indicatorConstLp_coeFn

theorem enorm_indicatorL1_le (A : Set Ω) : ‖indicatorL1 μ A‖ₑ ≤ μ A := by
  by_cases hA : MeasurableSet A
  · rw [indicatorL1_of_measurable μ hA]
    simpa using (enorm_indicatorConstLp_le (p := 1) (hs := hA)
      (hμs := measure_ne_top μ A) (c := (1 : ℝ)))
  · simp [indicatorL1, hA]

theorem norm_indicatorL1 {A : Set Ω} (hA : MeasurableSet A) :
    ‖indicatorL1 μ A‖ = μ.real A := by
  rw [indicatorL1_of_measurable μ hA]
  simpa using (norm_indicatorConstLp (p := 1) (hs := hA)
    (hμs := measure_ne_top μ A) (c := (1 : ℝ)) (by norm_num) (by simp))

theorem indicatorL1_eq_zero_of_null {A : Set Ω} (hA : μ A = 0) : indicatorL1 μ A = 0 := by
  apply enorm_eq_zero.1
  exact le_antisymm (hA ▸ enorm_indicatorL1_le μ A) zero_le

/-- Countable additivity of the canonical indicator-valued vector measure. -/
theorem hasSum_indicatorL1 {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Disjoint on A)) :
    HasSum (fun n => indicatorL1 μ (A n)) (indicatorL1 μ (⋃ n, A n)) := by
  have habs : (∑' n, ‖indicatorL1 μ (A n)‖ₑ) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n, μ (A n) := ENNReal.tsum_le_tsum (fun n => enorm_indicatorL1_le μ (A n))
      _ = μ (⋃ n, A n) := (measure_iUnion hdisj hA).symm
      _ < ∞ := measure_lt_top μ _
  have hsum : Summable (fun n => indicatorL1 μ (A n)) := Summable.of_enorm habs
  have heq : (∑' n, indicatorL1 μ (A n)) = indicatorL1 μ (⋃ n, A n) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_tsum habs,
      ae_all_iff.2 (fun n => indicatorL1_coeFn μ (hA n)),
      indicatorL1_coeFn μ (MeasurableSet.iUnion hA)] with x hx hxi hxU
    rw [hx, hxU]
    simp only [hxi]
    by_cases hmem : ∃ n, x ∈ A n
    · obtain ⟨n, hn⟩ := hmem
      rw [Set.indicator_of_mem (Set.mem_iUnion.2 ⟨n, hn⟩)]
      rw [tsum_eq_single n]
      · exact Set.indicator_of_mem hn _
      · intro k hk
        apply Set.indicator_of_notMem
        intro hxk
        exact Set.disjoint_left.1 (hdisj hk) hxk hn
    · have hnone : ∀ n, x ∉ A n := by simpa using hmem
      have hU : x ∉ ⋃ n, A n := by simpa using hmem
      simp [hnone, hU]
  rw [← heq]
  exact hsum.hasSum

/-- The canonical countably additive `L1`-valued measure `A ↦ 1_A`. -/
def indicatorVectorMeasure : VectorMeasure Ω (Lp ℝ 1 μ) where
  measureOf' := indicatorL1 μ
  empty' := by simp [indicatorL1, indicatorConstLp_empty]
  not_measurable' := by intro A hA; simp [indicatorL1, hA]
  m_iUnion' := by
    intro A hA hdisj
    exact hasSum_indicatorL1 μ hA hdisj

@[simp]
theorem indicatorVectorMeasure_apply (A : Set Ω) :
    indicatorVectorMeasure μ A = indicatorL1 μ A := rfl

theorem variation_indicatorVectorMeasure_le : (indicatorVectorMeasure μ).variation ≤ μ :=
  VectorMeasure.variation_le_of_forall_enorm_le (fun A _ => enorm_indicatorL1_le μ A)

/-- The vector measure canonically induced by an operator out of actual `L1`. -/
def operatorVectorMeasure (T : Lp ℝ 1 μ →L[ℝ] E) : VectorMeasure Ω E :=
  mapVectorMeasure T (indicatorVectorMeasure μ)

@[simp]
theorem operatorVectorMeasure_apply (T : Lp ℝ 1 μ →L[ℝ] E) (A : Set Ω) :
    operatorVectorMeasure μ T A = T (indicatorL1 μ A) := rfl

theorem variation_operatorVectorMeasure_le (T : Lp ℝ 1 μ →L[ℝ] E) :
    (operatorVectorMeasure μ T).variation ≤ ‖T‖ₑ • μ := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro A hA
  simp only [operatorVectorMeasure_apply, Measure.smul_apply, smul_eq_mul]
  exact (T.le_opENorm (indicatorL1 μ A)).trans
    (mul_le_mul_of_nonneg_left (enorm_indicatorL1_le μ A) zero_le)

theorem operatorVectorMeasure_finite_variation (T : Lp ℝ 1 μ →L[ℝ] E) :
    (operatorVectorMeasure μ T).variation univ < ∞ := by
  apply lt_of_le_of_lt (variation_operatorVectorMeasure_le μ T univ)
  simpa only [Measure.smul_apply, smul_eq_mul] using
    ENNReal.mul_lt_top (by simp : ‖T‖ₑ < ∞) (measure_lt_top μ univ)

theorem operatorVectorMeasure_absolutelyContinuous (T : Lp ℝ 1 μ →L[ℝ] E)
    {A : Set Ω} (hA : μ A = 0) : operatorVectorMeasure μ T A = 0 := by
  rw [operatorVectorMeasure_apply, indicatorL1_eq_zero_of_null μ hA, map_zero]

/-- The full reviewed RNP gives a Bochner density for the operator's values on
every measurable indicator. No representability premise is substituted for RNP. -/
theorem exists_setwise_density_of_RNP (hE : HasRadonNikodymProperty.{u, w} E)
    (T : Lp ℝ 1 μ →L[ℝ] E) :
    ∃ g : Ω → E, Integrable g μ ∧ ∀ A : Set Ω, MeasurableSet A →
      T (indicatorL1 μ A) = ∫ x in A, g x ∂μ := by
  obtain ⟨g, hg, hrepr⟩ := hE Ω inferInstance μ (measure_lt_top μ univ)
    (operatorVectorMeasure μ T) (operatorVectorMeasure_finite_variation μ T)
    (fun A _ hA => operatorVectorMeasure_absolutelyContinuous μ T hA)
  exact ⟨g, hg, hrepr⟩

/-- A single nonrepresentable operator witnesses failure of the reviewed RNP. -/
theorem not_RNP_of_no_setwise_density (T : Lp ℝ 1 μ →L[ℝ] E)
    (hT : ¬ ∃ g : Ω → E, Integrable g μ ∧ ∀ A : Set Ω, MeasurableSet A →
      T (indicatorL1 μ A) = ∫ x in A, g x ∂μ) :
    ¬ HasRadonNikodymProperty.{u, w} E := fun hE => hT (exists_setwise_density_of_RNP μ hE T)

end IndicatorMeasure

end PL1.RNPBridge

