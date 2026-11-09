import PL1.ConcreteResolvents
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # Actual finite-coordinate averaging on the sign group -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PL1.WalshExpectations

open Walsh

/-- Erase the first m coordinates, retaining the tail. -/
def tailProjection (m : ℕ) (x : Walsh.Group) : Walsh.Group :=
  fun j => if j < m then 1 else x j

theorem continuous_tailProjection (m : ℕ) : Continuous (tailProjection m) := by
  apply continuous_pi
  intro j
  by_cases h : j < m
  · simpa only [tailProjection, h, ite_true] using continuous_const
  · simpa only [tailProjection, h, ite_false] using continuous_apply j

theorem character_tailProjection (m : ℕ) (F : Finset ℕ) (x : Walsh.Group) :
    character F (tailProjection m x) = character (F.filter (fun j => m ≤ j)) x := by
  unfold character
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h : j < m
  · simp [tailProjection, h, Nat.not_le.mpr h]
  · simp [tailProjection, h, Nat.le_of_not_gt h]

/-- Haar probability on the subgroup whose first m coordinates are one. -/
def tailMeasure (m : ℕ) : Measure Walsh.Group := haar.map (tailProjection m)

instance (m : ℕ) : IsProbabilityMeasure (tailMeasure m) := by
  unfold tailMeasure
  infer_instance

theorem coefficient_tailMeasure (m : ℕ) (F : Finset ℕ) :
    coefficient (tailMeasure m) F = if F ⊆ Finset.range m then 1 else 0 := by
  rw [coefficient, tailMeasure, integral_map (continuous_tailProjection m).measurable.aemeasurable
    (continuous_character F).aestronglyMeasurable]
  simp_rw [character_tailProjection]
  rw [Walsh.integral_character]
  have h : F.filter (fun j => m ≤ j) = ∅ ↔ F ⊆ Finset.range m := by
    simp only [Finset.filter_eq_empty_iff, Finset.subset_iff, Finset.mem_range]
    constructor
    · intro h j hj
      exact Nat.lt_of_not_ge (h hj)
    · intro h j hj
      exact Nat.not_le.mpr (h hj)
  simp only [h]

variable (K : Type*) [RCLike K]

/-- The genuine contractive finite-coordinate expectation on Haar L1. -/
def expectationL1 (m : ℕ) : Lp K 1 haar →L[K] Lp K 1 haar :=
  convolutionL1 (tailMeasure m)

theorem norm_expectationL1_le_one (m : ℕ) : ‖expectationL1 K m‖ ≤ 1 :=
  norm_convolutionL1_le_one (tailMeasure m)

theorem expectationL1_character (m : ℕ) (F : Finset ℕ) :
    expectationL1 K m (scalarCharacterLp K 1 F) =
      if F ⊆ Finset.range m then scalarCharacterLp K 1 F else 0 := by
  rw [expectationL1, convolutionL1_scalarCharacter, coefficient_tailMeasure]
  split_ifs <;> simp

/-- Finite-coordinate averaging commutes with every probability convolution. -/
theorem expectationL1_commute (m : ℕ) (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] :
    (expectationL1 K m).comp (convolutionL1 ν) =
      (convolutionL1 ν).comp (expectationL1 K m) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, convolutionL1_scalarCharacter,
    map_smul, expectationL1_character]
  split_ifs
  · exact (convolutionL1_scalarCharacter ν F).symm
  · simp

theorem expectationL1_resolvent_commute (m : ℕ) (rates : ℕ → ℝ≥0) (t : Noise.PositiveTime) :
    (expectationL1 K m).comp (Noise.resolventL1 K rates t) =
      (Noise.resolventL1 K rates t).comp (expectationL1 K m) := by
  let := Noise.isProbabilityMeasure_resolventMeasure rates t.property
  exact expectationL1_commute K m (Noise.resolventMeasure rates t)

theorem expectationL1_comp_of_le (m n : ℕ) (hmn : m ≤ n) :
    (expectationL1 K m).comp (expectationL1 K n) = expectationL1 K m := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, expectationL1_character]
  by_cases hm : F ⊆ Finset.range m
  · have hn : F ⊆ Finset.range n := hm.trans (Finset.range_mono hmn)
    simp [hm, hn, expectationL1_character]
  · by_cases hn : F ⊆ Finset.range n <;> simp [hm, hn, expectationL1_character]

theorem expectationL1_idempotent (m : ℕ) :
    (expectationL1 K m).comp (expectationL1 K m) = expectationL1 K m :=
  expectationL1_comp_of_le K m m le_rfl

/-- These actual contractions converge strongly to the identity. -/
theorem tendsto_expectationL1 (f : Lp K 1 haar) :
    Tendsto (fun m => expectationL1 K m f) atTop (𝓝 f) := by
  apply tendsto_apply_of_dense_span (scalarCharacterLp K 1)
    (dense_span_scalarCharacterLp K 1 (by norm_num)) (expectationL1 K)
    (ContinuousLinearMap.id K _) atTop 1 (norm_expectationL1_le_one K)
  intro F
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (F.sup id + 1)] with m hm
  have hF : F ⊆ Finset.range m := by
    intro j hj
    simp only [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hj) (by omega)
  simp only [expectationL1_character, hF, ite_true]
  rfl

/-- The finite-dimensional space of Walsh polynomials using the first m coordinates. -/
def finiteSpan (m : ℕ) : Submodule K (Lp K 1 haar) :=
  Submodule.span K ((scalarCharacterLp K 1) '' ((Finset.range m).powerset : Set (Finset ℕ)))

instance (m : ℕ) : FiniteDimensional K (finiteSpan K m) :=
  FiniteDimensional.span_of_finite K
    ((Finset.finite_toSet (Finset.range m).powerset).image (scalarCharacterLp K 1))

theorem character_mem_finiteSpan (m : ℕ) (F : Finset ℕ) (hF : F ⊆ Finset.range m) :
    scalarCharacterLp K 1 F ∈ finiteSpan K m := by
  apply Submodule.subset_span
  exact ⟨F, Finset.mem_powerset.mpr hF, rfl⟩

theorem expectationL1_mem_finiteSpan (m : ℕ) (f : Lp K 1 haar) :
    expectationL1 K m f ∈ finiteSpan K m := by
  let S := (finiteSpan K m).comap (expectationL1 K m).toLinearMap
  have hclosed : IsClosed (S : Set (Lp K 1 haar)) :=
    (finiteSpan K m).closed_of_finiteDimensional.preimage (expectationL1 K m).continuous
  have hs : Submodule.span K (Set.range (scalarCharacterLp K 1)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨F, rfl⟩
    change expectationL1 K m (scalarCharacterLp K 1 F) ∈ finiteSpan K m
    rw [expectationL1_character]
    split_ifs with hF
    · exact character_mem_finiteSpan K m F hF
    · exact Submodule.zero_mem _
  exact hclosed.closure_subset_iff.mpr hs (dense_span_scalarCharacterLp K 1 (by norm_num) f)

theorem range_expectationL1_le (m : ℕ) :
    (expectationL1 K m).range ≤ finiteSpan K m := by
  rintro x ⟨f, rfl⟩
  exact expectationL1_mem_finiteSpan K m f

/-- The actual expectation operator has finite rank. -/
instance (m : ℕ) : FiniteDimensional K (expectationL1 K m).range :=
  FiniteDimensional.of_injective (Submodule.inclusion (range_expectationL1_le K m))
    (Submodule.inclusion_injective _)

end PL1.WalshExpectations
