import ThesisCommon.Analysis.KernelOperatorNorm

/-! Restricting the genuine product measure of a positive L1 operator gives
an actual positive bounded operator. Measurable relations split operators, and
kernel section bounds give all-vector operator norm bounds for the restrictions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

def lOnePositiveRelation (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (E : Set (X × Y)) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (exists_operator_of_le_clopenOperatorMeasure S hS
    ((clopenOperatorMeasure S hS).restrict E) Measure.restrict_le_self).choose

theorem lOnePositiveRelation_nonneg (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (E : Set (X × Y)) : 0 ≤ lOnePositiveRelation S hS E :=
  (exists_operator_of_le_clopenOperatorMeasure S hS
    ((clopenOperatorMeasure S hS).restrict E) Measure.restrict_le_self).choose_spec.choose

theorem lOnePositiveRelation_spec (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (E : Set (X × Y)) : lOnePositiveRelation S hS E ≤ S ∧
      clopenOperatorMeasure (lOnePositiveRelation S hS E) (lOnePositiveRelation_nonneg S hS E) =
        (clopenOperatorMeasure S hS).restrict E :=
  (exists_operator_of_le_clopenOperatorMeasure S hS
    ((clopenOperatorMeasure S hS).restrict E) Measure.restrict_le_self).choose_spec.choose_spec

theorem lOnePositiveRelation_add_compl (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (E : Set (X × Y)) (hE : MeasurableSet E) :
    lOnePositiveRelation S hS E + lOnePositiveRelation S hS Eᶜ = S := by
  apply clopenOperatorMeasure_injective _ _
    (add_nonneg (lOnePositiveRelation_nonneg S hS E) (lOnePositiveRelation_nonneg S hS Eᶜ)) hS
  rw [clopenOperatorMeasure_add _ _ (lOnePositiveRelation_nonneg S hS E)
      (lOnePositiveRelation_nonneg S hS Eᶜ),
    (lOnePositiveRelation_spec S hS E).2, (lOnePositiveRelation_spec S hS Eᶜ).2,
    Measure.restrict_add_restrict_compl hE]

theorem lOnePositiveRelation_add_disjoint (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (E F : Set (X × Y)) (_hE : MeasurableSet E) (hF : MeasurableSet F) (hd : Disjoint E F) :
    lOnePositiveRelation S hS E + lOnePositiveRelation S hS F = lOnePositiveRelation S hS (E ∪ F) := by
  apply clopenOperatorMeasure_injective _ _
    (add_nonneg (lOnePositiveRelation_nonneg S hS E) (lOnePositiveRelation_nonneg S hS F))
    (lOnePositiveRelation_nonneg S hS (E ∪ F))
  rw [clopenOperatorMeasure_add _ _ (lOnePositiveRelation_nonneg S hS E)
    (lOnePositiveRelation_nonneg S hS F), (lOnePositiveRelation_spec S hS E).2,
    (lOnePositiveRelation_spec S hS F).2, (lOnePositiveRelation_spec S hS (E ∪ F)).2]
  exact (Measure.restrict_union hd hF).symm

theorem lOnePositiveRelation_inter (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (E F : Set (X × Y)) (hF : MeasurableSet F) :
    lOnePositiveRelation (lOnePositiveRelation S hS E) (lOnePositiveRelation_nonneg S hS E) F =
      lOnePositiveRelation S hS (F ∩ E) := by
  apply clopenOperatorMeasure_injective _ _
    (lOnePositiveRelation_nonneg _ _ F) (lOnePositiveRelation_nonneg S hS (F ∩ E))
  rw [(lOnePositiveRelation_spec _ _ F).2, (lOnePositiveRelation_spec S hS E).2,
    (lOnePositiveRelation_spec S hS (F ∩ E)).2, Measure.restrict_restrict hF]

omit [SigmaFinite ν] in
theorem clopenOperatorMeasure_inputCut
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (A : Set X) (hA : MeasurableSet A) :
    clopenOperatorMeasure (S.comp (lpCutL A hA))
      (fun f hf => hS (lpCut A hA f) (lOneCut_nonneg A hA hf)) =
      (clopenOperatorMeasure S hS).restrict (A ×ˢ Set.univ) := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod _ _ ha hb, Measure.restrict_apply (ha.prod hb),
    prod_inter_prod, inter_univ, clopenOperatorMeasure_prod _ _ (ha.inter hA) hb]
  have hi : lpCut A hA (lOneIndicator μ a ha) = lOneIndicator μ (a ∩ A) (ha.inter hA) := by
    apply Lp.ext
    filter_upwards [lpCut_coe A hA (lOneIndicator μ a ha), lOneIndicator_coe (μ := μ) a ha,
      lOneIndicator_coe (μ := μ) (a ∩ A) (ha.inter hA)] with x hx hy hz
    rw [hx, hz]
    by_cases hxa : x ∈ a <;> by_cases hxA : x ∈ A <;> simp [hxa, hxA, hy]
  change ENNReal.ofReal (∫ y in b, S (lpCut A hA (lOneIndicator μ a ha)) y ∂ν) = _
  rw [hi]

theorem lOnePositiveRelation_rectangle
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (A : Set X) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B) :
    lOnePositiveRelation S hS (A ×ˢ B) = (lpCutL B hB).comp (S.comp (lpCutL A hA)) := by
  apply clopenOperatorMeasure_injective _ _ (lOnePositiveRelation_nonneg S hS _)
    (fun f hf => lOneCut_nonneg B hB (hS _ (lOneCut_nonneg A hA hf)))
  rw [(lOnePositiveRelation_spec S hS _).2,
    clopenOperatorMeasure_outputCut (S.comp (lpCutL A hA))
      (fun f hf => hS (lpCut A hA f) (lOneCut_nonneg A hA hf)) B hB,
    clopenOperatorMeasure_inputCut S hS A hA,
    Measure.restrict_restrict (MeasurableSet.univ.prod hB)]
  congr 1
  ext z
  simp [and_comm]

theorem lOnePositiveRelation_kernel (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (E : Set (X × Y)) (hE : MeasurableSet E) :
    μ ⊗ₘ productSetKernel κ E =
      clopenOperatorMeasure (lOnePositiveRelation S hS E) (lOnePositiveRelation_nonneg S hS E) := by
  rw [compProd_productSetKernel μ κ E hE, hκ, (lOnePositiveRelation_spec S hS E).2]

theorem norm_lOnePositiveRelation_le_of_kernel (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (E : Set (X × Y)) (hE : MeasurableSet E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, κ x (Prod.mk x ⁻¹' E) ≤ ENNReal.ofReal C) :
    ‖lOnePositiveRelation S hS E‖ ≤ C := by
  apply (positive_operator_norm_le_iff_kernel_mass _ (lOnePositiveRelation_nonneg S hS E)
    (productSetKernel κ E) (lOnePositiveRelation_kernel S hS κ hκ E hE) C hC).mpr
  filter_upwards [hb] with x hx
  rw [productSetKernel_apply κ E hE, Measure.restrict_apply_univ]
  exact hx

end ThesisCommon
