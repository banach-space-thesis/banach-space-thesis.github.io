import ThesisCommon.Analysis.L1KernelDiagonalMultiplier

/-! Actual diagonal compression for every bounded real L1 operator. The error
is obtained by restricting its positive and negative operator measures to the
off-diagonal rectangle, so the bound holds on all vectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace X] [TotallyDisconnectedSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

theorem lOnePositiveRelation_offDiagonal_rectangle
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hS : 0 ≤ S)
    (D : Set X) (hD : MeasurableSet D) :
    lOnePositiveRelation S hS ((D ×ˢ D) \ diagonal X) =
      (lpCutL D hD).comp ((S - lOnePositiveRelation S hS (diagonal X)).comp (lpCutL D hD)) := by
  have hd : MeasurableSet (diagonal X) := isClosed_diagonal.measurableSet
  have h := lOnePositiveRelation_add_disjoint S hS
    ((D ×ˢ D) ∩ diagonal X) ((D ×ˢ D) \ diagonal X)
    ((hD.prod hD).inter hd) ((hD.prod hD).diff hd) disjoint_inf_sdiff
  rw [inter_union_diff, lOnePositiveRelation_rectangle S hS D hD D hD] at h
  rw [← lOnePositiveRelation_inter S hS (diagonal X) (D ×ˢ D) (hD.prod hD),
    lOnePositiveRelation_rectangle _ _ D hD D hD] at h
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  exact eq_sub_of_add_eq' h

theorem norm_positive_offDiagonal_compression_le
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hS : 0 ≤ S)
    (κ : Kernel X X) [IsFiniteKernel κ] (hκ : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (D : Set X) (hD : MeasurableSet D) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ x ∈ D, (κ x).real (D \ {x}) ≤ ε) :
    ‖(lpCutL D hD).comp ((S - lOnePositiveRelation S hS (diagonal X)).comp (lpCutL D hD))‖ ≤ ε := by
  rw [← lOnePositiveRelation_offDiagonal_rectangle S hS D hD]
  apply norm_lOnePositiveRelation_le_of_kernel S hS κ hκ _
    ((hD.prod hD).diff isClosed_diagonal.measurableSet) ε hε
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ D
  · have he : Prod.mk x ⁻¹' ((D ×ˢ D) \ diagonal X) = D \ {x} := by
      ext y
      simp [hx, eq_comm]
    rw [he]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mpr (hb x hx)
  · have he : Prod.mk x ⁻¹' ((D ×ˢ D) \ diagonal X) = ∅ := by
      ext y
      simp [hx]
    change κ x (Prod.mk x ⁻¹' ((D ×ˢ D) \ diagonal X)) ≤ ENNReal.ofReal ε
    rw [he, measure_empty]
    exact zero_le _

variable [StandardBorelSpace X]

def realL1SignedDiagonalMultiplier (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  lpBoundedMultiplier (realL1Diagonal T) (realL1Diagonal_measurable T).aestronglyMeasurable
    ‖T‖ (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using realL1Diagonal_abs_le T x)

theorem realL1SignedDiagonalMultiplier_coe (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (f : Lp ℝ 1 μ) :
    realL1SignedDiagonalMultiplier T f =ᵐ[μ] fun x => realL1Diagonal T x * f x :=
  lpBoundedMultiplier_coe _ _ _ _ f

theorem realL1SignedDiagonalMultiplier_eq_relations (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) :
    realL1SignedDiagonalMultiplier T = lOnePositiveRelation T⁺ (posPart_nonneg T) (diagonal X) -
      lOnePositiveRelation T⁻ (negPart_nonneg T) (diagonal X) := by
  let K := realL1ReverseKernel T
  have hb : ∀ x, K.variationKernel x univ ≤ ENNReal.ofReal ‖T‖ := by
    intro x
    rw [← K.fibre_totalVariation]
    exact (realL1ReverseKernel_spec T).1 x
  have hp : ∀ x, K.posPart x univ ≤ ENNReal.ofReal ‖T‖ := by
    intro x
    apply le_trans _ (hb x)
    change K.posPart x univ ≤ K.posPart x univ + K.negPart x univ
    exact le_self_add
  have hn : ∀ x, K.negPart x univ ≤ ENNReal.ofReal ‖T‖ := by
    intro x
    apply le_trans _ (hb x)
    change K.negPart x univ ≤ K.posPart x univ + K.negPart x univ
    exact le_add_self
  rw [lOnePositiveRelation_diagonal_eq_multiplier T⁺ (posPart_nonneg T) K.posPart
      (realL1ReverseKernel_spec T).2.1 ‖T‖ (norm_nonneg T) hp,
    lOnePositiveRelation_diagonal_eq_multiplier T⁻ (negPart_nonneg T) K.negPart
      (realL1ReverseKernel_spec T).2.2.1 ‖T‖ (norm_nonneg T) hn]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [realL1SignedDiagonalMultiplier_coe T f,
    kernelDiagonalMultiplier_coe K.posPart ‖T‖ (norm_nonneg T) hp f,
    kernelDiagonalMultiplier_coe K.negPart ‖T‖ (norm_nonneg T) hn f,
    Lp.coeFn_sub (kernelDiagonalMultiplier K.posPart ‖T‖ (norm_nonneg T) hp f)
      (kernelDiagonalMultiplier K.negPart ‖T‖ (norm_nonneg T) hn f)] with x hx hp' hn' hs
  change _ = ((kernelDiagonalMultiplier K.posPart ‖T‖ (norm_nonneg T) hp f) -
    (kernelDiagonalMultiplier K.negPart ‖T‖ (norm_nonneg T) hn f)) x
  rw [hx, hs, Pi.sub_apply, hp', hn']
  change K.diagonal x * f x = _
  rw [K.diagonal_eq]
  exact sub_mul _ _ _

theorem norm_realL1Diagonal_compression_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (D : Set X) (hD : MeasurableSet D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ x ∈ D, ((realL1ReverseKernel T).variationKernel x).real (D \ {x}) ≤ ε) :
    ‖(lpCutL D hD).comp ((T - realL1SignedDiagonalMultiplier T).comp (lpCutL D hD))‖ ≤ 2 * ε := by
  let K := realL1ReverseKernel T
  have hp : ∀ x ∈ D, (K.posPart x).real (D \ {x}) ≤ ε := by
    intro x hx
    apply le_trans _ (hb x hx)
    change (K.posPart x).real _ ≤ (K.posPart x + K.negPart x).real _
    rw [measureReal_add_apply]
    exact le_add_of_nonneg_right measureReal_nonneg
  have hn : ∀ x ∈ D, (K.negPart x).real (D \ {x}) ≤ ε := by
    intro x hx
    apply le_trans _ (hb x hx)
    change (K.negPart x).real _ ≤ (K.posPart x + K.negPart x).real _
    rw [measureReal_add_apply]
    exact le_add_of_nonneg_left measureReal_nonneg
  have hp' := norm_positive_offDiagonal_compression_le T⁺ (posPart_nonneg T) K.posPart
    (realL1ReverseKernel_spec T).2.1 D hD ε hε hp
  have hn' := norm_positive_offDiagonal_compression_le T⁻ (negPart_nonneg T) K.negPart
    (realL1ReverseKernel_spec T).2.2.1 D hD ε hε hn
  rw [realL1SignedDiagonalMultiplier_eq_relations]
  have he : T - (lOnePositiveRelation T⁺ (posPart_nonneg T) (diagonal X) -
      lOnePositiveRelation T⁻ (negPart_nonneg T) (diagonal X)) =
      (T⁺ - lOnePositiveRelation T⁺ (posPart_nonneg T) (diagonal X)) -
      (T⁻ - lOnePositiveRelation T⁻ (negPart_nonneg T) (diagonal X)) := by
    calc
      _ = (T⁺ - T⁻) - (lOnePositiveRelation T⁺ (posPart_nonneg T) (diagonal X) -
          lOnePositiveRelation T⁻ (negPart_nonneg T) (diagonal X)) := by rw [posPart_sub_negPart]
      _ = _ := by abel
  rw [he, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  exact (norm_sub_le _ _).trans (by linarith)

end ThesisCommon

