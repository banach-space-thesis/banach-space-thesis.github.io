import ThesisCommon.Analysis.OperatorSetContent
import ThesisCommon.Analysis.IntegralKernelOrder

/-! The measure associated to an operator 0 <= S <= K, with K integral.
The content is first constructed on the algebra of finite input sections,
then extended by domination by the finite measure k d(mu x nu). -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem sectionOperatorApply_sub (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (q : Y →ₛ MeasurableSubset X) :
    sectionOperatorApply (S - T) q =ᵐ[ν] fun y => sectionOperatorApply S q y - sectionOperatorApply T q y :=
  simpleFunc_ae_bind q (fun a => Lp.coeFn_sub
    (S (lOneIndicator μ a.val a.property)) (T (lOneIndicator μ a.val a.property)))

theorem operatorSetIntegral_sub (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    operatorSetIntegral (S - T) s = operatorSetIntegral S s - operatorSetIntegral T s := by
  obtain ⟨q, rfl⟩ := hs
  rw [operatorSetIntegral_sectionSet, operatorSetIntegral_sectionSet,
    operatorSetIntegral_sectionSet, integral_congr_ae (sectionOperatorApply_sub S T q),
    integral_sub (integrable_sectionOperatorApply S q) (integrable_sectionOperatorApply T q)]

theorem operatorSetIntegral_prod (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {a : Set X} {b : Set Y} (ha : MeasurableSet a) (hb : MeasurableSet b) :
    operatorSetIntegral S (a ×ˢ b) = ∫ y in b, S (lOneIndicator μ a ha) y ∂ν := by
  let q : Y →ₛ MeasurableSubset X := SimpleFunc.piecewise b hb
    (SimpleFunc.const Y ⟨a, ha⟩) (SimpleFunc.const Y ⟨∅, MeasurableSet.empty⟩)
  have heq : sectionSet q = a ×ˢ b := by
    ext z
    by_cases hz : z.2 ∈ b <;> simp [sectionSet, q, SimpleFunc.piecewise_apply, hz]
  have hrep : sectionOperatorApply S q =ᵐ[ν] b.indicator (S (lOneIndicator μ a ha)) := by
    filter_upwards [Lp.coeFn_zero ℝ 1 ν] with y hy
    change (0 : Lp ℝ 1 ν) y = 0 at hy
    by_cases hyb : y ∈ b
    · simp [sectionOperatorApply, q, SimpleFunc.piecewise_apply, hyb]
    · simpa [sectionOperatorApply, q, SimpleFunc.piecewise_apply, hyb, lOneIndicator_empty] using hy
  rw [← heq, operatorSetIntegral_sectionSet, integral_congr_ae hrep, integral_indicator hb]

variable [SFinite ν] {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.operatorSetIntegral_eq (hk : IsIntegralKernel k K)
    {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    operatorSetIntegral K s = ∫ z in s, k z ∂μ.prod ν := by
  obtain ⟨q, rfl⟩ := hs
  have hrep := simpleFunc_ae_bind q (fun a => hk.apply_indicator a.val a.property)
  rw [operatorSetIntegral_sectionSet, ← integral_indicator (sectionSet_measurable q),
    integral_prod_symm _ (hk.integrable.indicator (sectionSet_measurable q))]
  apply integral_congr_ae
  filter_upwards [hrep] with y hy
  change K (lOneIndicator μ (q y).val (q y).property) y = _
  rw [hy, ← integral_indicator (q y).property]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (if x ∈ (q y).val then k (x, y) else 0) =
      (if x ∈ (q y).val then k (x, y) else 0)
    rfl

def integralKernelMeasure (μ : Measure X) (ν : Measure Y) (k : X × Y → ℝ) : Measure (X × Y) :=
  (μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z))

theorem IsIntegralKernel.isFiniteMeasure_kernelMeasure (hk : IsIntegralKernel k K) :
    IsFiniteMeasure (integralKernelMeasure μ ν k) :=
  isFiniteMeasure_withDensity_ofReal hk.integrable.2

theorem IsIntegralKernel.operatorContent_eq_kernelMeasure (hk : IsIntegralKernel k K)
    (hK : ∀ f, 0 ≤ f → 0 ≤ K f) {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    operatorContent K hK s = integralKernelMeasure μ ν k s := by
  rw [operatorContent_apply, hk.operatorSetIntegral_eq hs, integralKernelMeasure,
    withDensity_apply _ (finiteSectionAlgebra_measurable hs)]
  exact ofReal_integral_eq_lintegral_ofReal hk.integrable.integrableOn
    (ae_restrict_of_ae (hk.nonneg_ae_of_positive hK))

theorem operatorContent_le_kernelMeasure (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    operatorContent S hS s ≤ integralKernelMeasure μ ν k s := by
  have hK : ∀ f, 0 ≤ f → 0 ≤ K f := fun f hf => (hS f hf).trans (hSK f hf)
  rw [← hk.operatorContent_eq_kernelMeasure hK hs, operatorContent_apply, operatorContent_apply]
  exact ENNReal.ofReal_le_ofReal (operatorSetIntegral_mono S K hSK hs)

/-- The actual finite Caratheodory extension of the operator content. -/
def dominatedOperatorMeasure (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) : Measure (X × Y) := by
  letI := hk.isFiniteMeasure_kernelMeasure
  exact measureOfDominatedContent finiteSectionAlgebra_isSetAlgebra
    generateFrom_finiteSectionAlgebra.symm (operatorContent S hS) (integralKernelMeasure μ ν k)
    (fun _ hs => operatorContent_le_kernelMeasure hk S hS hSK hs)

theorem dominatedOperatorMeasure_apply (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    dominatedOperatorMeasure hk S hS hSK s = ENNReal.ofReal (operatorSetIntegral S s) := by
  letI := hk.isFiniteMeasure_kernelMeasure
  exact measureOfDominatedContent_apply finiteSectionAlgebra_isSetAlgebra
    generateFrom_finiteSectionAlgebra.symm (operatorContent S hS) (integralKernelMeasure μ ν k)
    (fun _ ht => operatorContent_le_kernelMeasure hk S hS hSK ht) hs

instance isFiniteMeasure_dominatedOperatorMeasure (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) : IsFiniteMeasure (dominatedOperatorMeasure hk S hS hSK) where
  measure_univ_lt_top := by
    rw [dominatedOperatorMeasure_apply hk S hS hSK finiteSectionAlgebra_isSetAlgebra.univ_mem]
    exact ENNReal.ofReal_lt_top

theorem dominatedOperatorMeasure_prod (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) {a : Set X} {b : Set Y}
    (ha : MeasurableSet a) (hb : MeasurableSet b) :
    dominatedOperatorMeasure hk S hS hSK (a ×ˢ b) =
      ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) := by
  rw [dominatedOperatorMeasure_apply hk S hS hSK (prod_mem_finiteSectionAlgebra ha hb),
    operatorSetIntegral_prod S ha hb]

/-- Domination survives extension. Extend the complementary positive
operator K-S as well; uniqueness on the generating algebra identifies the
sum of the two finite measures with the kernel measure. -/
theorem dominatedOperatorMeasure_le_kernelMeasure (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) :
    dominatedOperatorMeasure hk S hS hSK ≤ integralKernelMeasure μ ν k := by
  have hK : ∀ f, 0 ≤ f → 0 ≤ K f := fun f hf => (hS f hf).trans (hSK f hf)
  have hR : ∀ f, 0 ≤ f → 0 ≤ (K - S) f := fun f hf => sub_nonneg.mpr (hSK f hf)
  have hRK : ∀ f, 0 ≤ f → (K - S) f ≤ K f := fun f hf => sub_le_self _ (hS f hf)
  let M := dominatedOperatorMeasure hk S hS hSK
  let N := dominatedOperatorMeasure hk (K - S) hR hRK
  have hsets (s : Set (X × Y)) (hs : s ∈ finiteSectionAlgebra X Y) :
      (M + N) s = integralKernelMeasure μ ν k s := by
    change (dominatedOperatorMeasure hk S hS hSK + dominatedOperatorMeasure hk (K - S) hR hRK) s = _
    rw [Measure.add_apply, dominatedOperatorMeasure_apply hk S hS hSK hs,
      dominatedOperatorMeasure_apply hk (K - S) hR hRK hs,
      ← ENNReal.ofReal_add (operatorSetIntegral_nonneg S hS hs)
        (operatorSetIntegral_nonneg (K - S) hR hs), operatorSetIntegral_sub K S hs]
    rw [← add_sub_assoc, add_sub_cancel_left]
    exact hk.operatorContent_eq_kernelMeasure hK hs
  have hadd : M + N = integralKernelMeasure μ ν k :=
    ext_of_generate_finite (finiteSectionAlgebra X Y) generateFrom_finiteSectionAlgebra.symm
      finiteSectionAlgebra_isSetAlgebra.isSetRing.isSetSemiring.isPiSystem hsets
      (hsets univ finiteSectionAlgebra_isSetAlgebra.univ_mem)
  change M ≤ _
  rw [← hadd]
  exact Measure.le_add_right le_rfl

theorem dominatedOperatorMeasure_absolutelyContinuous (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) :
    dominatedOperatorMeasure hk S hS hSK ≪ μ.prod ν :=
  (Measure.absolutelyContinuous_of_le (dominatedOperatorMeasure_le_kernelMeasure hk S hS hSK)).trans
    (withDensity_absolutelyContinuous _ _)

end ThesisCommon
