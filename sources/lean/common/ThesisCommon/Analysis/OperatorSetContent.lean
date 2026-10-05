import ThesisCommon.Analysis.IntegralKernelModulus
import ThesisCommon.Analysis.FiniteSectionAlgebra
import ThesisCommon.Analysis.SimpleFuncDiagonal
import ThesisCommon.Analysis.DominatedContent

/-! The content associated to a positive L1 operator, on the concrete algebra
of product sets with finitely many input sections. On a rectangle A x B its
value is the integral over B of S(1_A). Finite simple-function patterns make
all uses of chosen L1 representatives simultaneous outside one null set. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem lOneIndicator_empty : lOneIndicator μ ∅ MeasurableSet.empty = 0 := by
  apply Lp.ext
  exact (lOneIndicator_coe ∅ MeasurableSet.empty).trans
    (by simpa only [indicator_empty] using (Lp.coeFn_zero ℝ 1 μ).symm)

theorem lOneIndicator_union {a b : Set X} (ha : MeasurableSet a) (hb : MeasurableSet b)
    (hab : Disjoint a b) :
    lOneIndicator μ (a ∪ b) (ha.union hb) = lOneIndicator μ a ha + lOneIndicator μ b hb := by
  apply Lp.ext
  filter_upwards [lOneIndicator_coe (μ := μ) (a ∪ b) (ha.union hb),
    lOneIndicator_coe (μ := μ) a ha, lOneIndicator_coe (μ := μ) b hb,
    Lp.coeFn_add (lOneIndicator μ a ha) (lOneIndicator μ b hb)] with x hu ha' hb' hadd
  rw [hu, hadd, Pi.add_apply, ha', hb', Set.indicator_union_of_disjoint hab]

def sectionOperatorApply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (q : Y →ₛ MeasurableSubset X) (y : Y) : ℝ :=
  S (lOneIndicator μ (q y).val (q y).property) y

theorem measurable_sectionOperatorApply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (q : Y →ₛ MeasurableSubset X) : Measurable (sectionOperatorApply S q) :=
  q.measurable_bind (fun a => S (lOneIndicator μ a.val a.property))
    (fun _ => (Lp.stronglyMeasurable _).measurable)

theorem integrable_sectionOperatorApply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (q : Y →ₛ MeasurableSubset X) : Integrable (sectionOperatorApply S q) ν :=
  simpleFunc_integrable_bind q (fun a => S (lOneIndicator μ a.val a.property))
    (fun _ => (Lp.stronglyMeasurable _).measurable) (fun _ => L1.integrable_coeFn _)

theorem sectionOperatorApply_nonneg (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) (q : Y →ₛ MeasurableSubset X) :
    0 ≤ᵐ[ν] sectionOperatorApply S q :=
  simpleFunc_ae_bind q (fun a => (Lp.coeFn_nonneg _).mpr
    (hS _ (lOneIndicator_nonneg a.val a.property)))

theorem sectionOperatorApply_mono (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hST : ∀ f, 0 ≤ f → S f ≤ T f) (q : Y →ₛ MeasurableSubset X) :
    sectionOperatorApply S q ≤ᵐ[ν] sectionOperatorApply T q :=
  simpleFunc_ae_bind q (fun a => (Lp.coeFn_le _ _).mpr
    (hST _ (lOneIndicator_nonneg a.val a.property)))

theorem sectionOperatorApply_union (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (q r : Y →ₛ MeasurableSubset X) (hdisj : Disjoint (sectionSet q) (sectionSet r)) :
    sectionOperatorApply S ((q.pair r).map
      (fun a => ⟨a.1.val ∪ a.2.val, a.1.property.union a.2.property⟩)) =ᵐ[ν]
      fun y => sectionOperatorApply S q y + sectionOperatorApply S r y := by
  have hd (y : Y) : Disjoint (q y).val (r y).val := by
    apply Set.disjoint_left.mpr
    intro x hxq hxr
    have hxq' : (x, y) ∈ sectionSet q := hxq
    have hxr' : (x, y) ∈ sectionSet r := hxr
    exact Set.disjoint_left.mp hdisj hxq' hxr'
  have hcoe := simpleFunc_ae_bind (q.pair r) (fun a =>
    Lp.coeFn_add (S (lOneIndicator μ a.1.val a.1.property))
      (S (lOneIndicator μ a.2.val a.2.property)))
  filter_upwards [hcoe] with y hy
  dsimp only [sectionOperatorApply, SimpleFunc.map_apply, SimpleFunc.pair_apply] at *
  rw [lOneIndicator_union (q y).property (r y).property (hd y), map_add, hy]
  rfl

/-- The real-valued content before using positivity. Values outside the
section algebra are immaterial and are set to zero. -/
def operatorSetIntegral (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (s : Set (X × Y)) : ℝ :=
  if hs : s ∈ finiteSectionAlgebra X Y then ∫ y, sectionOperatorApply S hs.choose y ∂ν else 0

theorem operatorSetIntegral_sectionSet (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (q : Y →ₛ MeasurableSubset X) :
    operatorSetIntegral S (sectionSet q) = ∫ y, sectionOperatorApply S q y ∂ν := by
  classical
  have hq : sectionSet q ∈ finiteSectionAlgebra X Y := ⟨q, rfl⟩
  rw [operatorSetIntegral, dif_pos hq, sectionSet_injective hq.choose_spec]

theorem operatorSetIntegral_empty (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    operatorSetIntegral S ∅ = 0 := by
  let q : Y →ₛ MeasurableSubset X := SimpleFunc.const Y ⟨∅, MeasurableSet.empty⟩
  have heq : sectionSet q = ∅ := by ext z; simp [q, sectionSet]
  rw [← heq, operatorSetIntegral_sectionSet]
  have hzero : sectionOperatorApply S q =ᵐ[ν] fun _ => (0 : ℝ) := by
    change (fun y => S (lOneIndicator μ ∅ MeasurableSet.empty) y) =ᵐ[ν] _
    rw [lOneIndicator_empty, map_zero]
    exact Lp.coeFn_zero ℝ 1 ν
  rw [integral_congr_ae hzero, integral_zero]

theorem operatorSetIntegral_nonneg (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    0 ≤ operatorSetIntegral S s := by
  obtain ⟨q, rfl⟩ := hs
  rw [operatorSetIntegral_sectionSet]
  exact integral_nonneg_of_ae (sectionOperatorApply_nonneg S hS q)

theorem operatorSetIntegral_mono (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hST : ∀ f, 0 ≤ f → S f ≤ T f) {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    operatorSetIntegral S s ≤ operatorSetIntegral T s := by
  obtain ⟨q, rfl⟩ := hs
  rw [operatorSetIntegral_sectionSet, operatorSetIntegral_sectionSet]
  exact integral_mono_ae (integrable_sectionOperatorApply S q)
    (integrable_sectionOperatorApply T q) (sectionOperatorApply_mono S T hST q)

theorem operatorSetIntegral_union (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {s t : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) (ht : t ∈ finiteSectionAlgebra X Y)
    (hdisj : Disjoint s t) : operatorSetIntegral S (s ∪ t) = operatorSetIntegral S s + operatorSetIntegral S t := by
  obtain ⟨q, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := ht
  let u := (q.pair r).map (fun a => (⟨a.1.val ∪ a.2.val, a.1.property.union a.2.property⟩ : MeasurableSubset X))
  have heq : sectionSet q ∪ sectionSet r = sectionSet u := by ext z; simp [sectionSet, u]
  rw [heq, operatorSetIntegral_sectionSet, operatorSetIntegral_sectionSet,
    operatorSetIntegral_sectionSet, integral_congr_ae (sectionOperatorApply_union S q r hdisj),
    integral_add (integrable_sectionOperatorApply S q) (integrable_sectionOperatorApply S r)]

def operatorContent (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    AddContent (finiteSectionAlgebra X Y) :=
  finiteSectionAlgebra_isSetAlgebra.isSetRing.addContent_of_union
    (fun s => ENNReal.ofReal (operatorSetIntegral S s))
    (by dsimp only; rw [operatorSetIntegral_empty, ENNReal.ofReal_zero])
    (fun hs ht hd => by
      dsimp only
      rw [operatorSetIntegral_union S hs ht hd,
        ENNReal.ofReal_add (operatorSetIntegral_nonneg S hS hs) (operatorSetIntegral_nonneg S hS ht)])

theorem operatorContent_apply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) (s : Set (X × Y)) :
    operatorContent S hS s = ENNReal.ofReal (operatorSetIntegral S s) := rfl

end ThesisCommon
