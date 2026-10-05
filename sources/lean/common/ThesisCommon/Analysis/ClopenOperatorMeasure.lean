import ThesisCommon.Analysis.CompactContent
import ThesisCommon.Analysis.IntegralOperatorMeasure
import ThesisCommon.Analysis.L1IndicatorExt

/-! Every positive operator between real L1 spaces over compact, second
countable, totally disconnected Hausdorff spaces has an actual finite product
measure. The construction extends its clopen content using compactness, and
therefore also applies to singular operators without an integral dominator. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Classical
namespace ThesisCommon
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y]
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

theorem clopen_mem_finiteSectionAlgebra {s : Set (X × Y)} (hs : IsClopen s) :
    s ∈ finiteSectionAlgebra X Y := by
  obtain ⟨I, hI⟩ := (⟨s, hs⟩ : Clopens (X × Y)).exists_finset_eq_sup_prod
  have hfinite : ∀ J : Finset (Clopens X × Clopens Y),
      ((J.sup (fun i => i.1 ×ˢ i.2) : Clopens (X × Y)) : Set (X × Y)) ∈
        finiteSectionAlgebra X Y := by
    intro J
    induction J using Finset.induction_on with
    | empty => exact finiteSectionAlgebra_isSetAlgebra.empty_mem
    | @insert i J hi hJ =>
      rw [Finset.sup_insert]
      exact finiteSectionAlgebra_isSetAlgebra.union_mem
        (prod_mem_finiteSectionAlgebra i.1.isClopen.isOpen.measurableSet
          i.2.isClopen.isOpen.measurableSet) hJ
  simpa only [← hI] using hfinite I

variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] in
theorem measurableSet_isSetAlgebra : IsSetAlgebra {a : Set X | MeasurableSet a} where
  empty_mem := MeasurableSet.empty
  compl_mem := fun _ ha => ha.compl
  union_mem := fun _ _ ha hb => ha.union hb

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] in
theorem lOneIndicator_norm {a : Set X} (ha : MeasurableSet a) :
    ‖lOneIndicator μ a ha‖ = (μ a).toReal := by
  have heq := indicatorConstLp_eq_smul_lOneIndicator (μ := μ) a ha (measure_ne_top μ a) (1 : ℝ)
  rw [one_smul] at heq
  rw [← heq, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Measure.real]

def operatorRectangleContent (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {b : Set Y} (hb : MeasurableSet b) :
    AddContent {a : Set X | MeasurableSet a} :=
  measurableSet_isSetAlgebra.isSetRing.addContent_of_union
    (fun a => operatorContent S hS (a ×ˢ b))
    (by simp only [empty_prod, addContent_empty])
    (fun ha ha' hdisj => by
      dsimp only
      rw [union_prod]
      exact addContent_union finiteSectionAlgebra_isSetAlgebra.isSetRing
        (prod_mem_finiteSectionAlgebra ha hb) (prod_mem_finiteSectionAlgebra ha' hb)
        (disjoint_prod.mpr (Or.inl hdisj)))

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [OpensMeasurableSpace Y] in
theorem operatorRectangleContent_le (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {b : Set Y} (hb : MeasurableSet b)
    {a : Set X} (ha : MeasurableSet a) :
    operatorRectangleContent S hS hb a ≤ (ENNReal.ofReal ‖S‖ • μ) a := by
  change ENNReal.ofReal (operatorSetIntegral S (a ×ˢ b)) ≤ _
  rw [operatorSetIntegral_prod S ha hb, Measure.smul_apply, smul_eq_mul,
    ← ENNReal.ofReal_toReal (measure_ne_top μ a), ← ENNReal.ofReal_mul (norm_nonneg S)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) ≤
        ∫ y, S (lOneIndicator μ a ha) y ∂ν :=
      setIntegral_le_integral (L1.integrable_coeFn _)
        ((Lp.coeFn_nonneg _).mpr (hS _ (lOneIndicator_nonneg a ha)))
    _ ≤ ∫ y, ‖S (lOneIndicator μ a ha) y‖ ∂ν :=
      integral_mono (L1.integrable_coeFn _) (L1.integrable_coeFn _).norm
        (fun y => le_abs_self _)
    _ = ‖S (lOneIndicator μ a ha)‖ := (L1.norm_eq_integral_norm _).symm
    _ ≤ ‖S‖ * ‖lOneIndicator μ a ha‖ := S.le_opNorm _
    _ = ‖S‖ * (μ a).toReal := by rw [lOneIndicator_norm ha]

instance isFiniteMeasure_ofReal_opNorm_smul (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsFiniteMeasure (ENNReal.ofReal ‖S‖ • μ) where
  measure_univ_lt_top := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

def operatorRectangleMeasure (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {b : Set Y} (hb : MeasurableSet b) : Measure X :=
  measureOfDominatedContent measurableSet_isSetAlgebra
    MeasurableSpace.generateFrom_measurableSet.symm (operatorRectangleContent S hS hb)
    (ENNReal.ofReal ‖S‖ • μ) (fun _ ha => operatorRectangleContent_le S hS hb ha)

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [OpensMeasurableSpace Y] in
theorem operatorRectangleMeasure_apply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {b : Set Y} (hb : MeasurableSet b)
    {a : Set X} (ha : MeasurableSet a) :
    operatorRectangleMeasure S hS hb a =
      ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) := by
  rw [operatorRectangleMeasure, measureOfDominatedContent_apply _ _ _ _ _ ha]
  change ENNReal.ofReal (operatorSetIntegral S (a ×ˢ b)) = _
  rw [operatorSetIntegral_prod S ha hb]

instance isFiniteMeasure_operatorRectangleMeasure (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {b : Set Y} (hb : MeasurableSet b) :
    IsFiniteMeasure (operatorRectangleMeasure S hS hb) := by
  unfold operatorRectangleMeasure
  infer_instance

def clopenOperatorContent (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) : AddContent (clopenAlgebra (X × Y)) where
  toFun := operatorContent S hS
  empty' := addContent_empty
  sUnion' _ hI hdisj hUnion :=
    addContent_sUnion (m := operatorContent S hS)
      (fun _ hs => clopen_mem_finiteSectionAlgebra (hI hs)) hdisj
      (clopen_mem_finiteSectionAlgebra hUnion)

variable [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

def clopenOperatorMeasure (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) : Measure (X × Y) :=
  measureOfClopenContent (clopenOperatorContent S hS)

theorem clopenOperatorMeasure_apply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {s : Set (X × Y)} (hs : IsClopen s) :
    clopenOperatorMeasure S hS s = ENNReal.ofReal (operatorSetIntegral S s) :=
  measureOfClopenContent_apply (clopenOperatorContent S hS) hs

theorem clopenOperatorMeasure_clopen_prod (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) {a : Set X} {b : Set Y}
    (ha : IsClopen a) (hb : IsClopen b) :
    clopenOperatorMeasure S hS (a ×ˢ b) =
      ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha.isOpen.measurableSet) y ∂ν) := by
  rw [clopenOperatorMeasure_apply S hS (ha.prod hb),
    operatorSetIntegral_prod S ha.isOpen.measurableSet hb.isOpen.measurableSet]

theorem clopenOperatorMeasure_univ (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    clopenOperatorMeasure S hS univ =
      ENNReal.ofReal (∫ y, S (lOneIndicator μ univ MeasurableSet.univ) y ∂ν) := by
  simpa only [univ_prod_univ, Measure.restrict_univ] using
    clopenOperatorMeasure_clopen_prod S hS isClopen_univ isClopen_univ

instance isFiniteMeasure_clopenOperatorMeasure (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) : IsFiniteMeasure (clopenOperatorMeasure S hS) where
  measure_univ_lt_top := by rw [clopenOperatorMeasure_univ]; exact ENNReal.ofReal_lt_top

theorem map_fst_restrict_prod_apply {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (M : Measure (A × B)) {a : Set A} (ha : MeasurableSet a) (b : Set B) :
    (M.restrict (univ ×ˢ b)).map Prod.fst a = M (a ×ˢ b) := by
  rw [Measure.map_apply measurable_fst ha, Measure.restrict_apply (measurable_fst ha)]
  congr 1
  ext z
  simp

theorem map_snd_restrict_prod_apply {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (M : Measure (A × B)) (a : Set A) {b : Set B} (hb : MeasurableSet b) :
    (M.restrict (a ×ˢ univ)).map Prod.snd b = M (a ×ˢ b) := by
  rw [Measure.map_apply measurable_snd hb, Measure.restrict_apply (measurable_snd hb)]
  congr 1
  ext z
  simp [and_comm]

theorem clopenOperatorMeasure_measurable_clopen_prod
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    {a : Set X} {b : Set Y} (ha : MeasurableSet a) (hb : IsClopen b) :
    clopenOperatorMeasure S hS (a ×ˢ b) =
      ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) := by
  let M := (clopenOperatorMeasure S hS).restrict (univ ×ˢ b) |>.map Prod.fst
  let N := operatorRectangleMeasure S hS hb.isOpen.measurableSet
  have hsets : ∀ c ∈ clopenAlgebra X, M c = N c := by
    intro c hc
    change ((clopenOperatorMeasure S hS).restrict (univ ×ˢ b)).map Prod.fst c =
      operatorRectangleMeasure S hS hb.isOpen.measurableSet c
    rw [map_fst_restrict_prod_apply _ hc.isOpen.measurableSet,
      clopenOperatorMeasure_clopen_prod S hS hc hb,
      operatorRectangleMeasure_apply S hS hb.isOpen.measurableSet hc.isOpen.measurableSet]
  have heq : M = N := ext_of_generate_finite (clopenAlgebra X)
    generateFrom_clopenAlgebra clopenAlgebra_isSetAlgebra.isSetRing.isSetSemiring.isPiSystem
    hsets (hsets univ isClopen_univ)
  have heq' := congrArg (fun R : Measure X => R a) heq
  change ((clopenOperatorMeasure S hS).restrict (univ ×ˢ b)).map Prod.fst a =
    operatorRectangleMeasure S hS hb.isOpen.measurableSet a at heq'
  simpa only [map_fst_restrict_prod_apply _ ha,
    operatorRectangleMeasure_apply S hS hb.isOpen.measurableSet ha] using heq'

theorem clopenOperatorMeasure_prod
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    {a : Set X} {b : Set Y} (ha : MeasurableSet a) (hb : MeasurableSet b) :
    clopenOperatorMeasure S hS (a ×ˢ b) =
      ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) := by
  let M := (clopenOperatorMeasure S hS).restrict (a ×ˢ univ) |>.map Prod.snd
  let N := ν.withDensity (fun y => ENNReal.ofReal (S (lOneIndicator μ a ha) y))
  have hpos : 0 ≤ᵐ[ν] fun y => S (lOneIndicator μ a ha) y :=
    (Lp.coeFn_nonneg _).mpr (hS _ (lOneIndicator_nonneg a ha))
  letI : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal (L1.integrable_coeFn _).2
  have hN : ∀ c : Set Y, MeasurableSet c → N c =
      ENNReal.ofReal (∫ y in c, S (lOneIndicator μ a ha) y ∂ν) := by
    intro c hc
    rw [show N = ν.withDensity (fun y => ENNReal.ofReal (S (lOneIndicator μ a ha) y)) from rfl,
      withDensity_apply _ hc]
    exact (ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae hpos)).symm
  have hsets : ∀ c ∈ clopenAlgebra Y, M c = N c := by
    intro c hc
    change ((clopenOperatorMeasure S hS).restrict (a ×ˢ univ)).map Prod.snd c = N c
    rw [map_snd_restrict_prod_apply _ a hc.isOpen.measurableSet,
      clopenOperatorMeasure_measurable_clopen_prod S hS ha hc,
      hN c hc.isOpen.measurableSet]
  have heq : M = N := ext_of_generate_finite (clopenAlgebra Y)
    generateFrom_clopenAlgebra clopenAlgebra_isSetAlgebra.isSetRing.isSetSemiring.isPiSystem
    hsets (hsets univ isClopen_univ)
  have heq' := congrArg (fun R : Measure Y => R b) heq
  change ((clopenOperatorMeasure S hS).restrict (a ×ˢ univ)).map Prod.snd b = N b at heq'
  simpa only [map_snd_restrict_prod_apply _ a hb, hN b hb] using heq'

theorem clopenOperatorMeasure_unique
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (M : Measure (X × Y))
    (hM : ∀ (a : Set X) (b : Set Y) (ha : MeasurableSet a), MeasurableSet b →
      M (a ×ˢ b) = ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν)) :
    clopenOperatorMeasure S hS = M := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod S hS ha hb, hM a b ha hb]

theorem clopenOperatorMeasure_fst_le
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    (clopenOperatorMeasure S hS).map Prod.fst ≤ ENNReal.ofReal ‖S‖ • μ := by
  apply Measure.le_iff.mpr
  intro a ha
  have hval : (clopenOperatorMeasure S hS).map Prod.fst a =
      operatorRectangleContent S hS (b := univ) MeasurableSet.univ a := by
    rw [Measure.map_apply measurable_fst ha]
    have hpre : Prod.fst ⁻¹' a = a ×ˢ (univ : Set Y) := by ext z; simp
    rw [hpre, clopenOperatorMeasure_prod S hS ha MeasurableSet.univ]
    change _ = ENNReal.ofReal (operatorSetIntegral S (a ×ˢ univ))
    rw [operatorSetIntegral_prod S ha MeasurableSet.univ]
  rw [hval]
  exact operatorRectangleContent_le S hS MeasurableSet.univ ha

theorem clopenOperatorMeasure_fst_absolutelyContinuous
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    (clopenOperatorMeasure S hS).map Prod.fst ≪ μ :=
  Measure.absolutelyContinuous_of_le_smul (clopenOperatorMeasure_fst_le S hS)

theorem clopenOperatorMeasure_snd_eq
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    (clopenOperatorMeasure S hS).map Prod.snd =
      ν.withDensity (fun y => ENNReal.ofReal (S (lOneIndicator μ univ MeasurableSet.univ) y)) := by
  apply Measure.ext
  intro b hb
  rw [Measure.map_apply measurable_snd hb]
  have hpre : Prod.snd ⁻¹' b = (univ : Set X) ×ˢ b := by ext z; simp
  rw [hpre, clopenOperatorMeasure_prod S hS MeasurableSet.univ hb, withDensity_apply _ hb]
  exact ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _).integrableOn
    (ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (hS _ (lOneIndicator_nonneg univ MeasurableSet.univ))))

theorem clopenOperatorMeasure_snd_absolutelyContinuous
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    (clopenOperatorMeasure S hS).map Prod.snd ≪ ν := by
  rw [clopenOperatorMeasure_snd_eq S hS]
  exact withDensity_absolutelyContinuous _ _

theorem IsIntegralKernel.clopenOperatorMeasure_eq [SFinite ν]
    {k : X × Y → ℝ} {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k S) (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    clopenOperatorMeasure S hS = integralKernelMeasure μ ν k := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod S hS ha hb,
    ← hk.operatorContent_eq_kernelMeasure hS (prod_mem_finiteSectionAlgebra ha hb),
    operatorContent_apply, operatorSetIntegral_prod S ha hb]

end ThesisCommon
