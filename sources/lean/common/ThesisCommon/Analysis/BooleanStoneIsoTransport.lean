import ThesisCommon.Analysis.BooleanStoneMeasure
import ThesisCommon.Analysis.LebesgueLpTransport
import Mathlib.MeasureTheory.Function.LpOrder

/-! Actual Stone point maps induced by a Boolean order isomorphism.
Matching cylinder masses give a measure-preserving measurable equivalence
and hence an onto isometry of the genuine Lp spaces. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace ThesisCommon
variable {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]

def booleanStoneOrderMap (e : A ≃o B) (p : BooleanStonePoint B) : BooleanStonePoint A :=
  ⟨fun a => booleanStoneHom p (e a), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro a b; simp
    · intro a b; simp⟩

theorem booleanStoneOrderMap_apply (e : A ≃o B) (p : BooleanStonePoint B) (a : A) :
    booleanStoneHom (booleanStoneOrderMap e p) a = booleanStoneHom p (e a) := rfl

theorem booleanStoneOrderMap_preimage (e : A ≃o B) (a : A) :
    booleanStoneOrderMap e ⁻¹' booleanStoneSet a = booleanStoneSet (e a) := rfl

theorem measurable_booleanStoneOrderMap (e : A ≃o B) : Measurable (booleanStoneOrderMap e) := by
  apply measurable_generateFrom
  rintro _ ⟨a,rfl⟩
  exact measurableSet_booleanStoneSet (e a)

def booleanStoneOrderEquiv (e : A ≃o B) : BooleanStonePoint B ≃ BooleanStonePoint A where
  toFun := booleanStoneOrderMap e
  invFun := booleanStoneOrderMap e.symm
  left_inv p := by
    apply Subtype.ext
    funext b
    change booleanStoneHom p (e (e.symm b)) = booleanStoneHom p b
    rw [e.apply_symm_apply]
  right_inv p := by
    apply Subtype.ext
    funext a
    change booleanStoneHom p (e.symm (e a)) = booleanStoneHom p a
    rw [e.symm_apply_apply]

def booleanStoneMeasurableEquiv (e : A ≃o B) : BooleanStonePoint B ≃ᵐ BooleanStonePoint A where
  toEquiv := booleanStoneOrderEquiv e
  measurable_toFun := measurable_booleanStoneOrderMap e
  measurable_invFun := measurable_booleanStoneOrderMap e.symm

theorem measurePreserving_booleanStoneOrderMap (e : A ≃o B)
    (μ : Measure (BooleanStonePoint A)) (ν : Measure (BooleanStonePoint B)) [IsFiniteMeasure ν]
    (h : ∀ a, ν (booleanStoneSet (e a)) = μ (booleanStoneSet a)) :
    MeasurePreserving (booleanStoneMeasurableEquiv e) ν μ := by
  refine ⟨measurable_booleanStoneOrderMap e, ?_⟩
  change ν.map (booleanStoneOrderMap e) = μ
  apply ext_of_generate_finite (booleanStoneAlgebra A) rfl
    booleanStoneAlgebra_isSetAlgebra.isSetRing.isSetSemiring.isPiSystem
  · rintro _ ⟨a,rfl⟩
    rw [Measure.map_apply (measurable_booleanStoneOrderMap e) (measurableSet_booleanStoneSet a)]
    exact h a
  · rw [Measure.map_apply (measurable_booleanStoneOrderMap e) MeasurableSet.univ, preimage_univ]
    simpa only [map_top, booleanStoneSet_top] using h ⊤

def booleanStoneLpEquiv {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : A ≃o B)
    (μ : Measure (BooleanStonePoint A)) (ν : Measure (BooleanStonePoint B)) [IsFiniteMeasure ν]
    (h : ∀ a, ν (booleanStoneSet (e a)) = μ (booleanStoneSet a)) :
    Lp V p μ ≃ₗᵢ[𝕜] Lp V p ν :=
  lebesgueLpTransport (booleanStoneMeasurableEquiv e) (measurePreserving_booleanStoneOrderMap e μ ν h)

theorem booleanStoneLpEquiv_coe {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : A ≃o B)
    (μ : Measure (BooleanStonePoint A)) (ν : Measure (BooleanStonePoint B)) [IsFiniteMeasure ν]
    (h : ∀ a, ν (booleanStoneSet (e a)) = μ (booleanStoneSet a)) (f : Lp V p μ) :
    booleanStoneLpEquiv (𝕜 := 𝕜) e μ ν h f =ᵐ[ν] f ∘ booleanStoneOrderMap e :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_booleanStoneOrderMap e μ ν h)

theorem booleanStoneLpEquiv_nonneg {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : A ≃o B)
    (μ : Measure (BooleanStonePoint A)) (ν : Measure (BooleanStonePoint B)) [IsFiniteMeasure ν]
    (h : ∀ a, ν (booleanStoneSet (e a)) = μ (booleanStoneSet a)) (f : Lp ℝ p μ) :
    0 ≤ booleanStoneLpEquiv (𝕜 := ℝ) e μ ν h f ↔ 0 ≤ f := by
  rw [← Lp.coeFn_nonneg, ← Lp.coeFn_nonneg]
  change (∀ᵐ x ∂ν, 0 ≤ (booleanStoneLpEquiv (𝕜 := ℝ) e μ ν h f) x) ↔ ∀ᵐ y ∂μ, 0 ≤ f y
  have hp := measurePreserving_booleanStoneOrderMap e μ ν h
  have hae : (∀ᵐ y ∂μ, 0 ≤ f y) ↔ ∀ᵐ x ∂ν, 0 ≤ f (booleanStoneOrderMap e x) := by
    have hs : MeasurableSet {y : BooleanStonePoint A | 0 ≤ f y} :=
      measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable
    have ht := ae_map_iff (μ := ν) hp.measurable.aemeasurable hs
    simpa only [hp.map_eq] using ht
  rw [hae]
  apply Filter.eventually_congr
  filter_upwards [booleanStoneLpEquiv_coe (𝕜 := ℝ) e μ ν h f] with x hx
  rw [hx]
  rfl

end ThesisCommon
