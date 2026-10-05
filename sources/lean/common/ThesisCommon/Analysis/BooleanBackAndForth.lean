import ThesisCommon.Analysis.BooleanPartialIsometryCardinality
import ThesisCommon.Analysis.WellOrderCoherentConstruction
import Mathlib.Order.Interval.Set.Basic

/-! Dense back-and-forth along a well-order.  The small-algebra extension
premise is explicit.  Finite stages remain finite, including at density aleph-zero. -/
noncomputable section
open Set Cardinal
open scoped Classical
namespace ThesisCommon
universe u
variable {A B I : Type u} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B] [LinearOrder I] [WellFoundedLT I]
open BooleanPartialIsometry

def BooleanStageSize (i : I) (p : BooleanPartialIsometry A B) : Prop :=
  #p.source ≤ max ℵ₀ #(Iic i) ∧ ((Iic i).Finite → (p.source : Set A).Finite)

theorem booleanStageSize_small {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    {i : I} (hi : #(Iic i) < κ) {p : BooleanPartialIsometry A B}
    (hp : BooleanStageSize i p) : #p.source < κ := by
  rcases eq_or_lt_of_le hκ with heq | hlt
  · rw [← heq] at hi ⊢
    exact Cardinal.lt_aleph0_iff_set_finite.mpr
      (hp.2 (Cardinal.lt_aleph0_iff_set_finite.mp hi))
  · exact hp.1.trans_lt (max_lt hlt hi)

theorem booleanStageSize_of_cardinal_le_fourth {i : I}
    {p q : BooleanPartialIsometry A B} (hp : BooleanStageSize i p)
    (hq : #q.source ≤ #p.source * #p.source * #p.source * #p.source) :
    BooleanStageSize i q := by
  constructor
  · have hC : ℵ₀ ≤ max ℵ₀ #(Iic i) := le_max_left _ _
    calc
      #q.source ≤ #p.source * #p.source * #p.source * #p.source := hq
      _ ≤ max ℵ₀ #(Iic i) * max ℵ₀ #(Iic i) * max ℵ₀ #(Iic i) * max ℵ₀ #(Iic i) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' hp.1 hp.1) hp.1) hp.1
      _ = max ℵ₀ #(Iic i) := by simp only [Cardinal.mul_eq_self hC]
  · intro hi
    have hpf : #p.source < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr (hp.2 hi)
    exact Cardinal.lt_aleph0_iff_set_finite.mp
      (hq.trans_lt (Cardinal.mul_lt_aleph0 (Cardinal.mul_lt_aleph0
        (Cardinal.mul_lt_aleph0 hpf hpf) hpf) hpf))

theorem exists_booleanPast_upper
    (p₀ : BooleanPartialIsometry A B) (hp₀ : (p₀.source : Set A).Finite)
    (i : I) (f : ∀ j, j < i → BooleanPartialIsometry A B)
    (hf : CoherentPast BooleanStageSize i f) :
    ∃ p, BooleanStageSize i p ∧ ∀ j hj, f j hj ≤ p := by
  let g : Iio i → BooleanPartialIsometry A B := fun j => f j.val j.property
  have hg : Monotone g := by
    intro j k hjk
    rcases hjk.eq_or_lt with h | h
    · exact (congrArg g h).le
    · exact (hf k.val k.property).2 j.val j.property h
  let c := range g
  by_cases hc : c.Nonempty
  · let p := chainUnion c hc hg.isChain_range
    refine ⟨p, ⟨?_, ?_⟩, fun j hj => le_chainUnion c hc hg.isChain_range ⟨⟨j,hj⟩, rfl⟩⟩
    · apply cardinal_source_chainUnion_le c hc hg.isChain_range _ (le_max_left _ _)
      · exact Cardinal.mk_range_le.trans ((Cardinal.mk_le_mk_of_subset Iio_subset_Iic_self).trans
          (le_max_right _ _))
      · rintro q ⟨j, rfl⟩
        exact (hf j.val j.property).1.1.trans
          (max_le_max_left _ (Cardinal.mk_le_mk_of_subset
            (Iic_subset_Iic.mpr j.property.le)))
    · intro hi
      have hif : (Iio i).Finite := hi.subset Iio_subset_Iic_self
      letI := hif.fintype
      have hcf : c.Finite := Set.finite_range g
      apply source_chainUnion_finite c hc hg.isChain_range hcf
      rintro q ⟨j, rfl⟩
      exact (hf j.val j.property).1.2 (hi.subset (Iic_subset_Iic.mpr j.property.le))
  · refine ⟨p₀, ⟨?_, fun _ => hp₀⟩, ?_⟩
    · exact (Cardinal.lt_aleph0_iff_set_finite.mpr hp₀).le.trans (le_max_left _ _)
    · intro j hj
      exact False.elim (hc ⟨g ⟨j,hj⟩, ⟨⟨j,hj⟩, rfl⟩⟩)

theorem exists_booleanIsometry_of_small_extensions
    [CompleteSpace A] [CompleteSpace B] [ContinuousInf A] [ContinuousInf B] [Nonempty I]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hprefix : ∀ i : I, #(Iic i) < κ)
    (a : I → A) (b : I → B) (ha : DenseRange a) (hb : DenseRange b)
    (p₀ : BooleanPartialIsometry A B) (hp₀ : (p₀.source : Set A).Finite)
    (extend : ∀ p : BooleanPartialIsometry A B, #p.source < κ → ∀ x : A, ∀ y : B,
      ∃ q : BooleanPartialIsometry A B, p ≤ q ∧ x ∈ q.source ∧ y ∈ q.target ∧
        #q.source ≤ #p.source * #p.source * #p.source * #p.source) :
    ∃ e : A ≃o B, Isometry e := by
  let Good (i : I) (p : BooleanPartialIsometry A B) : Prop :=
    BooleanStageSize i p ∧ a i ∈ p.source ∧ b i ∈ p.target
  have step : ∀ i (f : ∀ j, j < i → BooleanPartialIsometry A B), CoherentPast Good i f →
      ∃ p, Good i p ∧ ∀ j hj, f j hj ≤ p := by
    intro i f hf
    have hsize : CoherentPast BooleanStageSize i f := by
      intro j hj
      exact ⟨(hf j hj).1.1, (hf j hj).2⟩
    obtain ⟨p, hp, hfp⟩ := exists_booleanPast_upper p₀ hp₀ i f hsize
    obtain ⟨q, hpq, haq, hbq, hq⟩ := extend p
      (booleanStageSize_small hκ (hprefix i) hp) (a i) (b i)
    exact ⟨q, ⟨booleanStageSize_of_cardinal_le_fourth hp hq, haq, hbq⟩,
      fun j hj => (hfp j hj).trans hpq⟩
  obtain ⟨f, hf, hgood⟩ := exists_coherent_wellOrder_family p₀ Good step
  let p := chainUnion (range f) (range_nonempty f) hf.isChain_range
  have hfp (i : I) : f i ≤ p := le_chainUnion _ _ _ ⟨i,rfl⟩
  have hsource : Dense (p.source : Set A) := by
    apply ha.mono
    rintro x ⟨i,rfl⟩
    exact source_mono (hfp i) (hgood i).2.1
  have htarget : Dense (p.target : Set B) := by
    apply hb.mono
    rintro y ⟨i,rfl⟩
    exact target_mono (hfp i) (hgood i).2.2
  obtain ⟨e, he, _⟩ := p.exists_global_extension hsource htarget
  exact ⟨e, he⟩

end ThesisCommon
