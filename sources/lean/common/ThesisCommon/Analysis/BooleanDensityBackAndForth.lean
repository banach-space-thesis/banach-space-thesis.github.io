import ThesisCommon.Analysis.BooleanBackAndForth
import ThesisCommon.Analysis.TopologicalDensity
import Mathlib.SetTheory.Cardinal.Ordinal

/-! Equal cardinal density provides the well-ordered dense enumerations
for the genuine partial-isometry recursion, also at countable density. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u

theorem cardinal_Iic_ord_toType_lt {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (i : κ.ord.toType) :
    #(Iic i) < κ := by
  rw [← Iio_insert]
  exact Cardinal.mk_insert_le.trans_lt
    (Cardinal.add_lt_of_lt hκ (Cardinal.mk_Iio_ord_toType i) (one_lt_aleph0.trans_le hκ))

theorem exists_dense_ordinal_enumeration {X : Type u} [TopologicalSpace X]
    {κ : Cardinal.{u}} (hX : topologicalDensity X = κ) :
    ∃ f : κ.ord.toType → X, DenseRange f := by
  obtain ⟨s, hs, hcard⟩ := exists_dense_card_eq_topologicalDensity X
  obtain ⟨e⟩ := Cardinal.eq.mp ((Cardinal.mk_ord_toType κ).trans (hcard.trans hX).symm)
  let f : κ.ord.toType → X := fun i => (e i).val
  refine ⟨f, ?_⟩
  have hf : range f = s := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  change Dense (range f)
  rwa [hf]

theorem exists_booleanIsometry_of_equal_density_and_small_extensions
    {A B : Type u} [BooleanAlgebra A] [BooleanAlgebra B]
    [MetricSpace A] [MetricSpace B] [CompleteSpace A] [CompleteSpace B]
    [ContinuousInf A] [ContinuousInf B]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hA : topologicalDensity A = κ) (hB : topologicalDensity B = κ)
    (p₀ : BooleanPartialIsometry A B) (hp₀ : (p₀.source : Set A).Finite)
    (extend : ∀ p : BooleanPartialIsometry A B, #p.source < κ → ∀ x : A, ∀ y : B,
      ∃ q : BooleanPartialIsometry A B, p ≤ q ∧ x ∈ q.source ∧ y ∈ q.target ∧
        #q.source ≤ #p.source * #p.source * #p.source * #p.source) :
    ∃ e : A ≃o B, Isometry e := by
  obtain ⟨a, ha⟩ := exists_dense_ordinal_enumeration hA
  obtain ⟨b, hb⟩ := exists_dense_ordinal_enumeration hB
  letI : Nonempty κ.ord.toType := Cardinal.mk_ne_zero_iff.mp
    (by rw [Cardinal.mk_ord_toType]; exact ne_of_gt (aleph0_pos.trans_le hκ))
  exact exists_booleanIsometry_of_small_extensions κ hκ (cardinal_Iic_ord_toType_lt hκ)
    a b ha hb p₀ hp₀ extend

end ThesisCommon
