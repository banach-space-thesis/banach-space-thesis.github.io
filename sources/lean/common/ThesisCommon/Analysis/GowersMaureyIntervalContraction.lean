import ThesisCommon.Analysis.GowersMaureyImplicitNorm
import ThesisCommon.Analysis.GowersMaureyIntervalGeometry

/-! Bimonotonicity of the actual least-fixed-point norm. Each norming clause
preserves interval contraction, and the property is preserved under suprema.
This supplies the interval estimate used in the source's RIS arguments. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def IntervalContractive (p : Seminorm 𝕜 (C00 𝕜)) : Prop :=
  ∀ (E : Interval) (x : C00 𝕜), p (restrict E x) ≤ p x

theorem normTest_restrict_le (D : ConstructionData 𝕜) (p : BoundedSeminorm 𝕜)
    (hp : IntervalContractive p.val) {q : Seminorm 𝕜 (C00 𝕜)}
    (hq : NormTest D p.val q) (E : Interval) (x : C00 𝕜) :
    q (restrict E x) ≤ (normOperator D p).val x := by
  have hle : ∀ r, NormTest D p.val r → r ≤ (normOperator D p).val :=
    fun r hr => le_csSup (testSet_bddAbove D p.property.2) hr
  cases hq with
  | coordinate n =>
    change ‖restrict E x n‖ ≤ _
    rw [restrict_apply]
    split_ifs
    · exact hle _ (NormTest.coordinate n) x
    · simpa only [norm_zero] using apply_nonneg ((normOperator D p).val) x
  | average T =>
    calc
      intervalAverage p.val T (restrict E x) ≤ intervalAverage p.val T x := by
        rw [intervalAverage_apply, intervalAverage_apply]
        apply mul_le_mul_of_nonneg_left _ (inverseWeight T.count).property
        apply Finset.sum_le_sum
        intro i _
        rw [restrict_comm]
        exact hp E (restrict (T.interval i) x)
      _ ≤ _ := hle _ (NormTest.average T) x
  | special hk g hg F =>
    change ‖pairing (specialFunctional g) (restrict F (restrict E x))‖ ≤ _
    rw [restrict_restrict]
    exact hle _ (NormTest.special hk g hg (F.inter E)) x
  | spread m n =>
    change p.val (spread m n (restrict E x)) ≤ _
    rw [spread_restrict]
    exact (hp (E.spreadImage m n) (spread m n x)).trans
      (hle _ (NormTest.spread m n) x)

theorem intervalContractive_normOperator (D : ConstructionData 𝕜)
    (p : BoundedSeminorm 𝕜) (hp : IntervalContractive p.val) :
    IntervalContractive (normOperator D p).val := by
  intro E x
  change (sSup (testSet D p.val)) (restrict E x) ≤ _
  rw [Seminorm.sSup_apply (testSet_bddAbove D p.property.2)]
  letI : Nonempty (testSet D p.val) := (testSet_nonempty D p.val).to_subtype
  apply ciSup_le
  intro q
  exact normTest_restrict_le D p hp q.property E x

theorem intervalContractive_sSup (s : Set (BoundedSeminorm 𝕜))
    (hs : ∀ p ∈ s, IntervalContractive p.val) : IntervalContractive (sSup s).val := by
  classical
  by_cases hne : s.Nonempty
  · intro E x
    have hb : BddAbove (Subtype.val '' s : Set (Seminorm 𝕜 (C00 𝕜))) := by
      refine ⟨mass, ?_⟩
      rintro _ ⟨p, _, rfl⟩
      exact p.property.2
    rw [Set.Icc.coe_sSup (show (0 : Seminorm 𝕜 (C00 𝕜)) ≤ mass from bot_le) hne]
    rw [Seminorm.sSup_apply hb]
    letI : Nonempty (Subtype.val '' s : Set (Seminorm 𝕜 (C00 𝕜))) :=
      (hne.image Subtype.val).to_subtype
    apply ciSup_le
    intro q
    obtain ⟨p, hp, heq⟩ := q.property
    change q.val (restrict E x) ≤ _
    rw [← heq]
    exact (hs p hp E x).trans
      (le_csSup hb (show p.val ∈ Subtype.val '' s from ⟨p, hp, rfl⟩) x)
  · have hz : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst s
    intro E x
    rw [sSup_empty]
    change (0 : Seminorm 𝕜 (C00 𝕜)) (restrict E x) ≤ 0
    simp

theorem implicitNorm_intervalContractive (D : ConstructionData 𝕜) :
    IntervalContractive (implicitNorm D) := by
  apply (normOperator D).lfp_induction
    (p := fun p : BoundedSeminorm 𝕜 => IntervalContractive p.val)
  · intro p hp _
    exact intervalContractive_normOperator D p hp
  · exact intervalContractive_sSup

theorem implicitNorm_restrict_le (D : ConstructionData 𝕜) (E : Interval) (x : C00 𝕜) :
    implicitNorm D (restrict E x) ≤ implicitNorm D x :=
  implicitNorm_intervalContractive D E x

end ThesisCommon.GowersMaurey
