import ThesisCommon.Analysis.ALFragmentSubalgebraMeasurable
import ThesisCommon.Analysis.ALFragmentIndicatorLattice
import ThesisCommon.Analysis.MeasureAlgebra

/-! A closed fragment subalgebra is exactly the measure algebra of its
generated Stone sub-sigma algebra. The correspondence uses actual quotient
classes, including all null sets, and does not assume a point isomorphism. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon

theorem ae_eq_set_trim_iff {X : Type*} {m m₀ : MeasurableSpace X}
    (μ : @Measure X m₀) (hm : m ≤ m₀) {A B : Set X}
    (hA : MeasurableSet[m] A) (hB : MeasurableSet[m] B) :
    A =ᵐ[μ.trim hm] B ↔ A =ᵐ[μ] B := by
  rw [← measure_symmDiff_eq_zero_iff, ← measure_symmDiff_eq_zero_iff,
    trim_measurableSet_eq hm (hA.symmDiff hB)]

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

abbrev alSubalgebraMeasure (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :=
  (alFragmentMeasure hAL e).trim (booleanSubalgebraStoneMeasurableSpace_le S)

abbrev ALSubalgebraMeasureAlgebra (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :=
  @MeasureAlgebra _ (booleanSubalgebraStoneMeasurableSpace S) (alSubalgebraMeasure hAL e S)

def alSubalgebraClass (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (a : S) : ALSubalgebraMeasureAlgebra hAL e S :=
  @MeasureAlgebra.mk _ (booleanSubalgebraStoneMeasurableSpace S) (alSubalgebraMeasure hAL e S)
    (booleanStoneSet a.val) (measurableSet_booleanStoneSet_of_mem_subalgebra S a.property)

omit [CompleteSpace E] in
theorem alSubalgebraClass_injective (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    Function.Injective (alSubalgebraClass hAL e S) := by
  letI := booleanSubalgebraStoneMeasurableSpace S
  intro a b hab
  apply Subtype.ext
  apply alFragment_eq_of_stoneSet_ae hAL e
  exact ae_of_ae_trim (booleanSubalgebraStoneMeasurableSpace_le S)
    ((MeasureAlgebra.mk_eq_mk _ _).mp hab)

theorem alSubalgebraClass_surjective (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e))) :
    Function.Surjective (alSubalgebraClass hAL e S) := by
  letI := booleanSubalgebraStoneMeasurableSpace S
  intro c
  let A := c.representative.val
  have hA : MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] A := c.representative.property
  let hm := booleanSubalgebraStoneMeasurableSpace_le S
  let a := alMeasurableFragment hAL e A (hm A hA)
  have ha : a ∈ S := alMeasurableFragment_mem_closed_subalgebra hAL e S hS A hA
  refine ⟨⟨a, ha⟩, ?_⟩
  change MeasureAlgebra.mk _ (booleanStoneSet a) _ = c
  rw [← MeasureAlgebra.mk_representative c]
  apply (MeasureAlgebra.mk_eq_mk _ _).mpr
  apply (ae_eq_set_trim_iff _ hm (measurableSet_booleanStoneSet_of_mem_subalgebra S ha) hA).mpr
  exact alMeasurableFragment_stoneSet_ae hAL e A (hm A hA)

def alSubalgebraMeasureAlgebraEquiv
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e))) :
    S ≃ ALSubalgebraMeasureAlgebra hAL e S :=
  Equiv.ofBijective (alSubalgebraClass hAL e S)
    ⟨alSubalgebraClass_injective hAL e S, alSubalgebraClass_surjective hAL e S hS⟩

omit [HasSolidNorm E] [CompleteSpace E] in
theorem alSubalgebraClass_compl (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) (a : S) :
    alSubalgebraClass hAL e S aᶜ = @MeasureAlgebra.compl _ (booleanSubalgebraStoneMeasurableSpace S)
      (alSubalgebraMeasure hAL e S) (alSubalgebraClass hAL e S a) := by
  letI := booleanSubalgebraStoneMeasurableSpace S
  unfold alSubalgebraClass
  rw [MeasureAlgebra.compl_mk]
  apply (MeasureAlgebra.mk_eq_mk _ _).mpr
  exact Filter.Eventually.of_forall (fun x => congrArg (fun A : Set _ => x ∈ A)
    (booleanStoneSet_compl a.val))

omit [HasSolidNorm E] [CompleteSpace E] in
theorem measure_alSubalgebraClass (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) (a : S) :
    @MeasureAlgebra.measure _ (booleanSubalgebraStoneMeasurableSpace S)
      (alSubalgebraMeasure hAL e S) (alSubalgebraClass hAL e S a) =
        ENNReal.ofReal ‖positiveFragmentValue a.val‖ := by
  letI := booleanSubalgebraStoneMeasurableSpace S
  change (alSubalgebraMeasure hAL e S) (booleanStoneSet a.val) = _
  rw [trim_measurableSet_eq _ (measurableSet_booleanStoneSet_of_mem_subalgebra S a.property),
    alFragmentMeasure_apply]

omit [CompleteSpace E] in
theorem alFragment_le_iff_stoneSet_ae (a b : PositiveFragmentAlgebra e) :
    a ≤ b ↔ ∀ᵐ x ∂alFragmentMeasure hAL e, x ∈ booleanStoneSet a → x ∈ booleanStoneSet b := by
  rw [← alFragmentIndicator_le_iff hAL e]
  constructor
  · intro hab
    filter_upwards [(Lp.coeFn_le _ _).mpr hab, alFragmentIndicator_coe hAL e a,
      alFragmentIndicator_coe hAL e b] with x hx ha hb
    rw [ha, hb] at hx
    intro hxa
    by_contra hxb
    norm_num [hxa, hxb] at hx
  · intro hab
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hab, alFragmentIndicator_coe hAL e a,
      alFragmentIndicator_coe hAL e b] with x hx ha hb
    rw [ha, hb]
    by_cases hxa : x ∈ booleanStoneSet a
    · simp [hxa, hx hxa]
    · simp [hxa]
      exact indicator_nonneg (fun _ _ => zero_le_one) x

theorem alSubalgebraClass_iUnion_iff_isLUB
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    {ι : Type*} [Countable ι] (a : ι → S) (b : S) :
    alSubalgebraClass hAL e S b =
      @MeasureAlgebra.iUnion _ (booleanSubalgebraStoneMeasurableSpace S)
        (alSubalgebraMeasure hAL e S) ι _ (fun i => alSubalgebraClass hAL e S (a i)) ↔
      IsLUB (Set.range a) b := by
  letI := booleanSubalgebraStoneMeasurableSpace S
  have hforward : ∀ b : S, alSubalgebraClass hAL e S b =
      MeasureAlgebra.iUnion (fun i => alSubalgebraClass hAL e S (a i)) →
        IsLUB (Set.range a) b := by
    intro b hb
    have heq : booleanStoneSet b.val =ᵐ[alFragmentMeasure hAL e]
        ⋃ i, booleanStoneSet (a i).val := by
      apply ae_of_ae_trim (booleanSubalgebraStoneMeasurableSpace_le S)
      apply (MeasureAlgebra.mk_eq_mk _ _).mp
      simpa only [alSubalgebraClass, MeasureAlgebra.iUnion_mk] using hb
    constructor
    · rintro _ ⟨i, rfl⟩
      apply (alFragment_le_iff_stoneSet_ae hAL e _ _).mpr
      filter_upwards [heq] with x hx
      intro hxa
      exact hx.mpr (Set.mem_iUnion.mpr ⟨i, hxa⟩)
    · intro c hc
      have hc' : ∀ i, ∀ᵐ x ∂alFragmentMeasure hAL e,
          x ∈ booleanStoneSet (a i).val → x ∈ booleanStoneSet c.val := fun i =>
        (alFragment_le_iff_stoneSet_ae hAL e _ _).mp (hc (Set.mem_range_self i))
      apply (alFragment_le_iff_stoneSet_ae hAL e _ _).mpr
      filter_upwards [heq, ae_all_iff.mpr hc'] with x hx hc''
      intro hxb
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hx.mp hxb)
      exact hc'' i hi
  constructor
  · exact hforward b
  · intro hb
    obtain ⟨c, hc⟩ := alSubalgebraClass_surjective hAL e S hS
      (MeasureAlgebra.iUnion (fun i => alSubalgebraClass hAL e S (a i)))
    have heq : b = c := hb.unique (hforward c hc)
    simpa only [heq] using hc

end ThesisCommon

