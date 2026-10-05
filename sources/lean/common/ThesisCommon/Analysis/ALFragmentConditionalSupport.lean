import ThesisCommon.Analysis.ALFragmentConditionalMass

/-! The support of actual conditional mass is the least cover in the
closed Boolean subalgebra. The equality holds almost everywhere, without
assuming that conditional expectations have pointwise chosen supports. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon

theorem lpCut_eq_zero_iff_ae_zero_on
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : ENNReal} [Fact (1 ≤ p)] (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 p μ) :
    lpCut A hA f = 0 ↔ ∀ᵐ x ∂μ, x ∈ A → f x = 0 := by
  constructor
  · intro h
    have heq := Lp.ext_iff.mp h
    filter_upwards [heq, lpCut_coe A hA f, Lp.coeFn_zero 𝕜 p μ] with x hx hc hz
    intro hxa
    simpa only [hc, indicator_of_mem hxa, hz] using hx
  · intro h
    apply Lp.ext
    filter_upwards [h, lpCut_coe A hA f, Lp.coeFn_zero 𝕜 p μ] with x hx hc hz
    rw [hc, hz]
    by_cases hxa : x ∈ A <;> simp [hxa, hx]

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

theorem alFragmentConditionalMass_pos_iff_relativeHull
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e))) (a : PositiveFragmentAlgebra e) :
    ∀ᵐ x ∂alFragmentMeasure hAL e,
      0 < alFragmentConditionalMass hAL e S a x ↔
        x ∈ booleanStoneSet (alFragmentRelativeHull hAL S hS a) := by
  let μ := alFragmentMeasure hAL e
  let f := alFragmentConditionalMass hAL e S a
  let H := alFragmentRelativeHull hAL S hS a
  have hH : H ∈ S := (alFragmentRelativeHull_spec hAL S hS a).1
  have hf := alFragmentConditionalMass_aestronglyMeasurable hAL e S a
  let g := hf.mk (f : BooleanStonePoint (PositiveFragmentAlgebra e) → ℝ)
  let A := {x | 0 < g x}
  have hA : MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] A :=
    measurableSet_lt measurable_const hf.stronglyMeasurable_mk.measurable
  let hm := booleanSubalgebraStoneMeasurableSpace_le S
  let b := alMeasurableFragment hAL e A (hm A hA)
  have hb : b ∈ S := alMeasurableFragment_mem_closed_subalgebra hAL e S hS A hA
  have hpos : ∀ᵐ x ∂μ, 0 < f x ↔ x ∈ booleanStoneSet b := by
    filter_upwards [hf.ae_eq_mk, alMeasurableFragment_stoneSet_ae hAL e A (hm A hA)] with x hx hb'
    change (x ∈ booleanStoneSet b) = (0 < g x) at hb'
    change f x = g x at hx
    rw [hx, hb']
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x :=
    (Lp.coeFn_nonneg _).mpr (alFragmentConditionalMass_nonneg hAL e S a)
  have hcutb : lpCut (booleanStoneSet bᶜ) (measurableSet_booleanStoneSet bᶜ) f = 0 := by
    apply (lpCut_eq_zero_iff_ae_zero_on _ _ _).mpr
    filter_upwards [hpos, hnonneg] with x hx hn
    intro hxb
    have hnb : x ∉ booleanStoneSet b := by simpa only [booleanStoneSet_compl] using hxb
    exact le_antisymm (not_lt.mp (fun hp => hnb (hx.mp hp))) hn
  have hHb : H ≤ b := by
    apply disjoint_compl_right_iff.mp
    apply disjoint_iff.mpr
    exact (alFragmentConditionalMass_cut_eq_zero_iff_relativeHull hAL e S hS a bᶜ
      (S.compl_mem hb)).mp hcutb
  have hcutH : lpCut (booleanStoneSet Hᶜ) (measurableSet_booleanStoneSet Hᶜ) f = 0 := by
    apply (alFragmentConditionalMass_cut_eq_zero_iff_relativeHull hAL e S hS a Hᶜ
      (S.compl_mem hH)).mpr
    exact inf_compl_eq_bot
  have hz := (lpCut_eq_zero_iff_ae_zero_on _ _ _).mp hcutH
  have hbH : b ≤ H := by
    apply (alFragmentIndicator_le_iff hAL e b H).mp
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hpos, hz, alFragmentIndicator_coe hAL e b,
      alFragmentIndicator_coe hAL e H] with x hp hz' hib hiH
    rw [hib, hiH]
    by_cases hxb : x ∈ booleanStoneSet b
    · have hxH : x ∈ booleanStoneSet H := by
        by_contra hnH
        have hfx := hz' (by simpa only [booleanStoneSet_compl] using hnH)
        exact (hp.mpr hxb).ne' hfx
      simp [hxb, hxH]
    · simp [hxb]
      exact indicator_nonneg (fun _ _ => zero_le_one) x
  have heq : H = b := le_antisymm hHb hbH
  simpa only [← heq] using hpos

theorem alFragmentConditionalMass_zero_iff_not_mem_relativeHull
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e))) (a : PositiveFragmentAlgebra e) :
    ∀ᵐ x ∂alFragmentMeasure hAL e,
      alFragmentConditionalMass hAL e S a x = 0 ↔
        x ∉ booleanStoneSet (alFragmentRelativeHull hAL S hS a) := by
  filter_upwards [alFragmentConditionalMass_pos_iff_relativeHull hAL e S hS a,
    (Lp.coeFn_nonneg _).mpr (alFragmentConditionalMass_nonneg hAL e S a)] with x hp hn
  rw [← hp]
  exact ⟨fun h => by simp [h], fun h => le_antisymm (not_lt.mp h) hn⟩

theorem alFragmentConditionalMass_same_positive_support_of_relativeHull_eq
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a b : PositiveFragmentAlgebra e)
    (hab : alFragmentRelativeHull hAL S hS a = alFragmentRelativeHull hAL S hS b) :
    ∀ᵐ x ∂alFragmentMeasure hAL e,
      0 < alFragmentConditionalMass hAL e S a x ↔
        0 < alFragmentConditionalMass hAL e S b x := by
  filter_upwards [alFragmentConditionalMass_pos_iff_relativeHull hAL e S hS a,
    alFragmentConditionalMass_pos_iff_relativeHull hAL e S hS b] with x ha hb
  rw [ha, hb, hab]

theorem alFragmentConditionalMass_same_zero_set_of_relativeHull_eq
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a b : PositiveFragmentAlgebra e)
    (hab : alFragmentRelativeHull hAL S hS a = alFragmentRelativeHull hAL S hS b) :
    ∀ᵐ x ∂alFragmentMeasure hAL e,
      alFragmentConditionalMass hAL e S a x = 0 ↔
        alFragmentConditionalMass hAL e S b x = 0 := by
  filter_upwards [alFragmentConditionalMass_zero_iff_not_mem_relativeHull hAL e S hS a,
    alFragmentConditionalMass_zero_iff_not_mem_relativeHull hAL e S hS b] with x ha hb
  rw [ha, hb, hab]

end ThesisCommon
