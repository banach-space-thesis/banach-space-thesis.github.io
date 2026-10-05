import ThesisCommon.Analysis.ALFragmentConditionalHalving
import ThesisCommon.Analysis.ALFragmentConditionalSupport
import ThesisCommon.Analysis.ConditionalHalvingIteration
import ThesisCommon.Analysis.ConditionalSmallIncrementTest

/-! Small conditional increments are constructed from actual relative halves.
The prescribed budget belongs to the generated sub-sigma algebra; no
divisibility of arbitrary ambient L1 functions is asserted. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

theorem homogeneous_exists_small_conditional_increment
    {a : PositiveFragmentAlgebra e} (ha : IsDensityHomogeneous a)
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (hden : topologicalDensity S < principalDensity a)
    (b : PositiveFragmentAlgebra e) (hba : b ≤ a)
    (g : Lp ℝ 1 (alFragmentMeasure hAL e))
    (hg : AEStronglyMeasurable[booleanSubalgebraStoneMeasurableSpace S]
      g (alFragmentMeasure hAL e))
    (hg0 : 0 ≤ g) (hgb : g ≤ alFragmentConditionalMass hAL e S b) (hgne : g ≠ 0) :
    ∃ z : PositiveFragmentAlgebra e, z ≠ ⊥ ∧ z ≤ b ∧
      alFragmentConditionalMass hAL e S z ≤ g := by
  let μ := alFragmentMeasure hAL e
  let M := alFragmentConditionalMass hAL e S
  obtain ⟨u, hu0, hunest, hub, huH, huM⟩ := exists_iterated_conditional_halves b
    (alFragmentRelativeHull hAL S hS) M (fun r hr =>
      homogeneous_exists_conditional_half_same_relativeHull hAL ha S hS hden r
        (hr.trans hba))
  have hfm (n : ℕ) := alFragmentConditionalMass_aestronglyMeasurable hAL e S (u n)
  have hqm := alFragmentConditionalMass_aestronglyMeasurable hAL e S b
  let f := fun n => (hfm n).mk (M (u n))
  let q := hqm.mk (M b)
  let h := hg.mk g
  have hbudget : ∀ᵐ x ∂μ, 0 ≤ h x ∧ h x ≤ q x := by
    filter_upwards [hg.ae_eq_mk, hqm.ae_eq_mk, (Lp.coeFn_nonneg g).mpr hg0,
      (Lp.coeFn_le g (M b)).mpr hgb] with x hx hqx hn hb
    change g x = h x at hx
    change M b x = q x at hqx
    simpa only [hx, hqx] using And.intro hn hb
  have hne : ¬ h =ᵐ[μ] 0 := by
    intro heq
    apply hgne
    apply Lp.ext
    filter_upwards [hg.ae_eq_mk, heq, Lp.coeFn_zero ℝ 1 μ] with x hx he hz
    change g x = h x at hx
    exact hx.trans (he.trans hz.symm)
  have hpos : ∀ n, ∀ᵐ x ∂μ, 0 < q x → 0 < f n x := by
    intro n
    filter_upwards [(hfm n).ae_eq_mk, hqm.ae_eq_mk,
      alFragmentConditionalMass_same_positive_support_of_relativeHull_eq
        hAL e S hS (u n) b (huH n)] with x hx hqx hp
    change M (u n) x = f n x at hx
    change M b x = q x at hqx
    change 0 < M (u n) x ↔ 0 < M b x at hp
    simpa only [hx, hqx] using hp.mpr
  have hbound : ∀ n, ∀ᵐ x ∂μ, f n x ≤ (1/2 : ℝ)^n * q x := by
    intro n
    filter_upwards [(hfm n).ae_eq_mk, hqm.ae_eq_mk,
      (Lp.coeFn_le _ _).mpr (huM n), Lp.coeFn_smul ((1/2 : ℝ)^n) (M b)]
      with x hx hqx hb hsm
    change M (u n) x = f n x at hx
    change M b x = q x at hqx
    simpa only [hsm, Pi.smul_apply, smul_eq_mul, hx, hqx] using hb
  obtain ⟨n, hn⟩ := exists_positive_measure_conditional_increment f q h hbudget hne hpos hbound
  let A := {x | 0 < f n x ∧ f n x ≤ h x}
  have hA : MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] A :=
    (measurableSet_lt measurable_const (hfm n).stronglyMeasurable_mk.measurable).inter
      (measurableSet_le (hfm n).stronglyMeasurable_mk.measurable hg.stronglyMeasurable_mk.measurable)
  let hm := booleanSubalgebraStoneMeasurableSpace_le S
  let d := alMeasurableFragment hAL e A (hm A hA)
  have hd : d ∈ S := alMeasurableFragment_mem_closed_subalgebra hAL e S hS A hA
  let z := u n ⊓ d
  have hcm : M z = lpCut (booleanStoneSet d) (measurableSet_booleanStoneSet d) (M (u n)) :=
    alFragmentConditionalMass_inf_of_mem hAL e S (u n) d hd
  have hzle : M z ≤ g := by
    rw [hcm]
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [lpCut_coe (booleanStoneSet d) (measurableSet_booleanStoneSet d) (M (u n)),
      alMeasurableFragment_stoneSet_ae hAL e A (hm A hA), (hfm n).ae_eq_mk,
      hg.ae_eq_mk, (Lp.coeFn_nonneg g).mpr hg0] with x hc hd' hx hgx hgn
    change M (u n) x = f n x at hx
    change g x = h x at hgx
    change (x ∈ booleanStoneSet d) = (x ∈ A) at hd'
    rw [hc]
    by_cases hxd : x ∈ booleanStoneSet d
    · rw [indicator_of_mem hxd, hx, hgx]
      exact (hd'.mp hxd).2
    · rw [indicator_of_notMem hxd]
      exact hgn
  refine ⟨z, ?_, inf_le_left.trans (hub n), hzle⟩
  intro hz
  have hmz : M z = 0 := (alFragmentConditionalMass_eq_zero_iff hAL e S z).mpr hz
  rw [hcm] at hmz
  have haez := (lpCut_eq_zero_iff_ae_zero_on _ _ _).mp hmz
  apply hn
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [haez, alMeasurableFragment_stoneSet_ae hAL e A (hm A hA),
    (hfm n).ae_eq_mk] with x hx hd' hfx
  change (x ∈ booleanStoneSet d) = (x ∈ A) at hd'
  change M (u n) x = f n x at hfx
  intro hxa
  exact hxa.1.ne' (hfx.symm.trans (hx (hd'.mpr hxa)))

end ThesisCommon

