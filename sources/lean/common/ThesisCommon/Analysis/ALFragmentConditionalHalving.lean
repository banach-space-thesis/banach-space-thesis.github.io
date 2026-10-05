import ThesisCommon.Analysis.ALFragmentConditionalMass
import ThesisCommon.Analysis.ALHomogeneousFullSupportSplit

/-! Conditional halving is constructed by choosing the smaller conditional
mass on a set in the generated subalgebra sigma algebra. The chosen fragment
retains the whole relative hull; no conditional nonatomicity assumption is
used. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
universe u
variable {E : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable {e : E} [Fact (0 ≤ e)]

/-- Select the smaller conditional half of a disjoint full-support partition. -/
theorem exists_conditional_half_of_partition_same_relativeHull
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (b u v : PositiveFragmentAlgebra e) (huv : u ⊔ v = b) (hd : Disjoint u v)
    (hu : alFragmentRelativeHull hAL S hS u = alFragmentRelativeHull hAL S hS b)
    (hv : alFragmentRelativeHull hAL S hS v = alFragmentRelativeHull hAL S hS b) :
    ∃ c : PositiveFragmentAlgebra e, c ≤ b ∧
      alFragmentRelativeHull hAL S hS c = alFragmentRelativeHull hAL S hS b ∧
      alFragmentConditionalMass hAL e S c ≤
        (1 / 2 : ℝ) • alFragmentConditionalMass hAL e S b := by
  let μ := alFragmentMeasure hAL e
  let fu := alFragmentConditionalMass hAL e S u
  let fv := alFragmentConditionalMass hAL e S v
  have hfu := alFragmentConditionalMass_aestronglyMeasurable hAL e S u
  have hfv := alFragmentConditionalMass_aestronglyMeasurable hAL e S v
  let gu := hfu.mk (fu : BooleanStonePoint (PositiveFragmentAlgebra e) → ℝ)
  let gv := hfv.mk (fv : BooleanStonePoint (PositiveFragmentAlgebra e) → ℝ)
  let A := {x | gu x ≤ gv x}
  have hA : MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] A :=
    measurableSet_le hfu.stronglyMeasurable_mk.measurable hfv.stronglyMeasurable_mk.measurable
  let hm := booleanSubalgebraStoneMeasurableSpace_le S
  let d := alMeasurableFragment hAL e A (hm A hA)
  have hdS : d ∈ S := alMeasurableFragment_mem_closed_subalgebra hAL e S hS A hA
  let c := (u ⊓ d) ⊔ (v ⊓ dᶜ)
  have hc : c ≤ b := by
    apply sup_le
    · exact inf_le_left.trans (le_sup_left.trans_eq huv)
    · exact inf_le_left.trans (le_sup_right.trans_eq huv)
  have hHc : alFragmentRelativeHull hAL S hS c = alFragmentRelativeHull hAL S hS b := by
    dsimp only [c]
    rw [booleanRelativeHull_sup S _ (alFragmentRelativeHull_spec hAL S hS),
      booleanRelativeHull_inf_of_mem S _ (alFragmentRelativeHull_spec hAL S hS) u hdS,
      booleanRelativeHull_inf_of_mem S _ (alFragmentRelativeHull_spec hAL S hS) v
        (S.compl_mem hdS), hu, hv, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  refine ⟨c, hc, hHc, ?_⟩
  have hmass : alFragmentConditionalMass hAL e S b = fu + fv := by
    rw [← huv, alFragmentConditionalMass_sup_of_disjoint hAL e S u v hd]
  have hcm : alFragmentConditionalMass hAL e S c =
      lpCut (booleanStoneSet d) (measurableSet_booleanStoneSet d) fu +
      lpCut (booleanStoneSet dᶜ) (measurableSet_booleanStoneSet dᶜ) fv := by
    dsimp only [c]
    rw [alFragmentConditionalMass_sup_of_disjoint hAL e S _ _
      (hd.mono inf_le_left inf_le_left),
      alFragmentConditionalMass_inf_of_mem hAL e S u d hdS,
      alFragmentConditionalMass_inf_of_mem hAL e S v dᶜ (S.compl_mem hdS)]
  rw [hcm, hmass]
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [hfu.ae_eq_mk, hfv.ae_eq_mk,
    alMeasurableFragment_stoneSet_ae hAL e A (hm A hA),
    lpCut_coe (booleanStoneSet d) (measurableSet_booleanStoneSet d) fu,
    lpCut_coe (booleanStoneSet dᶜ) (measurableSet_booleanStoneSet dᶜ) fv,
    Lp.coeFn_add (lpCut (booleanStoneSet d) (measurableSet_booleanStoneSet d) fu)
      (lpCut (booleanStoneSet dᶜ) (measurableSet_booleanStoneSet dᶜ) fv),
    Lp.coeFn_add fu fv, Lp.coeFn_smul (1 / 2 : ℝ) (fu + fv)] with x hgu hgv hdx hcutu hcutv hadd hsum hsmul
  change fu x = gu x at hgu
  change fv x = gv x at hgv
  change (x ∈ booleanStoneSet d) = (gu x ≤ gv x) at hdx
  rw [hadd, Pi.add_apply, hcutu, hcutv, hsmul, Pi.smul_apply, smul_eq_mul, hsum,
    Pi.add_apply]
  by_cases hxd : x ∈ booleanStoneSet d
  · have hle : fu x ≤ fv x := by simpa only [hgu, hgv] using hdx.mp hxd
    have hxn : x ∉ booleanStoneSet dᶜ := by
      simpa only [booleanStoneSet_compl, mem_compl_iff, not_not] using hxd
    rw [indicator_of_mem hxd, indicator_of_notMem hxn]
    linarith
  · have hle : fv x ≤ fu x := by
      have hnot : ¬ gu x ≤ gv x := fun hh => hxd (hdx.mpr hh)
      simpa only [hgu, hgv] using (not_le.mp hnot).le
    have hxc : x ∈ booleanStoneSet dᶜ := by simpa only [booleanStoneSet_compl, mem_compl_iff] using hxd
    rw [indicator_of_notMem hxd, indicator_of_mem hxc]
    linarith

/-- Every fragment of a homogeneous component admits a full-relative-support
subfragment with at most half its conditional mass. -/
theorem homogeneous_exists_conditional_half_same_relativeHull
    {a : PositiveFragmentAlgebra e} (ha : IsDensityHomogeneous a)
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (hden : topologicalDensity S < principalDensity a)
    (b : PositiveFragmentAlgebra e) (hba : b ≤ a) :
    ∃ c : PositiveFragmentAlgebra e, c ≤ b ∧
      alFragmentRelativeHull hAL S hS c = alFragmentRelativeHull hAL S hS b ∧
      alFragmentConditionalMass hAL e S c ≤
        (1 / 2 : ℝ) • alFragmentConditionalMass hAL e S b := by
  obtain ⟨u, v, huv, hd, hu, hv⟩ :=
    homogeneous_exists_partition_same_relativeHull hAL ha S hS hden b hba
  exact exists_conditional_half_of_partition_same_relativeHull hAL S hS b u v huv hd hu hv

theorem homogeneous_exists_nonzero_conditional_half
    {a : PositiveFragmentAlgebra e} (ha : IsDensityHomogeneous a)
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (hden : topologicalDensity S < principalDensity a)
    (b : PositiveFragmentAlgebra e) (hb : b ≠ ⊥) (hba : b ≤ a) :
    ∃ c : PositiveFragmentAlgebra e, c ≠ ⊥ ∧ c ≤ b ∧
      alFragmentRelativeHull hAL S hS c = alFragmentRelativeHull hAL S hS b ∧
      alFragmentConditionalMass hAL e S c ≤
        (1 / 2 : ℝ) • alFragmentConditionalMass hAL e S b := by
  obtain ⟨c, hcb, hcH, hc⟩ :=
    homogeneous_exists_conditional_half_same_relativeHull hAL ha S hS hden b hba
  refine ⟨c, ?_, hcb, hcH, hc⟩
  intro hz
  apply hb
  apply (booleanRelativeHull_eq_bot_iff S _ (alFragmentRelativeHull_spec hAL S hS) b).mp
  rw [← hcH, hz, booleanRelativeHull_bot S _ (alFragmentRelativeHull_spec hAL S hS)]

end ThesisCommon
