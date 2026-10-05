import ThesisCommon.Analysis.L1UniformTailCriterion
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-! Turn summably small biting sets into disjoint measurable annuli.
The discarded future cut tends to zero in L1, so the complementary sequence
retains uniform integrability. All scalar fields are real or complex. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem lOneCut_tendsto_zero_antitone_rclike
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (ha : Antitone A)
    (hz : μ (⋂ n, A n) = 0) (f : Lp 𝕜 1 μ) :
    Tendsto (fun n => ‖lpCut (A n) (hA n) f‖) atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_of_antitone hA ha
    (f := fun x => ‖f x‖) ⟨0, (L1.integrable_coeFn f).norm.integrableOn⟩
  simpa only [norm_lOneCut_eq_integral_rclike, Measure.restrict_eq_zero.mpr hz,
    integral_zero_measure] using ht

theorem exists_disjoint_lOne_biting_annuli
    (f : ℕ → Lp 𝕜 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hsum : (∑' n, μ (A n)) ≠ ∞)
    (hUI : UniformIntegrable (fun n => (lpCut (A n)ᶜ (hA n).compl (f n) : X → 𝕜)) 1 μ) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ B : ℕ → Set X,
      ∃ hB : ∀ n, MeasurableSet (B n), Pairwise (Disjoint on B) ∧
      UniformIntegrable (fun n => (lpCut (B n)ᶜ (hB n).compl (f (r n)) : X → 𝕜)) 1 μ := by
  let E : ℕ → Set X := fun n => ⋃ j ≥ n, A j
  have hE : ∀ n, MeasurableSet (E n) := fun n => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => hA j
  have hanti : Antitone E := by
    intro n m hnm x hx
    obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨j, hnm.trans hj, hx⟩
  have hAE (n : ℕ) : A n ⊆ E n := fun x hx => mem_iUnion₂.mpr ⟨n, le_rfl, hx⟩
  have hz : μ (⋂ n, E n) = 0 := by
    apply measure_mono_null (t := limsup A atTop) _ (measure_limsup_atTop_eq_zero hsum)
    simp only [limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
    exact Subset.rfl
  have hnext : ∀ n, ∃ m, n < m ∧ ‖lpCut (E m) (hE m) (f n)‖ < (2⁻¹ : ℝ) ^ n := by
    intro n
    have he := (lOneCut_tendsto_zero_antitone_rclike E hE hanti hz (f n)).eventually
      (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n))
    obtain ⟨m, hm⟩ := eventually_atTop.mp he
    exact ⟨max m (n + 1), lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _),
      hm _ (le_max_left _ _)⟩
  choose next hlt hsmall using hnext
  let r : ℕ → ℕ := fun n => next^[n] 0
  have hrs : ∀ n, r (n + 1) = next (r n) := fun n => iterate_succ_apply' next n 0
  have hr : StrictMono r := strictMono_nat_of_lt_succ fun n => by rw [hrs]; exact hlt _
  let B : ℕ → Set X := fun n => E (r n) \ E (r (n + 1))
  have hB : ∀ n, MeasurableSet (B n) := fun n => (hE _).diff (hE _)
  have hd : Pairwise (Disjoint on B) := by
    intro n m hnm
    wlog hnm' : n < m generalizing n m
    · exact (this hnm.symm (lt_of_le_of_ne (le_of_not_gt hnm') hnm.symm)).symm
    apply Set.disjoint_left.2
    intro x hxn hxm
    exact hxn.2 (hanti (hr.monotone (Nat.succ_le_of_lt hnm')) hxm.1)
  let u : ℕ → Lp 𝕜 1 μ := fun n => lpCut (E (r n))ᶜ (hE _).compl (f (r n))
  let v : ℕ → Lp 𝕜 1 μ := fun n => lpCut (E (r (n + 1))) (hE _) (f (r n))
  have hu : UniformIntegrable (fun n => (u n : X → 𝕜)) 1 μ := by
    apply UniformIntegrable.lOne_ae_norm_le (UniformIntegrable.lOne_comp hUI r)
    intro n
    filter_upwards [lpCut_coe (E (r n))ᶜ (hE _).compl (f (r n)),
      lpCut_coe (A (r n))ᶜ (hA _).compl (f (r n))] with x h1 h2
    change ‖lpCut (E (r n))ᶜ (hE _).compl (f (r n)) x‖ ≤ _
    rw [h1, h2]
    exact norm_indicator_le_of_subset (compl_subset_compl.mpr (hAE _)) _ x
  have hvsmall (n : ℕ) : ‖v n‖ ≤ (2⁻¹ : ℝ) ^ (r n) := by
    have h := (hsmall (r n)).le
    rwa [← hrs] at h
  have hvt : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hvsmall
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hr.tendsto_atTop)
  have hv : UnifIntegrable (fun n => (v n : X → 𝕜)) 1 μ := by
    apply unifIntegrable_of_tendsto_Lp_zero (by norm_num) (by norm_num) (fun n => Lp.memLp (v n))
    have ht := ENNReal.continuous_ofReal.tendsto 0 |>.comp hvt
    simpa only [Function.comp_def, ENNReal.ofReal_zero, ofReal_norm_eq_enorm, Lp.enorm_def] using ht
  have heq (n : ℕ) : u n + v n = lpCut (B n)ᶜ (hB n).compl (f (r n)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (u n) (v n),
      lpCut_coe (E (r n))ᶜ (hE _).compl (f (r n)),
      lpCut_coe (E (r (n + 1))) (hE _) (f (r n)),
      lpCut_coe (B n)ᶜ (hB n).compl (f (r n))] with x hs h1 h2 h3
    change u n x = _ at h1
    change v n x = _ at h2
    rw [hs, Pi.add_apply, h1, h2, h3]
    have hsub := hanti (hr.monotone (Nat.le_succ n))
    by_cases hxn : x ∈ E (r n) <;> by_cases hxm : x ∈ E (r (n + 1))
    · simp [B, hxn, hxm]
    · simp [B, hxn, hxm]
    · exact (hxn (hsub hxm)).elim
    · simp [B, hxn, hxm]
  refine ⟨r, hr, B, hB, hd, ?_⟩
  apply uniformIntegrable_lOne_of_unifIntegrable_norm_bounded _ ?_
    ((norm_nonneg (f 0)).trans (hf 0)) (fun n => (norm_lpCut_le _ _ _).trans (hf _))
  have hsumUI := hu.2.1.add hv (by norm_num) hu.1 (fun n => Lp.aestronglyMeasurable (v n))
  apply hsumUI.ae_eq
  intro n
  simpa only [Pi.add_apply, heq n] using (Lp.coeFn_add (u n) (v n)).symm

end ThesisCommon
