import ThesisCommon.Analysis.L1DisjointCut
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-! Necessary Dunford--Pettis estimate for the genuine weak topology of real L1.
Failure of uniform absolute continuity produces disjoint annuli on which a
sequence retains positive L1 mass. Their norming functionals define a bounded
map into ell-one, contradicting weak compactness and the Schur theorem. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lOneCut_tendsto_zero_antitone
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (ha : Antitone A)
    (hz : μ (⋂ n, A n) = 0) (f : Lp ℝ 1 μ) :
    Tendsto (fun n => ‖lpCut (A n) (hA n) f‖) atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_of_antitone hA ha
    (f := fun x => ‖f x‖) ⟨0, (L1.integrable_coeFn f).norm.integrableOn⟩
  simpa only [norm_lOneCut_eq_integral, Measure.restrict_eq_zero.mpr hz,
    integral_zero_measure] using ht

theorem exists_disjoint_lOneCut_of_not_uniform
    (K : Set (Lp ℝ 1 μ)) {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ δ : ℝ, 0 < δ → ∃ f ∈ K, ∃ A : Set X, ∃ hA : MeasurableSet A,
      μ A ≤ ENNReal.ofReal δ ∧ ε < ‖lpCut A hA f‖) :
    ∃ A : ℕ → Set X, ∃ hA : ∀ n, MeasurableSet (A n),
      Pairwise (Disjoint on A) ∧ ∃ f : ℕ → Lp ℝ 1 μ,
        (∀ n, f n ∈ K) ∧ ∀ n, ε / 2 < ‖lpCut (A n) (hA n) (f n)‖ := by
  choose f hf B hB hμB hnorm using fun n : ℕ =>
    hbad ((2 : ℝ)⁻¹ ^ n) (pow_pos (by norm_num) n)
  have hsum : (∑' n, μ (B n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n)
    · simp
    · apply ENNReal.tsum_le_tsum
      intro n
      convert hμB n using 1
      simp [inv_pow, ENNReal.inv_pow]
  let E : ℕ → Set X := fun n => ⋃ j ≥ n, B j
  have hE : ∀ n, MeasurableSet (E n) := fun n => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => hB j
  have hanti : Antitone E := by
    intro n m hnm x hx
    obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨j, hnm.trans hj, hx⟩
  have hz : μ (⋂ n, E n) = 0 := by
    apply measure_mono_null (t := limsup B atTop) _ (measure_limsup_atTop_eq_zero hsum)
    simp only [limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
    exact Subset.rfl
  have hEnorm : ∀ n, ε < ‖lpCut (E n) (hE n) (f n)‖ := by
    intro n
    apply (hnorm n).trans_le
    rw [norm_lOneCut_eq_integral, norm_lOneCut_eq_integral]
    apply setIntegral_mono_set (L1.integrable_coeFn (f n)).norm.integrableOn
      (Eventually.of_forall fun x => norm_nonneg _) (Eventually.of_forall ?_)
    intro x hx
    exact mem_iUnion₂.mpr ⟨n, le_rfl, hx⟩
  have hnext : ∀ n, ∃ m, n < m ∧ ‖lpCut (E m) (hE m) (f n)‖ < ε / 2 := by
    intro n
    have he := (lOneCut_tendsto_zero_antitone E hE hanti hz (f n)).eventually
      (gt_mem_nhds (half_pos hε))
    obtain ⟨m, hm⟩ := eventually_atTop.mp he
    exact ⟨max m (n + 1), lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _),
      hm _ (le_max_left _ _)⟩
  choose next hlt hsmall using hnext
  let r : ℕ → ℕ := fun n => next^[n] 0
  have hrs : ∀ n, r (n + 1) = next (r n) := fun n => iterate_succ_apply' next n 0
  have hr : StrictMono r := strictMono_nat_of_lt_succ fun n => by rw [hrs]; exact hlt _
  let A : ℕ → Set X := fun n => E (r n) \ E (r (n + 1))
  have hA : ∀ n, MeasurableSet (A n) := fun n => (hE _).diff (hE _)
  have hd : Pairwise (Disjoint on A) := by
    intro n m hnm
    wlog hnm' : n < m generalizing n m
    · exact (this hnm.symm (lt_of_le_of_ne (le_of_not_gt hnm') hnm.symm)).symm
    apply Set.disjoint_left.2
    intro x hxn hxm
    exact hxn.2 (hanti (hr.monotone (Nat.succ_le_of_lt hnm')) hxm.1)
  refine ⟨A, hA, hd, fun n => f (r n), fun n => hf _, fun n => ?_⟩
  have hlarge := hEnorm (r n)
  have hsmall' := hsmall (r n)
  rw [← hrs] at hsmall'
  rw [norm_lOneCut_eq_integral] at hlarge hsmall' ⊢
  rw [show A n = E (r n) \ E (r (n + 1)) from rfl,
    integral_diff (hE _) (L1.integrable_coeFn (f (r n))).norm.integrableOn
      (hanti (hr.monotone (Nat.le_succ n)))]
  linarith

theorem isCompact_weakL1_uniform_cut
    {K : Set (WeakSpace ℝ (Lp ℝ 1 μ))} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : Lp ℝ 1 μ, toWeakSpace ℝ (Lp ℝ 1 μ) f ∈ K →
      ∀ A, ∀ hA : MeasurableSet A, μ A ≤ ENNReal.ofReal δ → ‖lpCut A hA f‖ ≤ ε := by
  by_contra h
  push_neg at h
  obtain ⟨A, hA, hd, f, hf, hlower⟩ := exists_disjoint_lOneCut_of_not_uniform
    {f | toWeakSpace ℝ (Lp ℝ 1 μ) f ∈ K} hε h
  have ht := weakCompact_lOne_disjointCut hK A hA hd f hf
  obtain ⟨n, hn⟩ := ((ht.eventually (gt_mem_nhds (half_pos hε)))).exists
  exact (hlower n).not_ge hn.le

theorem IsWeaklyCompactOperator.exists_small_cut_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E →L[ℝ] Lp ℝ 1 μ} (hT : IsWeaklyCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A, ∀ hA : MeasurableSet A,
      μ A ≤ ENNReal.ofReal δ → ‖(lpCutL A hA).comp T‖ ≤ ε := by
  obtain ⟨K, hK, hTK⟩ := hT
  obtain ⟨δ, hδ, hcut⟩ := isCompact_weakL1_uniform_cut hK hε
  refine ⟨δ, hδ, fun A hA hμA => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  exact hcut (T x) (hTK x hx.le) A hA hμA

theorem isCompact_weakL1_unifIntegrable
    {ι : Type*} (f : ι → Lp ℝ 1 μ)
    {K : Set (WeakSpace ℝ (Lp ℝ 1 μ))} (hK : IsCompact K)
    (hf : ∀ i, toWeakSpace ℝ (Lp ℝ 1 μ) (f i) ∈ K) :
    UnifIntegrable (fun i x => f i x) 1 μ := by
  intro ε hε
  obtain ⟨δ, hδ, hcut⟩ := isCompact_weakL1_uniform_cut hK hε
  refine ⟨δ, hδ, fun i A hA hμA => ?_⟩
  apply (ENNReal.toReal_le_toReal ((Lp.memLp (f i)).indicator hA).2.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε.le]
  simpa only [lpCut, Lp.norm_toLp] using hcut (f i) (hf i) A hA hμA

end ThesisCommon
