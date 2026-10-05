import ThesisCommon.Analysis.L1WeakUniformIntegrable
import Mathlib.MeasureTheory.Function.UnifTight

/-! Actual weakly compact subsets of real L1 are uniformly tight on an
arbitrary measure space. A failure of tightness produces disjoint finite
measure increments with uniformly positive mass, contradicting the
checked disjoint-cut consequence of Schur compactness. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lOneCut_exists_finite_measure (f : Lp ℝ 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set X, ∃ hA : MeasurableSet A, μ A < ∞ ∧ ‖lpCut Aᶜ hA.compl f‖ < ε := by
  obtain ⟨A, hA, hμA, hcut⟩ := (Lp.memLp f).exists_eLpNorm_indicator_compl_lt
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨A, hA, hμA, ?_⟩
  change ‖((Lp.memLp f).indicator hA.compl).toLp (Aᶜ.indicator f)‖ < ε
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_lt_toReal ((Lp.memLp f).indicator hA.compl).2.ne
    ENNReal.ofReal_ne_top).mpr hcut |>.trans_eq (ENNReal.toReal_ofReal hε.le)

theorem exists_disjoint_lOneCut_of_not_tight
    (K : Set (Lp ℝ 1 μ)) {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ A : Set X, ∀ hA : MeasurableSet A, μ A < ∞ →
      ∃ f ∈ K, ε < ‖lpCut Aᶜ hA.compl f‖) :
    ∃ A : ℕ → Set X, ∃ hA : ∀ n, MeasurableSet (A n),
      Pairwise (Disjoint on A) ∧ ∃ f : ℕ → Lp ℝ 1 μ,
        (∀ n, f n ∈ K) ∧ ∀ n, ε / 2 < ‖lpCut (A n) (hA n) (f n)‖ := by
  let F := {A : Set X // MeasurableSet A ∧ μ A < ∞}
  choose f hf hlarge using fun A : F => hbad A A.property.1 A.property.2
  choose B hB hμB hsmall using fun A : F =>
    lOneCut_exists_finite_measure (f A) (half_pos hε)
  let next : F → F := fun A => ⟨A ∪ B A, A.property.1.union (hB A),
    (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨A.property.2, hμB A⟩)⟩
  let r : ℕ → F := fun n => next^[n] ⟨∅, MeasurableSet.empty, by simp⟩
  let E : ℕ → Set X := fun n => r n
  have hE : ∀ n, MeasurableSet (E n) := fun n => (r n).property.1
  have hrs : ∀ n, r (n + 1) = next (r n) := fun n => iterate_succ_apply' next n _
  have hEs : ∀ n, E (n + 1) = E n ∪ B (r n) := fun n => by
    change (r (n + 1)).val = _
    rw [hrs]
  have hmono : Monotone E := monotone_nat_of_le_succ fun n => by
    rw [hEs]
    exact subset_union_left
  let A : ℕ → Set X := fun n => E (n + 1) \ E n
  have hA : ∀ n, MeasurableSet (A n) := fun n => (hE _).diff (hE _)
  have hd : Pairwise (Disjoint on A) := by
    intro n m hnm
    wlog hnm' : n < m generalizing n m
    · exact (this hnm.symm (lt_of_le_of_ne (le_of_not_gt hnm') hnm.symm)).symm
    apply Set.disjoint_left.2
    intro x hxn hxm
    exact hxm.2 (hmono (Nat.succ_le_of_lt hnm') hxn.1)
  refine ⟨A, hA, hd, fun n => f (r n), fun n => hf _, fun n => ?_⟩
  have hlarge' := hlarge (r n)
  have hsmall' : ‖lpCut (E (n + 1))ᶜ (hE _).compl (f (r n))‖ < ε / 2 := by
    apply lt_of_le_of_lt _ (hsmall (r n))
    rw [norm_lOneCut_eq_integral, norm_lOneCut_eq_integral]
    apply setIntegral_mono_set (L1.integrable_coeFn (f (r n))).norm.integrableOn
      (Eventually.of_forall fun x => norm_nonneg _) (Eventually.of_forall ?_)
    intro x hx hxB
    exact hx (by rw [hEs]; exact Or.inr hxB)
  have hdiff : A n = (E n)ᶜ \ (E (n + 1))ᶜ := by
    ext x
    simp only [A, mem_diff, mem_compl_iff, not_not]
    tauto
  rw [norm_lOneCut_eq_integral] at hlarge' hsmall' ⊢
  rw [hdiff, integral_diff (hE _).compl (L1.integrable_coeFn (f (r n))).norm.integrableOn
    (compl_subset_compl.mpr (hmono (Nat.le_succ n)))]
  change ε < ∫ x in (E n)ᶜ, ‖f (r n) x‖ ∂μ at hlarge'
  linarith

theorem isCompact_weakL1_uniform_tight
    {K : Set (WeakSpace ℝ (Lp ℝ 1 μ))} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set X, ∃ hA : MeasurableSet A, μ A < ∞ ∧
      ∀ f : Lp ℝ 1 μ, toWeakSpace ℝ (Lp ℝ 1 μ) f ∈ K →
        ‖lpCut Aᶜ hA.compl f‖ ≤ ε := by
  by_contra h
  push_neg at h
  obtain ⟨A, hA, hd, f, hf, hlower⟩ := exists_disjoint_lOneCut_of_not_tight
    {f | toWeakSpace ℝ (Lp ℝ 1 μ) f ∈ K} hε h
  have ht := weakCompact_lOne_disjointCut hK A hA hd f hf
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  exact (hlower n).not_ge hn.le

theorem IsWeaklyCompactOperator.exists_finite_measure_cut_compl_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E →L[ℝ] Lp ℝ 1 μ} (hT : IsWeaklyCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set X, ∃ hA : MeasurableSet A, μ A < ∞ ∧ ‖(lpCutL Aᶜ hA.compl).comp T‖ ≤ ε := by
  obtain ⟨K, hK, hTK⟩ := hT
  obtain ⟨A, hA, hμA, hcut⟩ := isCompact_weakL1_uniform_tight hK hε
  refine ⟨A, hA, hμA, ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  exact hcut (T x) (hTK x hx.le)

theorem isCompact_weakL1_unifTight
    {ι : Type*} (f : ι → Lp ℝ 1 μ)
    {K : Set (WeakSpace ℝ (Lp ℝ 1 μ))} (hK : IsCompact K)
    (hf : ∀ i, toWeakSpace ℝ (Lp ℝ 1 μ) (f i) ∈ K) :
    UnifTight (fun i x => f i x) 1 μ := by
  apply (unifTight_iff_real _ _ _).mpr
  intro ε hε
  obtain ⟨A, hA, hμA, hcut⟩ := isCompact_weakL1_uniform_tight hK hε
  refine ⟨A, hμA.ne, fun i => ?_⟩
  apply (ENNReal.toReal_le_toReal ((Lp.memLp (f i)).indicator hA.compl).2.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε.le]
  simpa only [lpCut, Lp.norm_toLp] using hcut (f i) (hf i)

end ThesisCommon
