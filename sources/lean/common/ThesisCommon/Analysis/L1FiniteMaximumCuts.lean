import ThesisCommon.Analysis.L1FiniteMaximumMass
import ThesisCommon.Analysis.RCLikeL1DisjointCut

/-! Finite maximum mass is realized by genuinely measurable disjoint cuts.
The least maximizing index breaks ties, after choosing measurable representatives
of the L1 vectors. This is a finite disjointization statement, not a nested-tree
selection or an L1 factorization assumption. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped BigOperators
namespace ThesisCommon

theorem finiteMaxNorm_attained {E : Type*} [SeminormedAddCommGroup E]
    {n : ℕ} (hn : 0 < n) (a : ℕ → E) :
    ∃ j, j < n ∧ ‖a j‖ = finiteMaxNorm n a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : finiteMaxNorm n a ≤ ‖a n‖
    · exact ⟨n, Nat.lt_succ_self n, (max_eq_right h).symm⟩
    · have hn' : 0 < n := by
        by_contra hz
        have : n = 0 := by omega
        subst n
        exact h (norm_nonneg _)
      obtain ⟨j, hj, he⟩ := ih hn'
      exact ⟨j, Nat.lt_succ_of_lt hj, he.trans (max_eq_left (le_of_not_ge h)).symm⟩

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X]

theorem measurable_finiteMaxNorm (n : ℕ) (g : ℕ → X → 𝕜)
    (hg : ∀ j, Measurable (g j)) :
    Measurable (fun x => finiteMaxNorm n (fun j => g j x)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (hg n).norm

def finiteMaximumWinner (n i : ℕ) (g : ℕ → X → 𝕜) : Set X :=
  {x | ‖g i x‖ = finiteMaxNorm n (fun j => g j x) ∧
    ∀ j < i, ‖g j x‖ < finiteMaxNorm n (fun k => g k x)}

theorem measurableSet_finiteMaximumWinner (n i : ℕ) (g : ℕ → X → 𝕜)
    (hg : ∀ j, Measurable (g j)) : MeasurableSet (finiteMaximumWinner n i g) := by
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun (hg i).norm (measurable_finiteMaxNorm n g hg)
  · simpa only [← Set.setOf_forall] using
      (MeasurableSet.iInter (fun j : ℕ => MeasurableSet.iInter (fun _ : j < i =>
        measurableSet_lt (hg j).norm (measurable_finiteMaxNorm n g hg))))

omit [MeasurableSpace X] in
theorem finiteMaximumWinner_pairwise (n : ℕ) (g : ℕ → X → 𝕜) :
    Pairwise (Disjoint on (fun i : Fin n => finiteMaximumWinner n i g)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (ne_of_lt (hj.2 i h)) hi.1
  · exact (ne_of_lt (hi.2 j h)) hj.1

omit [MeasurableSpace X] in
theorem exists_finiteMaximumWinner {n : ℕ} (hn : 0 < n) (g : ℕ → X → 𝕜) (x : X) :
    ∃ i : Fin n, x ∈ finiteMaximumWinner n i g := by
  have hex := finiteMaxNorm_attained hn (fun j => g j x)
  refine ⟨⟨Nat.find hex, (Nat.find_spec hex).1⟩, (Nat.find_spec hex).2, ?_⟩
  intro j hj
  apply lt_of_le_of_ne (norm_le_finiteMaxNorm _ (hj.trans (Nat.find_spec hex).1))
  intro he
  exact Nat.find_min hex hj ⟨hj.trans (Nat.find_spec hex).1, he⟩

omit [MeasurableSpace X] in
theorem sum_finiteMaximumWinner_indicator {n : ℕ} (hn : 0 < n)
    (g : ℕ → X → 𝕜) (x : X) :
    (∑ i : Fin n, (finiteMaximumWinner n i g).indicator (fun y => ‖g i y‖) x) =
      finiteMaxNorm n (fun j => g j x) := by
  classical
  obtain ⟨i, hi⟩ := exists_finiteMaximumWinner hn g x
  rw [Finset.sum_eq_single i]
  · rw [indicator_of_mem hi]
    exact hi.1
  · intro j _ hji
    exact indicator_of_notMem (fun hj =>
      Set.disjoint_left.mp (finiteMaximumWinner_pairwise n g hji) hj hi) _
  · simp

variable {μ : Measure X}

theorem sum_l1_disjoint_cuts_le_maximumMass (n : ℕ) (f : ℕ → Lp 𝕜 1 μ)
    (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) :
    (∑ i : Fin n, ‖lpCut (A i) (hA i) (f i)‖) ≤ l1FiniteMaximumMass n f := by
  classical
  simp_rw [norm_lOneCut_eq_integral_rclike, ← integral_indicator (hA _)]
  rw [← integral_finset_sum _ (fun (i : Fin n) _ =>
    (L1.integrable_coeFn (f i)).norm.indicator (hA i))]
  apply integral_mono
    (integrable_finset_sum _ (fun (i : Fin n) _ =>
      (L1.integrable_coeFn (f i)).norm.indicator (hA i)))
    (integrable_finiteMaxNorm n f)
  intro x
  dsimp only
  by_cases hex : ∃ i, x ∈ A i
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [indicator_of_mem hi]
      exact norm_le_finiteMaxNorm (fun j => f j x) i.isLt
    · intro j _ hji
      exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (hd hji) hj hi) _
    · simp
  · have hx (i : Fin n) : x ∉ A i := fun hi => hex ⟨i, hi⟩
    simp only [indicator_of_notMem (hx _), Finset.sum_const_zero]
    exact finiteMaxNorm_nonneg n _

theorem exists_l1FiniteMaximum_disjoint_cuts {n : ℕ} (hn : 0 < n)
    (f : ℕ → Lp 𝕜 1 μ) :
    ∃ (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i)),
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = Set.univ ∧
      (∑ i : Fin n, ‖lpCut (A i) (hA i) (f i)‖) = l1FiniteMaximumMass n f := by
  let hm (i : ℕ) := (L1.integrable_coeFn (f i)).aestronglyMeasurable
  let g (i : ℕ) : X → 𝕜 := (hm i).mk (f i)
  have hg (i : ℕ) : Measurable (g i) := (hm i).measurable_mk
  let A (i : Fin n) := finiteMaximumWinner n i g
  have hA (i : Fin n) : MeasurableSet (A i) := measurableSet_finiteMaximumWinner n i g hg
  refine ⟨A, hA, finiteMaximumWinner_pairwise n g, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := exists_finiteMaximumWinner hn g x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · simp_rw [norm_lOneCut_eq_integral_rclike, ← integral_indicator (hA _)]
    rw [← integral_finset_sum _ (fun (i : Fin n) _ =>
      (L1.integrable_coeFn (f i)).norm.indicator (hA i))]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (hm i).ae_eq_mk)] with x hx
    have hi (i : Fin n) : (A i).indicator (fun y => ‖f i y‖) x =
        (A i).indicator (fun y => ‖g i y‖) x := by
      by_cases hix : x ∈ A i <;> simp [hix, hx i, g]
    simpa only [hi, hx] using sum_finiteMaximumWinner_indicator hn g x

end ThesisCommon
