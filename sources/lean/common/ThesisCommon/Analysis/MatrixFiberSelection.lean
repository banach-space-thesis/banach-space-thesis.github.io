import ThesisCommon.Analysis.SchauderSelection

/-! A gliding-hump selection with a prescribed infinite fibre at each
stage. The stage is the cardinality of the finite history, so all tolerances
and the next fibre are determined before choosing the next index.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon

theorem matrix_fiber_selection (w : ℕ → ℕ → ℝ)
    (hrow : ∀ m, Tendsto (w m) atTop (𝓝 0))
    (hcol : ∀ m, Tendsto (fun n => w n m) atTop (𝓝 0))
    (M : ℕ → Set ℕ) (hM : ∀ k, (M k).Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ (∀ k, r k ∈ M k) ∧
      ∀ i j, i ≠ j → w (r i) (r j) < ε / (2 : ℝ) ^ (i + j + 3) := by
  classical
  let P : ℕ → Finset ℕ → Prop := fun n F => n ∈ M F.card ∧ ∀ m ∈ F,
    w m n < ε / (2 : ℝ) ^ (m + F.card + 3) ∧
    w n m < ε / (2 : ℝ) ^ (m + F.card + 3)
  have hnext : ∀ F : Finset ℕ, (∀ m ∈ F, m ∈ (Set.univ : Set ℕ)) →
      ∃ n ∈ (Set.univ : Set ℕ), (∀ m ∈ F, m < n) ∧ P n F := by
    intro F _
    have hev : ∀ᶠ n in atTop, ∀ m ∈ F, m < n ∧
        w m n < ε / (2 : ℝ) ^ (m + F.card + 3) ∧
        w n m < ε / (2 : ℝ) ^ (m + F.card + 3) := by
      apply (Filter.eventually_all_finset F).mpr
      intro m _
      have hp : 0 < ε / (2 : ℝ) ^ (m + F.card + 3) := by positivity
      exact (eventually_gt_atTop m).and
        (((hrow m).eventually (gt_mem_nhds hp)).and
          ((hcol m).eventually (gt_mem_nhds hp)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨n, hn, hNn⟩ := (hM F.card).exists_gt N
    exact ⟨n, Set.mem_univ _, fun m hm => (hN n hNn.le m hm).1,
      hn, fun m hm => (hN n hNn.le m hm).2⟩
  obtain ⟨r, hr, _, hP⟩ := increasing_finite_history Set.univ P hnext
  have hcard (k : ℕ) : ((Finset.range k).image r).card = k := by
    rw [Finset.card_image_of_injective _ hr.injective, Finset.card_range]
  have hpair (i j : ℕ) (hij : i < j) :
      w (r i) (r j) < ε / (2 : ℝ) ^ (i + j + 3) ∧
      w (r j) (r i) < ε / (2 : ℝ) ^ (i + j + 3) := by
    have hh := (hP j).2 (r i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩)
    change w (r i) (r j) < ε / (2 : ℝ) ^ (r i + ((Finset.range j).image r).card + 3) ∧
      w (r j) (r i) < ε / (2 : ℝ) ^ (r i + ((Finset.range j).image r).card + 3) at hh
    rw [hcard] at hh
    have hbound : ε / (2 : ℝ) ^ (r i + j + 3) ≤ ε / (2 : ℝ) ^ (i + j + 3) := by
      apply div_le_div_of_nonneg_left hε.le (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      have hi : i ≤ r i := hr.id_le i
      omega
    exact ⟨hh.1.trans_le hbound, hh.2.trans_le hbound⟩
  refine ⟨r, hr, ?_, ?_⟩
  · intro k
    simpa only [hcard] using (hP k).1
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (hpair i j hij).1
    · simpa only [Nat.add_comm j i] using (hpair j i hji).2

end ThesisCommon
