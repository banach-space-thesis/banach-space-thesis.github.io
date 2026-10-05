import Posets.AcceptanceDichotomyFiniteBlocks

/-! A gliding hump whose selected output indices avoid every input block. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_disjoint_row_blocks (u : ℕ → lp (fun _ : ℕ => 𝕜) 1)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0))
    (k : ℕ → ℕ) (hk : StrictMono k)
    (hdiag : Tendsto (fun n => u n (k n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ B : ℕ → Finset ℕ,
      Pairwise (fun m n => Disjoint (B m) (B n)) ∧
      (∀ m n, k (r m) ∉ B n) ∧
      ∀ n, ‖u (r n) - ∑ i ∈ B n, lp.single 1 i (u (r n) i)‖ < ε := by
  choose F hF using fun n => ThesisCommon.scalar_ellOne_exists_finite_approx (u n)
    (by positivity : 0 < ε / 4)
  let G (H : Finset ℕ) := H.biUnion F ∪ H.image k
  have hsmall (H : Finset ℕ) : ∀ᶠ n in atTop, ∑ i ∈ G H, ‖u n i‖ < ε / 4 := by
    have ht : Tendsto (fun n => ∑ i ∈ G H, ‖u n i‖) atTop (𝓝 0) := by
      simpa only [norm_zero, Finset.sum_const_zero] using
        tendsto_finset_sum (G H) (fun i _ => (hu i).norm)
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hdsmall : ∀ᶠ n in atTop, ‖u n (k n)‖ < ε / 4 :=
    hdiag.norm.eventually (by simpa using gt_mem_nhds (by positivity : 0 < ε / 4))
  obtain ⟨r, hr, _, hpast⟩ := ThesisCommon.increasing_finite_history Set.univ
    (fun n H => (H.biUnion F).sup id < k n ∧
      (∑ i ∈ G H, ‖u n i‖) < ε / 4 ∧ ‖u n (k n)‖ < ε / 4) (by
      intro H _
      have hklarge : ∀ᶠ n in atTop, (H.biUnion F).sup id < k n :=
        hk.tendsto_atTop (eventually_gt_atTop _)
      obtain ⟨n, hn, hkn, hmass, hdiag'⟩ :=
        ((eventually_gt_atTop (H.sup id)).and (hklarge.and ((hsmall H).and hdsmall))).exists
      exact ⟨n, Set.mem_univ _, fun m hm => (Finset.le_sup (f := id) hm).trans_lt hn,
        hkn, hmass, hdiag'⟩)
  let H (n : ℕ) := (Finset.range n).image r
  let B (n : ℕ) := F (r n) \ insert (k (r n)) (G (H n))
  have hprior {m n : ℕ} (hmn : m < n) : r m ∈ H n :=
    Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmn, rfl⟩
  have hbefore {m n : ℕ} (hmn : m < n) : Disjoint (B m) (B n) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    apply (Finset.mem_sdiff.mp hj).2
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨r m, hprior hmn, (Finset.mem_sdiff.mp hi).1⟩
  refine ⟨r, hr, B, ?_, ?_, ?_⟩
  · intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hbefore h
    · exact (hbefore h).symm
  · intro m n hmem
    rcases lt_trichotomy m n with hmn | rfl | hnm
    · apply (Finset.mem_sdiff.mp hmem).2
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨r m, hprior hmn, rfl⟩))
    · exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_self _ _)
    · have hFmem : k (r m) ∈ (H m).biUnion F :=
        Finset.mem_biUnion.mpr ⟨r n, hprior hnm, (Finset.mem_sdiff.mp hmem).1⟩
      exact (not_lt_of_ge (Finset.le_sup (f := id) hFmem)) (hpast m).1
  · intro n
    have hsum : (∑ i ∈ insert (k (r n)) (G (H n)), ‖u (r n) i‖) ≤
        ‖u (r n) (k (r n))‖ + ∑ i ∈ G (H n), ‖u (r n) i‖ := by
      by_cases hn : k (r n) ∈ G (H n)
      · rw [Finset.insert_eq_of_mem hn]
        exact le_add_of_nonneg_left (norm_nonneg _)
      · rw [Finset.sum_insert hn]
    have htail := ThesisCommon.scalar_ellOne_norm_tail_sdiff_le (u (r n))
      (F (r n)) (insert (k (r n)) (G (H n)))
    have hs : (∑ i ∈ insert (k (r n)) (G (H n)), ‖u (r n) i‖) < ε / 2 :=
      hsum.trans_lt (by linarith only [(hpast n).2.1, (hpast n).2.2])
    convert htail.trans_lt ((add_lt_add (hF (r n)) hs).trans_le
      (by linarith only [hε] : ε / 4 + ε / 2 ≤ ε)) using 1
    congr 3
    · ext i
      simp [B]
    · ext i j
      by_cases h : i = j
      · subst j
        simp [lp.single_apply]
      · simp [lp.single_apply, Pi.single, Function.update, Ne.symm h]

end Posets
