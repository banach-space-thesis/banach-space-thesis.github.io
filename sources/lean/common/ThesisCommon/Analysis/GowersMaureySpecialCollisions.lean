import ThesisCommon.Analysis.GowersMaureySpecialCodeCounts

/-! Collision bookkeeping for literal special sequences. The constructed
sequence may have increasing sizes; the competing sequence is arbitrary.
There is at most one off-diagonal collision with the distinguished first size,
and a last diagonal collision recovers the common earlier prefix. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem SpecialSequence.size_is_odd {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (i : Fin k) :
    ∃ n, specialSequenceSize D g i = D.j (2*n+1) := by
  by_cases hi : i.val = 0
  · have hk : 0 < k := i.isLt.trans_le' (Nat.zero_le _)
    refine ⟨k-1,?_⟩
    simp only [specialSequenceSize,if_pos hi]
    congr 1
    omega
  · simpa only [specialSequenceSize,if_neg hi] using hg.code_prefix_is_odd_size i

theorem SpecialSequence.size_le_selected_count {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (t : ℕ) :
    (Finset.univ.filter (fun i => specialSequenceSize D g i ≤ D.j (2*t))).card ≤ t+1 := by
  classical
  apply (Finset.card_le_card (show Finset.univ.filter
      (fun i => specialSequenceSize D g i ≤ D.j (2*t)) ⊆
      Finset.univ.filter (fun i => specialSequenceSize D g i < D.j (2*t+1)) from ?_)).trans
    (hg.low_size_count t)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp hi).2.trans_lt (D.j_strict (by omega))⟩

theorem SpecialSequence.offDiagonal_collision_initial {D : ConstructionData 𝕜}
    {p q : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g h : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (hh : SpecialSequence D q h)
    (hmono : StrictMono (specialSequenceSize D g)) {i j : Fin k} (hij : i ≠ j)
    (he : specialSequenceSize D g i = specialSequenceSize D h j) :
    i.val = 0 ∧ j.val ≠ 0 := by
  have hj : j.val ≠ 0 := by
    intro hj
    apply hij
    apply hmono.injective
    exact he.trans (by simp only [specialSequenceSize,if_pos hj])
  refine ⟨?_,hj⟩
  by_contra hi
  exact hij (hg.noninitial_size_collision hh i j hi hj he).1

theorem SpecialSequence.offDiagonal_collision_count {D : ConstructionData 𝕜}
    {p q : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g h : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (hh : SpecialSequence D q h)
    (hmono : StrictMono (specialSequenceSize D g)) :
    (Finset.univ.filter (fun z : Fin k × Fin k => z.1 ≠ z.2 ∧
      specialSequenceSize D g z.1 = specialSequenceSize D h z.2)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro z hz w hw
  have hz' := (Finset.mem_filter.mp hz).2
  have hw' := (Finset.mem_filter.mp hw).2
  have hz0 := hg.offDiagonal_collision_initial hh hmono hz'.1 hz'.2
  have hw0 := hg.offDiagonal_collision_initial hh hmono hw'.1 hw'.2
  have hfirst : z.1 = w.1 := Fin.ext (hz0.1.trans hw0.1.symm)
  have he : specialSequenceSize D h z.2 = specialSequenceSize D h w.2 := by
    rw [← hz'.2,← hw'.2,hfirst]
  exact Prod.ext hfirst (hh.noninitial_size_collision hh z.2 w.2 hz0.2 hw0.2 he).1

theorem SpecialSequence.exists_last_diagonal_collision {D : ConstructionData 𝕜}
    {p q : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} (hk : 0 < k) {g h : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (hh : SpecialSequence D q h) :
    ∃ t : Fin k, specialSequenceSize D g t = specialSequenceSize D h t ∧
      (∀ i, t < i → specialSequenceSize D g i ≠ specialSequenceSize D h i) ∧
      ∀ i, i < t → g i = h i := by
  classical
  let s := Finset.univ.filter (fun i => specialSequenceSize D g i = specialSequenceSize D h i)
  have hs : s.Nonempty := ⟨⟨0,hk⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
    simp [specialSequenceSize]⟩⟩
  let t := s.max' hs
  have ht : t ∈ s := Finset.max'_mem _ _
  have he := (Finset.mem_filter.mp ht).2
  refine ⟨t,he,?_,?_⟩
  · intro i hi hie
    have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hie⟩
    exact (not_le_of_gt hi) (Finset.le_max' _ i his)
  · intro i hi
    have ht0 : t.val ≠ 0 := by have hil : i.val < t.val := hi; omega
    exact (hg.noninitial_size_collision hh t t ht0 ht0 he).2 i hi

end ThesisCommon.GowersMaurey
