import ThesisCommon.Analysis.GowersMaureyCodePrefixes

/-! Exact exceptional-code counts for the literal special-sequence definition.
No monotonicity or lower-size condition is assumed for the coding injection.
Nonempty-prefix collisions recover their positions and earlier functionals;
the distinguished initial size is counted separately. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def specialSequenceSize (D : ConstructionData 𝕜) {k : ℕ}
    (g : Fin k → C00 𝕜) (i : Fin k) : ℕ :=
  if i.val = 0 then D.j (2*k-1) else D.sigma (initialSegment g i)

theorem SpecialSequence.size_averaged {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (i : Fin k) :
    AveragedFunctional p (specialSequenceSize D g i) (g i) := hg.2.2 i

theorem SpecialSequence.noninitial_size_collision {D : ConstructionData 𝕜}
    {p q : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g h : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (hh : SpecialSequence D q h) (i j : Fin k)
    (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (he : specialSequenceSize D g i = specialSequenceSize D h j) :
    i = j ∧ ∀ t : Fin k, t < i → g t = h t := by
  apply hg.code_prefix_eq_imp_prefix hh i j
  simpa only [specialSequenceSize,if_neg hi,if_neg hj] using he

theorem SpecialSequence.low_prefix_code_count {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (t : ℕ) :
    (Finset.univ.filter (fun i => D.sigma (initialSegment g i) < D.j (2*t+1))).card ≤ t := by
  classical
  choose n hn using hg.code_prefix_is_odd_size
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun i => D.sigma (initialSegment g i) < D.j (2*t+1))) (t := Finset.range t) n
    (fun i hi => ?_) (fun i _ j _ hij => ?_)
  · simpa using h
  · have hh := (Finset.mem_filter.mp hi).2
    rw [hn i] at hh
    have hnt := D.j_strict.lt_iff_lt.mp hh
    exact Finset.mem_range.mpr (by omega)
  · apply hg.code_prefix_injective
    change D.sigma (initialSegment g i) = D.sigma (initialSegment g j)
    rw [hn i,hn j,hij]

theorem SpecialSequence.low_size_count {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (t : ℕ) :
    (Finset.univ.filter (fun i => specialSequenceSize D g i < D.j (2*t+1))).card ≤ t+1 := by
  classical
  let s := Finset.univ.filter (fun i : Fin k => i.val = 0)
  let a := Finset.univ.filter (fun i => D.sigma (initialSegment g i) < D.j (2*t+1))
  have hs : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    apply Fin.ext
    exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hsub : Finset.univ.filter (fun i => specialSequenceSize D g i < D.j (2*t+1)) ⊆
      a ∪ s := by
    intro i hi
    by_cases hiz : i.val = 0
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiz⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        simpa only [specialSequenceSize,if_neg hiz] using (Finset.mem_filter.mp hi).2⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le a s).trans
    (Nat.add_le_add (hg.low_prefix_code_count t) hs))

end ThesisCommon.GowersMaurey
