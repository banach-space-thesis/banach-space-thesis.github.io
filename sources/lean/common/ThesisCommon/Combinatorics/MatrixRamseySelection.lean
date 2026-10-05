import ThesisCommon.Combinatorics.MatrixRamseyPatterns

/-! Successive finite Ramsey thinning and the complete off-diagonal case split. -/
noncomputable section
namespace ThesisCommon

theorem MatrixGoodSlices.mono {w : ℕ → ℕ → ℕ → ℕ → ℝ} {δ : ℝ} {m : ℕ}
    {S T : Set ℕ} (h : MatrixGoodSlices w δ m S) (hTS : T ⊆ S) :
    MatrixGoodSlices w δ m T :=
  ⟨fun j hj k hk l hl g hg => h.1 j (hTS hj) k (hTS hk) l (hTS hl) g (hg.trans hTS),
    fun i hi k hk l hl g hg => h.2 i (hTS hi) k (hTS hk) l (hTS hl) g (hg.trans hTS)⟩

theorem finite_matrix_pattern_selection (C : Type*) [Finite C] [Nonempty C] (m L : ℕ)
    (hL : m + 3 ≤ L) :
    ∃ N : ℕ, 0 < N ∧ ∀ A : Finset ℕ, N ≤ A.card →
      ∀ color : (Fin 2 ↪o ℕ) → C, ∀ w : ℕ → ℕ → ℕ → ℕ → ℝ, ∀ δ : ℝ,
      MatrixGoodSlices w δ m (A : Set ℕ) →
      ∃ S : Finset ℕ, S ⊆ A ∧ S.card = L ∧
        (∃ c : C, OrderedHomogeneous color (S : Set ℕ) c) ∧
        OrderedHomogeneous (matrixTripleBadColor w δ) (S : Set ℕ) (fun _ => false) ∧
        OrderedHomogeneous (matrixQuadrupleBadColor w δ) (S : Set ℕ) (fun _ => false) := by
  classical
  obtain ⟨N₄, hN₄, hR₄⟩ := finite_ordered_ramsey_in_finset (Fin 4 → Bool) 4 L
  obtain ⟨N₃, _, hR₃⟩ := finite_ordered_ramsey_in_finset (Fin 4 → Bool) 3 N₄
  obtain ⟨N₂, hN₂, hR₂⟩ := finite_ordered_ramsey_in_finset C 2 N₃
  refine ⟨N₂, hN₂, ?_⟩
  intro A hA color w δ hslices
  obtain ⟨S₂, hS₂, hc₂, c₂, hh₂⟩ := hR₂ A hA color
  obtain ⟨S₃, hS₃, hc₃, c₃, hh₃⟩ := hR₃ S₂ hc₂.ge (matrixTripleBadColor w δ)
  obtain ⟨S₄, hS₄, hc₄, c₄, hh₄⟩ := hR₄ S₃ hc₃.ge (matrixQuadrupleBadColor w δ)
  have h₄A : (S₄ : Set ℕ) ⊆ A := hS₄.trans (hS₃.trans hS₂)
  have hh₃' := hh₃.mono (show (S₄ : Set ℕ) ⊆ S₃ from hS₄)
  have he : Set.range (S₄.orderEmbOfFin hc₄) ⊆ (S₄ : Set ℕ) := by
    rintro _ ⟨i, rfl⟩
    exact S₄.orderEmbOfFin_mem hc₄ i
  obtain ⟨hc₃false, hc₄false⟩ := matrix_homogeneous_bad_colors_false hL
    (S₄.orderEmbOfFin hc₄) he (hslices.mono h₄A) hh₃' hh₄
  refine ⟨S₄, h₄A, hc₄, ⟨c₂, hh₂.mono (hS₄.trans hS₃)⟩, ?_, ?_⟩
  · rwa [← hc₃false]
  · rwa [← hc₄false]

theorem matrix_patterns_small {w : ℕ → ℕ → ℕ → ℕ → ℝ} {δ : ℝ} {S : Set ℕ}
    (h₃ : OrderedHomogeneous (matrixTripleBadColor w δ) S (fun _ => false))
    (h₄ : OrderedHomogeneous (matrixQuadrupleBadColor w δ) S (fun _ => false))
    {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a < b) (had : a < d) (hcb : c < b) (hcd : c < d)
    (hne : a ≠ c ∨ b ≠ d) : w a b c d < δ := by
  classical
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := hne.resolve_left (not_not.mpr rfl)
    rcases lt_or_gt_of_ne hbd with hbd | hdb
    · have hh := congrFun (h₃ (orderedTriple a b d hab hbd)
        (range_orderedTriple_subset hab hbd ha hb hd)) 0
      simpa [matrixTripleBadColor, orderedTriple] using hh
    · have hh := congrFun (h₃ (orderedTriple a d b had hdb)
        (range_orderedTriple_subset had hdb ha hd hb)) 1
      simpa [matrixTripleBadColor, orderedTriple] using hh
  · by_cases hbd : b = d
    · subst d
      rcases lt_or_gt_of_ne hac with hac | hca
      · have hh := congrFun (h₃ (orderedTriple a c b hac hcb)
          (range_orderedTriple_subset hac hcb ha hc hb)) 2
        simpa [matrixTripleBadColor, orderedTriple] using hh
      · have hh := congrFun (h₃ (orderedTriple c a b hca hab)
          (range_orderedTriple_subset hca hab hc ha hb)) 3
        simpa [matrixTripleBadColor, orderedTriple] using hh
    · rcases lt_or_gt_of_ne hac with hac | hca <;> rcases lt_or_gt_of_ne hbd with hbd | hdb
      · have hh := congrFun (h₄ (orderedQuadruple a c b d hac hcb hbd)
          (range_orderedQuadruple_subset hac hcb hbd ha hc hb hd)) 0
        simpa [matrixQuadrupleBadColor, orderedQuadruple] using hh
      · have hh := congrFun (h₄ (orderedQuadruple a c d b hac hcd hdb)
          (range_orderedQuadruple_subset hac hcd hdb ha hc hd hb)) 1
        simpa [matrixQuadrupleBadColor, orderedQuadruple] using hh
      · have hh := congrFun (h₄ (orderedQuadruple c a b d hca hab hbd)
          (range_orderedQuadruple_subset hca hab hbd hc ha hb hd)) 2
        simpa [matrixQuadrupleBadColor, orderedQuadruple] using hh
      · have hh := congrFun (h₄ (orderedQuadruple c a d b hca had hdb)
          (range_orderedQuadruple_subset hca had hdb hc ha hd hb)) 3
        simpa [matrixQuadrupleBadColor, orderedQuadruple] using hh

end ThesisCommon

