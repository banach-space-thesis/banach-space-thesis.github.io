import Posets.IncidenceIdealUnits

/-! Ideals of a finite incidence algebra are exactly the interval upsets.
The correspondence uses genuine two-sided ideals, not a count definition. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P]
  [LocallyFiniteOrder P] [Fintype P]

def incidenceIdealIntervals (I : TwoSidedIdeal (IncidenceAlgebra 𝕜 P)) : IntervalUpsets P :=
  ⟨{i | incidenceUnit (𝕜 := 𝕜) i ∈ I}, by
    intro i hi j hs ht
    change incidenceUnit j ∈ I
    rw [← incidence_enlarge_unit i j hs ht]
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hi)⟩

def intervalUpsetIdeal (W : IntervalUpsets P) : TwoSidedIdeal (IncidenceAlgebra 𝕜 P) :=
  TwoSidedIdeal.mk' {f | ∀ i : PosetInterval P, i ∉ W.val → f i.val.1 i.val.2 = 0}
    (by intro i _; rfl)
    (by intro f g hf hg i hi; change f _ _ + g _ _ = 0; rw [hf i hi, hg i hi, add_zero])
    (by intro f hf i hi; change -f _ _ = 0; rw [hf i hi, neg_zero])
    (by
      intro f g hg i hi
      rw [incidence_mul_univ]
      apply Finset.sum_eq_zero
      intro r _
      by_cases hsr : i.val.1 ≤ r
      · by_cases hrt : r ≤ i.val.2
        · have hn : (⟨(r, i.val.2), hrt⟩ : PosetInterval P) ∉ W.val :=
            fun h => hi (W.property _ h i hsr le_rfl)
          rw [hg ⟨(r, i.val.2), hrt⟩ hn, mul_zero]
        · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hrt g, mul_zero]
      · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hsr f, zero_mul])
    (by
      intro f g hf i hi
      rw [incidence_mul_univ]
      apply Finset.sum_eq_zero
      intro r _
      by_cases hsr : i.val.1 ≤ r
      · by_cases hrt : r ≤ i.val.2
        · have hn : (⟨(i.val.1, r), hsr⟩ : PosetInterval P) ∉ W.val :=
            fun h => hi (W.property _ h i le_rfl hrt)
          rw [hf ⟨(i.val.1, r), hsr⟩ hn, zero_mul]
        · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hrt g, mul_zero]
      · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hsr f, zero_mul])

@[simp] theorem mem_intervalUpsetIdeal (W : IntervalUpsets P) (f : IncidenceAlgebra 𝕜 P) :
    f ∈ intervalUpsetIdeal (𝕜 := 𝕜) W ↔
      ∀ i : PosetInterval P, i ∉ W.val → f i.val.1 i.val.2 = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f

theorem incidenceUnit_mem_intervalUpsetIdeal (W : IntervalUpsets P) (i : PosetInterval P) :
    incidenceUnit (𝕜 := 𝕜) i ∈ intervalUpsetIdeal W ↔ i ∈ W.val := by
  rw [mem_intervalUpsetIdeal]
  constructor
  · intro h
    by_contra hi
    have hbad := h i hi
    simp at hbad
  · intro hi j hj
    have hn : ¬ (j.val.1 = i.val.1 ∧ j.val.2 = i.val.2) := by
      rintro ⟨hs, ht⟩
      exact hj (Subtype.ext (Prod.ext hs ht) ▸ hi)
    simp [hn]

theorem intervalUpsetIdeal_intervals (I : TwoSidedIdeal (IncidenceAlgebra 𝕜 P)) :
    intervalUpsetIdeal (incidenceIdealIntervals I) = I := by
  ext f
  rw [mem_intervalUpsetIdeal]
  constructor
  · intro h
    rw [incidence_unit_expansion f]
    apply I.finsetSum_mem
    intro i _
    by_cases hi : incidenceUnit (𝕜 := 𝕜) i ∈ I
    · exact incidenceIdeal_smul_mem I _ hi
    · have hz := h i hi
      rw [hz, zero_smul]
      exact I.zero_mem
  · intro hf i hi
    by_contra hn
    exact hi (incidenceUnit_mem_of_coefficient_ne_zero I hf i hn)

theorem incidenceIdealIntervals_ideal (W : IntervalUpsets P) :
    incidenceIdealIntervals (intervalUpsetIdeal (𝕜 := 𝕜) W) = W := by
  apply Subtype.ext
  ext i
  exact incidenceUnit_mem_intervalUpsetIdeal W i

/-- Algebraic classification for every finite poset, including the empty poset. -/
def incidenceIdealEquiv : TwoSidedIdeal (IncidenceAlgebra 𝕜 P) ≃ IntervalUpsets P where
  toFun := incidenceIdealIntervals
  invFun := intervalUpsetIdeal
  left_inv := intervalUpsetIdeal_intervals
  right_inv := incidenceIdealIntervals_ideal

theorem incidenceIdeal_card : Nat.card (TwoSidedIdeal (IncidenceAlgebra 𝕜 P)) = idealCount P :=
  Nat.card_congr (incidenceIdealEquiv (𝕜 := 𝕜) (P := P))

end Posets
