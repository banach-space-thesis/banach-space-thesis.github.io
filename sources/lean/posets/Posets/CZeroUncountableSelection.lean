import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic

/-! A locally countable symmetric forbidden relation on an uncountable set
admits a full-cardinality independent selection. The recursion does not assume
regularity of the cardinal. -/

noncomputable section
open Cardinal Set
namespace Posets
variable {I : Type}

abbrev UncountableSelectionStage (I : Type) := (Cardinal.mk I).ord.toType

def countableForbiddenHistory (N : I → Set I) (i : UncountableSelectionStage I)
    (g : ∀ j, j < i → I) : Set I := ⋃ j : Iio i, N (g j.val j.property)

theorem countableForbiddenHistory_card_lt (hI : ℵ₀ < #I) (N : I → Set I)
    (hN : ∀ i, (N i).Countable) (i : UncountableSelectionStage I) (g : ∀ j, j < i → I) :
    #(countableForbiddenHistory N i g) < #I := by
  have hbound : #(countableForbiddenHistory N i g) ≤ #(Iio i) * ℵ₀ := by
    apply Cardinal.mk_iUnion_le_sum_mk.trans
    calc
      Cardinal.sum (fun j : Iio i => #(N (g j.val j.property))) ≤
          Cardinal.sum (fun _ : Iio i => ℵ₀) :=
        Cardinal.sum_le_sum _ _ (fun j => Cardinal.le_aleph0_iff_set_countable.mpr (hN _))
      _ = #(Iio i) * ℵ₀ := Cardinal.sum_const' _ _
  exact hbound.trans_lt (Cardinal.mul_lt_of_lt hI.le (Cardinal.mk_Iio_ord_toType i) hI)

theorem exists_outside_countableForbiddenHistory (hI : ℵ₀ < #I) (S : Set I) (hS : #I ≤ #S)
    (N : I → Set I) (hN : ∀ i, (N i).Countable)
    (i : UncountableSelectionStage I) (g : ∀ j, j < i → I) :
    ∃ x ∈ S, x ∉ countableForbiddenHistory N i g := by
  classical
  by_contra hn
  push_neg at hn
  have hsub : S ⊆ countableForbiddenHistory N i g := hn
  exact (countableForbiddenHistory_card_lt hI N hN i g).not_ge
    (hS.trans (Cardinal.mk_le_mk_of_subset hsub))

def chooseOutsideCountableHistory (hI : ℵ₀ < #I) (S : Set I) (hS : #I ≤ #S)
    (N : I → Set I) (hN : ∀ i, (N i).Countable)
    (i : UncountableSelectionStage I) (g : ∀ j, j < i → I) : I :=
  Classical.choose (exists_outside_countableForbiddenHistory hI S hS N hN i g)

def uncountableIndependentChoice (hI : ℵ₀ < #I) (S : Set I) (hS : #I ≤ #S)
    (N : I → Set I) (hN : ∀ i, (N i).Countable) : UncountableSelectionStage I → I :=
  WellFoundedLT.fix (chooseOutsideCountableHistory hI S hS N hN)

theorem uncountableIndependentChoice_spec (hI : ℵ₀ < #I) (S : Set I) (hS : #I ≤ #S)
    (N : I → Set I) (hN : ∀ i, (N i).Countable) (i : UncountableSelectionStage I) :
    uncountableIndependentChoice hI S hS N hN i ∈ S ∧
      ∀ j < i, uncountableIndependentChoice hI S hS N hN i ∉
        N (uncountableIndependentChoice hI S hS N hN j) := by
  have he : uncountableIndependentChoice hI S hS N hN i =
      chooseOutsideCountableHistory hI S hS N hN i
        (fun j _ => uncountableIndependentChoice hI S hS N hN j) := WellFoundedLT.fix_eq _ _
  have hs := Classical.choose_spec (exists_outside_countableForbiddenHistory hI S hS N hN i
    (fun j _ => uncountableIndependentChoice hI S hS N hN j))
  change chooseOutsideCountableHistory hI S hS N hN i _ ∈ S ∧
    chooseOutsideCountableHistory hI S hS N hN i _ ∉ _ at hs
  refine ⟨he ▸ hs.1, ?_⟩
  intro j hj hn
  apply hs.2
  exact mem_iUnion.mpr ⟨⟨j, hj⟩, he ▸ hn⟩

theorem exists_uncountable_independent_embedding (hI : ℵ₀ < #I) (S : Set I) (hS : #I ≤ #S)
    (N : I → Set I) (hN : ∀ i, (N i).Countable) (hself : ∀ i, i ∈ N i)
    (hsymm : ∀ i j, i ∈ N j → j ∈ N i) :
    ∃ e : I ↪ I, (∀ i, e i ∈ S) ∧ ∀ i j, i ≠ j → e i ∉ N (e j) := by
  let g := uncountableIndependentChoice hI S hS N hN
  have havoid : ∀ i j, i ≠ j → g i ∉ N (g j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · intro hn
      exact (uncountableIndependentChoice_spec hI S hS N hN j).2 i hlt (hsymm _ _ hn)
    · exact (uncountableIndependentChoice_spec hI S hS N hN i).2 j hgt
  have hginj : Function.Injective g := by
    intro i j he
    by_contra hij
    exact havoid i j hij (he ▸ hself (g i))
  let d : I ≃ UncountableSelectionStage I := Classical.choice
    (Cardinal.eq.mp (by simp [UncountableSelectionStage]))
  exact ⟨⟨fun i => g (d i), hginj.comp d.injective⟩,
    fun i => (uncountableIndependentChoice_spec hI S hS N hN (d i)).1,
    fun i j hij => havoid (d i) (d j) (fun h => hij (d.injective h))⟩

theorem infinite_twoColor_large (I : Type) [Infinite I] (S : Set I) :
    #I ≤ #S ∨ #I ≤ #(Sᶜ : Set I) := by
  by_cases h : #I ≤ #S
  · exact Or.inl h
  · exact Or.inr (by rw [Cardinal.mk_compl_of_infinite S (lt_of_not_ge h)])

end Posets
