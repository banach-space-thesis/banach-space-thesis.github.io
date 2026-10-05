import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Basic

/-! Selecting disjoint finite witnesses through continuum many stages. The
argument uses the initial ordinal of the continuum, so it needs neither the
continuum hypothesis nor regularity of the continuum. -/

noncomputable section
namespace Posets
open Cardinal

theorem exists_finite_witness_avoiding {α : Type}
    (F : Set ℕ → Finset α) (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (S : Set α) (hS : #S < 𝔠) : ∃ i, ∀ a ∈ F i, a ∉ S := by
  classical
  by_contra hn
  push_neg at hn
  choose a ha haS using hn
  have hinj : Function.Injective (fun i => (⟨a i, haS i⟩ : S)) := by
    intro i j heq
    by_contra hij
    apply Finset.disjoint_left.mp (hd hij) (ha i)
    have he : a i = a j := congrArg Subtype.val heq
    rw [he]
    exact ha j
  have hle := Cardinal.mk_le_of_injective hinj
  rw [Cardinal.mk_set_nat] at hle
  exact hS.not_ge hle

abbrev ContinuumStage := Cardinal.continuum.{0}.ord.toType

def finiteWitnessHistory {α : Type} (F : ContinuumStage → Set ℕ → Finset α)
    (i : ContinuumStage) (g : ∀ j, j < i → Set ℕ) : Set α :=
  ⋃ j : Set.Iio i, (F j.val (g j.val j.property) : Set α)

theorem finiteWitnessHistory_card_lt {α : Type} (F : ContinuumStage → Set ℕ → Finset α)
    (i : ContinuumStage) (g : ∀ j, j < i → Set ℕ) :
    #(finiteWitnessHistory F i g) < 𝔠 := by
  have hbound : #(finiteWitnessHistory F i g) ≤ #(Set.Iio i) * ℵ₀ := by
    apply Cardinal.mk_iUnion_le_sum_mk.trans
    calc
      Cardinal.sum (fun j : Set.Iio i => #↥(F j.val (g j.val j.property)))
          ≤ Cardinal.sum (fun _ : Set.Iio i => ℵ₀) :=
        Cardinal.sum_le_sum _ _ (fun _ => (Cardinal.lt_aleph0_of_finite _).le)
      _ = #(Set.Iio i) * ℵ₀ := Cardinal.sum_const' _ _
  exact hbound.trans_lt (Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum
    (Cardinal.mk_Iio_ord_toType i) Cardinal.aleph0_lt_continuum)

def chooseFiniteWitness {α : Type} (F : ContinuumStage → Set ℕ → Finset α)
    (hd : ∀ i, Pairwise fun j k => Disjoint (F i j) (F i k))
    (i : ContinuumStage) (g : ∀ j, j < i → Set ℕ) : Set ℕ :=
  Classical.choose (exists_finite_witness_avoiding (F i) (hd i)
    (finiteWitnessHistory F i g) (finiteWitnessHistory_card_lt F i g))

theorem chooseFiniteWitness_avoids {α : Type} (F : ContinuumStage → Set ℕ → Finset α)
    (hd : ∀ i, Pairwise fun j k => Disjoint (F i j) (F i k))
    (i : ContinuumStage) (g : ∀ j, j < i → Set ℕ) :
    ∀ a ∈ F i (chooseFiniteWitness F hd i g), a ∉ finiteWitnessHistory F i g :=
  Classical.choose_spec (exists_finite_witness_avoiding (F i) (hd i)
    (finiteWitnessHistory F i g) (finiteWitnessHistory_card_lt F i g))

def transfiniteFiniteWitnessChoice {α : Type} (F : ContinuumStage → Set ℕ → Finset α)
    (hd : ∀ i, Pairwise fun j k => Disjoint (F i j) (F i k)) : ContinuumStage → Set ℕ :=
  WellFoundedLT.fix (chooseFiniteWitness F hd)

theorem transfiniteFiniteWitnessChoice_disjoint {α : Type}
    (F : ContinuumStage → Set ℕ → Finset α)
    (hd : ∀ i, Pairwise fun j k => Disjoint (F i j) (F i k)) :
    Pairwise fun i j => Disjoint
      (F i (transfiniteFiniteWitnessChoice F hd i))
      (F j (transfiniteFiniteWitnessChoice F hd j)) := by
  have hlt (i j : ContinuumStage) (hij : i < j) : Disjoint
      (F i (transfiniteFiniteWitnessChoice F hd i))
      (F j (transfiniteFiniteWitnessChoice F hd j)) := by
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have heq : transfiniteFiniteWitnessChoice F hd j =
        chooseFiniteWitness F hd j (fun k _ => transfiniteFiniteWitnessChoice F hd k) :=
      WellFoundedLT.fix_eq _ _
    rw [heq] at haj
    apply chooseFiniteWitness_avoids F hd j _ a haj
    exact Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hai⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem exists_transfinite_disjoint_finite_witnesses {α : Type}
    (F : ContinuumStage → Set ℕ → Finset α)
    (hd : ∀ i, Pairwise fun j k => Disjoint (F i j) (F i k)) :
    ∃ g : ContinuumStage → Set ℕ, Pairwise fun i j => Disjoint (F i (g i)) (F j (g j)) :=
  ⟨transfiniteFiniteWitnessChoice F hd, transfiniteFiniteWitnessChoice_disjoint F hd⟩

end Posets
