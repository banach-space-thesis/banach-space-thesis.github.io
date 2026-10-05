import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic

/-! The infinite finite-color Ramsey theorem for finite subsets of naturals.
The proof uses nested infinite sets and ordinary finite pigeonhole, with
an induction on the size of the subsets. -/
noncomputable section
namespace ThesisCommon

def FinsetHomogeneous {C : Type*} (c : Finset ℕ → C) (k : ℕ) (S : Set ℕ) (γ : C) : Prop :=
  ∀ u : Finset ℕ, (u : Set ℕ) ⊆ S → u.card = k → c u = γ

theorem infinite_ramsey {C : Type*} [Finite C] (k : ℕ) (c : Finset ℕ → C)
    {S : Set ℕ} (hS : S.Infinite) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧ ∃ γ : C, FinsetHomogeneous c k T γ := by
  classical
  induction k generalizing c S with
  | zero =>
      refine ⟨S, Set.Subset.refl S, hS, c ∅, ?_⟩
      intro u _ hu
      exact congrArg c (Finset.card_eq_zero.mp hu)
  | succ k ih =>
      let InfiniteSet := {A : Set ℕ // A.Infinite}
      have step (A : InfiniteSet) :
          ∃ (x : ℕ) (B : InfiniteSet) (γ : C), x ∈ A.val ∧ B.val ⊆ A.val ∧
            (∀ y ∈ B.val, x < y) ∧
            FinsetHomogeneous (fun u => c (insert x u)) k B.val γ := by
        obtain ⟨x, hx⟩ := A.property.nonempty
        have htail : (A.val \ Set.Iic x).Infinite := A.property.diff (Set.finite_Iic x)
        obtain ⟨B, hB, hBinf, γ, hγ⟩ := ih (fun u => c (insert x u)) htail
        exact ⟨x, ⟨B, hBinf⟩, γ, hx, fun y hy => (hB hy).1,
          fun y hy => lt_of_not_ge (hB hy).2, hγ⟩
      choose point next color hpoint hsub hlt hcolor using step
      let chain : ℕ → InfiniteSet := Nat.rec ⟨S, hS⟩ (fun _ A => next A)
      let f : ℕ → ℕ := fun n => point (chain n)
      let labels : ℕ → C := fun n => color (chain n)
      have hanti : Antitone (fun n => (chain n).val) := by
        apply antitone_nat_of_succ_le
        intro n
        exact hsub (chain n)
      have hfmem (n : ℕ) : f n ∈ (chain n).val := hpoint (chain n)
      have htail (i j : ℕ) (hij : i < j) : f j ∈ (chain (i + 1)).val :=
        hanti (Nat.succ_le_of_lt hij) (hfmem j)
      have hf : StrictMono f := by
        intro i j hij
        exact hlt (chain i) (f j) (htail i j hij)
      obtain ⟨γ, hγ⟩ := Finite.exists_infinite_fiber labels
      let I := labels ⁻¹' {γ}
      let T := f '' I
      have hI : I.Infinite := Set.infinite_coe_iff.mp hγ
      refine ⟨T, ?_, hI.image hf.injective.injOn, γ, ?_⟩
      · rintro x ⟨n, _, rfl⟩
        exact hanti (Nat.zero_le n) (hfmem n)
      · intro u hu hucard
        have hu0 : u.Nonempty := Finset.card_pos.mp (by omega)
        let x := u.min' hu0
        have hxmem : x ∈ u := Finset.min'_mem _ _
        obtain ⟨i, hi, hix⟩ := hu hxmem
        have hrest : ((u.erase x : Finset ℕ) : Set ℕ) ⊆ (chain (i+1)).val := by
          intro y hy
          have hyu : y ∈ u := Finset.mem_of_mem_erase hy
          obtain ⟨j, _, hj⟩ := hu hyu
          have hxy : x < y := Finset.min'_lt_of_mem_erase_min' u hu0 hy
          have hij : i < j := hf.lt_iff_lt.mp (by simpa only [hix, hj] using hxy)
          rw [← hj]
          exact htail i j hij
        have hrestcard : (u.erase x).card = k := by
          rw [Finset.card_erase_of_mem hxmem, hucard]
          omega
        have hmono := hcolor (chain i) (u.erase x) hrest hrestcard
        have hlabel : labels i = γ := hi
        change c (insert (f i) (u.erase x)) = labels i at hmono
        rw [hix, Finset.insert_erase hxmem] at hmono
        exact hmono.trans hlabel

end ThesisCommon
