import SurveyStatements.P1PrefixClassRamsey
import Mathlib.Order.OrderIsoNat

/-! Finite initial segments of ordered finite and infinite sets of naturals,
including the actual extension of a prescribed finite set to an infinite branch. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

def FinsetIsInitialSegment (A B : Finset ℕ) : Prop :=
  A ⊆ B ∧ ∀ a ∈ A, ∀ b ∈ B, b ∉ A → a < b

def FinsetIsInitialSegmentOfSet (s : Finset ℕ) (A : Set ℕ) : Prop :=
  (s : Set ℕ) ⊆ A ∧ ∀ a ∈ s, ∀ b ∈ A, b ∉ s → a < b

theorem strictMono_prefix_initialSegment (ν : ℕ → ℕ) (hν : StrictMono ν)
    (m n : ℕ) (hmn : m ≤ n) :
    FinsetIsInitialSegment ((Finset.range m).image ν) ((Finset.range n).image ν) := by
  refine ⟨Finset.image_subset_image (Finset.range_mono hmn), ?_⟩
  intro a ha b hb hba
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  have hmj : m ≤ j := by
    by_contra h
    exact hba (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  exact hν (lt_of_lt_of_le (Finset.mem_range.mp hi) hmj)

theorem strictMono_prefix_initialSegmentOfSet (ν : ℕ → ℕ) (hν : StrictMono ν) (n : ℕ) :
    FinsetIsInitialSegmentOfSet ((Finset.range n).image ν) (range ν) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, rfl⟩
  · intro a ha b hb hba
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, rfl⟩ := hb
    have hnj : n ≤ j := by
      by_contra h
      exact hba (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
    exact hν (lt_of_lt_of_le (Finset.mem_range.mp hi) hnj)

theorem initialSegmentOfSet_eq_prefix (ν : ℕ → ℕ) (hν : StrictMono ν)
    (s : Finset ℕ) (hs : FinsetIsInitialSegmentOfSet s (range ν)) :
    ∃ n, (Finset.range n).image ν = s := by
  have hex : ∃ n, ν n ∉ s := by
    refine ⟨s.sup id + 1, ?_⟩
    intro hmem
    have hle : ν (s.sup id + 1) ≤ s.sup id := Finset.le_sup (f := id) hmem
    have hge : s.sup id + 1 ≤ ν (s.sup id + 1) := hν.id_le (s.sup id + 1)
    omega
  let n := Nat.find hex
  have hn : ν n ∉ s := Nat.find_spec hex
  refine ⟨n, Finset.Subset.antisymm ?_ ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    by_contra hnot
    exact Nat.find_min hex (Finset.mem_range.mp hj) hnot
  · intro a ha
    obtain ⟨j, rfl⟩ := hs.1 ha
    have hj : j < n := hν.lt_iff_lt.mp (hs.2 _ ha _ ⟨n, rfl⟩ hn)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

theorem initialSegmentsOfSet_comparable (ν : ℕ → ℕ) (hν : StrictMono ν)
    (s t : Finset ℕ) (hs : FinsetIsInitialSegmentOfSet s (range ν))
    (ht : FinsetIsInitialSegmentOfSet t (range ν)) :
    FinsetIsInitialSegment s t ∨ FinsetIsInitialSegment t s := by
  obtain ⟨m, hm⟩ := initialSegmentOfSet_eq_prefix ν hν s hs
  obtain ⟨n, hn⟩ := initialSegmentOfSet_eq_prefix ν hν t ht
  rcases le_total m n with h | h
  · exact Or.inl (by simpa only [hm, hn] using strictMono_prefix_initialSegment ν hν m n h)
  · exact Or.inr (by simpa only [hm, hn] using strictMono_prefix_initialSegment ν hν n m h)

theorem infinite_branch_extending_finset (M : Set ℕ) (hM : M.Infinite)
    (s : Finset ℕ) (hsM : (s : Set ℕ) ⊆ M) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ range ν ⊆ M ∧
      FinsetIsInitialSegmentOfSet s (range ν) := by
  let A : Set ℕ := (s : Set ℕ) ∪ (M ∩ Ioi (s.sup id))
  have hA : A.Infinite := (infiniteSet_inter_Ioi M hM (s.sup id)).mono (by
    intro x hx
    exact Or.inr hx)
  letI : Infinite A := Set.infinite_coe_iff.mpr hA
  let ν := Nat.orderEmbeddingOfSet A
  have hr : range ν = A := Nat.orderEmbeddingOfSet_range A
  refine ⟨ν, ν.strictMono, ?_, ?_⟩
  · rw [hr]
    intro x hx
    rcases hx with hx | hx
    · exact hsM hx
    · exact hx.1
  · rw [hr]
    refine ⟨fun x hx => Or.inl hx, ?_⟩
    intro a ha b hb hbs
    have hb' : s.sup id < b := by
      rcases hb with hb | hb
      · exact (hbs hb).elim
      · exact hb.2
    exact (Finset.le_sup (f := id) ha).trans_lt hb'

end SurveyStatements.P1
