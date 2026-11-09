import SurveyStatements.P1PrefixClassRamsey
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Nat.Lattice

/-! Predicting the color of the next point after a fixed finite front.
Local characteristic-prefix dependence is enough; the homogeneous tail is
provided by the proved finite-color closed Ramsey theorem. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

theorem strictMono_prefix_eq_low_membership (ν η : ℕ → ℕ)
    (hν : StrictMono ν) (hη : StrictMono η) {N : ℕ}
    (heq : (Finset.range N).image η = (Finset.range N).image ν) :
    ∀ i : ℕ, i < N → (i ∈ range ν ↔ i ∈ range η) := by
  intro i hi
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j < N := (hν.id_le j).trans_lt hi
    have hm : ν j ∈ (Finset.range N).image η := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact ⟨k, hk⟩
  · rintro ⟨j, rfl⟩
    have hj : j < N := (hη.id_le j).trans_lt hi
    have hm : η j ∈ (Finset.range N).image ν := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact ⟨k, hk⟩

theorem strictMono_prefix_eq_first (ν η : ℕ → ℕ)
    (hν : StrictMono ν) (hη : StrictMono η) {N : ℕ} (hN : 0 < N)
    (heq : (Finset.range N).image η = (Finset.range N).image ν) : η 0 = ν 0 := by
  apply le_antisymm
  · have hm : ν 0 ∈ (Finset.range N).image η := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hN, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hj ▸ hη.monotone (Nat.zero_le j)
  · have hm : η 0 ∈ (Finset.range N).image ν := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hN, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hj ▸ hν.monotone (Nat.zero_le j)

theorem strictMono_range_sInf (ν : ℕ → ℕ) (hν : StrictMono ν) :
    sInf (range ν) = ν 0 := by
  apply le_antisymm (Nat.sInf_le (show ν 0 ∈ range ν from ⟨0, rfl⟩))
  obtain ⟨j, hj⟩ := Nat.sInf_mem (Set.range_nonempty ν)
  exact hj ▸ hν.monotone (Nat.zero_le j)

theorem ramsey_exists_nextColor_prediction {α : Type*} [Finite α]
    (c : Set ℕ → ℕ → α)
    (hc : ∀ A : Set ℕ, A.Infinite → ∀ n : ℕ, ∃ r : ℕ,
      ∀ B : Set ℕ, B.Infinite →
        (∀ i : ℕ, i < r → (i ∈ A ↔ i ∈ B)) → c B n = c A n)
    (front : Finset ℕ) (M : Set ℕ) (hM : M.Infinite) :
    ∃ Y : Set ℕ, Y ⊆ M ∧ Y.Infinite ∧
      (∀ a ∈ front, ∀ b ∈ Y, a < b) ∧ ∃ color : α,
        ∀ Q : Set ℕ, Q ⊆ Y → Q.Infinite →
          c ((front : Set ℕ) ∪ Q) (sInf Q) = color := by
  classical
  let F : Set ℕ → α := fun Q => c ((front : Set ℕ) ∪ Q) (sInf Q)
  have hlocal : ∀ ν : ℕ → ℕ, StrictMono ν → ∃ N : ℕ,
      ∀ η : ℕ → ℕ, StrictMono η →
        (Finset.range N).image η = (Finset.range N).image ν → F (range η) = F (range ν) := by
    intro ν hν
    have hνinf := Set.infinite_range_of_injective hν.injective
    have hAinf : ((front : Set ℕ) ∪ range ν).Infinite := hνinf.mono subset_union_right
    obtain ⟨r, hr⟩ := hc _ hAinf (ν 0)
    refine ⟨max r 1, ?_⟩
    intro η hη heq
    have hηinf := Set.infinite_range_of_injective hη.injective
    have hBinf : ((front : Set ℕ) ∪ range η).Infinite := hηinf.mono subset_union_right
    have hfirst := strictMono_prefix_eq_first ν η hν hη
      (show 0 < max r 1 by omega) heq
    dsimp only [F]
    rw [strictMono_range_sInf ν hν, strictMono_range_sInf η hη, hfirst]
    apply hr _ hBinf
    intro i hi
    have hmem := strictMono_prefix_eq_low_membership ν η hν hη heq i
      (hi.trans_le (Nat.le_max_left _ _))
    exact or_congr Iff.rfl hmem
  let T := M ∩ Ioi (front.sup id)
  have hT : T.Infinite := infiniteSet_inter_Ioi M hM (front.sup id)
  obtain ⟨Y, hYT, hY, color, hcolor⟩ := prefixClass_finiteColorRamsey F hlocal T hT
  refine ⟨Y, fun b hb => (hYT hb).1, hY, ?_, color, ?_⟩
  · intro a ha b hb
    exact (Finset.le_sup (f := id) ha).trans_lt (hYT hb).2
  · intro Q hQY hQ
    letI : Infinite Q := hQ.to_subtype
    let ν : ℕ → ℕ := Nat.orderEmbeddingOfSet Q
    have hν : StrictMono ν := (Nat.orderEmbeddingOfSet Q).strictMono
    have hνrange : range ν = Q := Nat.orderEmbeddingOfSet_range Q
    have h := hcolor ν hν (by rw [hνrange]; exact hQY)
    simpa only [F, hνrange] using h

end SurveyStatements.P1
