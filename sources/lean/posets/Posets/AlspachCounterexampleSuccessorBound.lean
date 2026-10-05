import Posets.AlspachCounterexampleWindowRows
import Posets.AlspachCounterexampleWindowBounds
import ThesisCommon.Analysis.OrdinalBakerDerived

/-! The successor rank recurrence. At a fixed mass threshold exceptional
spines inherit the previous bound, while all remaining spines reduce to
the base after the doubled-threshold bound. Two extra successor levels
allow the common base point to be removed from a closed parent window. -/

noncomputable section
open Set Topology Order ThesisCommon
namespace Posets
namespace AlspachCompactRows
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [CompactSpace K] [T2Space K] [Countable K]
variable (p : K) (G : AlspachCompactRows 𝕜)

theorem successorBaseRows_derived_empty (η : Ordinal)
    (hK : ordinalDerived (univ : Set K) η = ∅) :
    ordinalDerived (successorBaseRows p G) η = ∅ := by
  let e : K → WeakDual 𝕜 (JLMS.CZero 𝕜 (baseSuccessor p G).Point) :=
    fun i => (baseSuccessor p G).weakRows (alspachGraftBase _ _ i)
  have he : IsClosedEmbedding e :=
    (baseSuccessor p G).weakRows_isClosedEmbedding.comp
      (alspachGraftBase_isClosedEmbedding id _)
  change ordinalDerived (range e) η = ∅
  rw [← image_univ, ordinalDerived_image_closedEmbedding he, hK, image_empty]

theorem fiber_wolfe_empty_of_inner {ε : ℝ} (i : K) (α : Ordinal)
    (he : wolfeFamily G.pointAtomicModel ε (range G.weakRows) α = ∅) :
    wolfeFamily (baseSuccessor p G).pointAtomicModel ε
      (range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j))) α = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨μ, U⟩ h
  obtain ⟨j, rfl⟩ := (wolfeFamily_subset_base (baseSuccessor p G).pointAtomicModel ε _ α h).1
  obtain ⟨b, hb⟩ := fiber_wolfe_same_threshold p G i α j U h
  rw [he] at hb
  exact hb

theorem successor_completedSpine_rows (i : K) :
    (baseSuccessor p G).weakRows '' range
      (alspachGraftCompletedSpine id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) i) =
      range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j)) := by
  apply subset_antisymm
  · rintro μ ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨alspachPunctureHomeomorph G.rows.index x, ?_⟩
    simp only [fiberIndex, AlspachPointedRows.baseIndexAttach, alspachCompactGraftAttach,
      Homeomorph.symm_apply_apply]
  · rintro μ ⟨j, rfl⟩
    exact ⟨fiberIndex p G i j,
      ⟨(alspachPunctureHomeomorph G.rows.index).symm j, rfl⟩, rfl⟩

theorem successor_wolfe_closed_window_empty {ε : ℝ} (hε : 0 < ε)
    (α β η κ : Ordinal) (hc : κ.card ≤ Cardinal.aleph0)
    (hα : α ≤ κ) (hβ : β + η ≤ κ)
    (hK : ordinalDerived (univ : Set K) η = ∅)
    (hinner : wolfeFamily G.pointAtomicModel ε (range G.weakRows) α = ∅)
    (hdouble : wolfeFamily G.pointAtomicModel (2 * ε) (range G.weakRows) β = ∅)
    (C : Set (baseSuccessor p G).Point) (hC : IsClosed C)
    (hp : alspachGraftBase _ _ p ∉ C) :
    ∀ U ⊆ C, ∀ μ, (μ, U) ∉
      wolfeFamily (baseSuccessor p G).pointAtomicModel ε (range (baseSuccessor p G).weakRows) κ := by
  obtain ⟨s, hs⟩ := exists_outside_wolfeWindow_subset_base p G C hC hp β hdouble
  let A : Option {i // i ∈ s} → Set (WeakDual 𝕜 (JLMS.CZero 𝕜 (baseSuccessor p G).Point)) :=
    fun j => (baseSuccessor p G).weakRows ''
      alspachGraftFiniteCover id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) s j
  have hA (j) : IsClosed (A j) :=
    ((alspachGraftFiniteCover_isClosed id _ s j).isCompact.image
      (baseSuccessor p G).weakRows_continuous).isClosed
  have hcover : (⋃ j, A j) = range (baseSuccessor p G).weakRows := by
    simp only [A, ← image_iUnion]
    exact (congrArg (fun W => (baseSuccessor p G).weakRows '' W)
      (alspachGraftFiniteCover_iUnion id
        (fun _ : K => {j : G.Index // j ≠ G.rows.index}) s)).trans (image_univ)
  intro U hUC μ hμ
  rw [← hcover, wolfeFamily_iUnion_closed _ _ A hA κ] at hμ
  obtain ⟨j, hj⟩ := mem_iUnion.mp hμ
  cases j with
  | none =>
      have hl := wolfeFamily_antitone_on_countable (baseSuccessor p G).pointAtomicModel ε
        (A none) hc hβ hj
      exact alspachWolfeWindow_empty_of_projection_bound (baseSuccessor p G).pointAtomicModel hε
        (successorOutsideRows p G s) (successorBaseRows p G) C β η
        ((Ordinal.card_le_card hβ).trans hc) hs
        (successorBaseRows_derived_empty p G η hK) U hUC μ hl
  | some i =>
      have hl := wolfeFamily_antitone_on_countable (baseSuccessor p G).pointAtomicModel ε
        (A (some i)) hc hα hj
      change (μ, U) ∈ wolfeFamily (baseSuccessor p G).pointAtomicModel ε
        ((baseSuccessor p G).weakRows '' range
          (alspachGraftCompletedSpine id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) i)) α at hl
      rw [successor_completedSpine_rows, fiber_wolfe_empty_of_inner p G i α hinner] at hl
      exact hl

theorem successor_wolfe_empty {ε : ℝ} (hε : 0 < ε)
    (α β η κ : Ordinal) (hc : κ.card ≤ Cardinal.aleph0)
    (hα : α ≤ κ) (hβ : β + η ≤ κ)
    (hK : ordinalDerived (univ : Set K) η = ∅)
    (hinner : wolfeFamily G.pointAtomicModel ε (range G.weakRows) α = ∅)
    (hdouble : wolfeFamily G.pointAtomicModel (2 * ε) (range G.weakRows) β = ∅) :
    wolfeFamily (baseSuccessor p G).pointAtomicModel ε (range (baseSuccessor p G).weakRows)
      (succ (succ κ)) = ∅ :=
  alspachWolfe_empty_of_closed_windows (baseSuccessor p G).pointAtomicModel ε
    (range (baseSuccessor p G).weakRows) (alspachGraftBase _ _ p) κ
    (successor_wolfe_closed_window_empty p G hε α β η κ hc hα hβ hK hinner hdouble)

end AlspachCompactRows
end Posets
