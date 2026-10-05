import Posets.AlspachCounterexampleFiberWolfe
import Posets.AlspachCounterexampleGraftCover
import Posets.AlspachCounterexampleWolfeWindow

/-! In a closed window missing the shared base point, the nonexceptional
successor rows disappear at the preceding family's doubled threshold. The
remaining projected Wolfe measures are supported on the embedded base. -/

noncomputable section
open Set Topology ThesisCommon
namespace Posets
namespace AlspachCompactRows
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [CompactSpace K] [T2Space K] [Countable K]
variable (p : K) (G : AlspachCompactRows 𝕜)

def successorOutsideRows (s : Finset K) :=
  (baseSuccessor p G).weakRows ''
    alspachGraftOutsideSpines id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) s

def successorBaseRows :=
  Set.range (fun i : K => (baseSuccessor p G).weakRows (alspachGraftBase _ _ i))

@[simp] theorem fiberIndex_nonroot (i : K) (j : {j : G.Index // j ≠ G.rows.index}) :
    fiberIndex p G i j = alspachGraftSpine _ _ ⟨i, j⟩ :=
  alspachCompactGraftAttach_nonroot id (fun _ : K => G.Index)
    (fun _ => G.rows.index) i j j.property

theorem successorOutsideRows_isClosed (s : Finset K) :
    IsClosed (successorOutsideRows p G s) :=
  ((alspachGraftOutsideSpines_isClosed id _ s).isCompact.image
    (baseSuccessor p G).weakRows_continuous).isClosed

theorem successorBaseRows_isClosed : IsClosed (successorBaseRows p G) :=
  isCompact_range ((baseSuccessor p G).weakRows_continuous.comp
    (alspachGraftBase_continuous id _)) |>.isClosed

theorem outside_wolfeWindow_subset_base {ε : ℝ}
    (C : Set (baseSuccessor p G).Point) (s : Finset K) (β : Ordinal)
    (hcontrolled : ∀ i ∉ s, ∀ j : G.Index, ∀ U : Set (baseSuccessor p G).Point,
      U ⊆ C → ((baseSuccessor p G).weakRows (fiberIndex p G i j), U) ∈
        wolfeFamily (baseSuccessor p G).pointAtomicModel ε
          (range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j))) β →
      ∃ b : Bool, (G.weakRows j, fiberPoint p G i b ⁻¹' U) ∈
        wolfeFamily G.pointAtomicModel (2 * ε) (range G.weakRows) β)
    (hempty : wolfeFamily G.pointAtomicModel (2 * ε) (range G.weakRows) β = ∅) :
    alspachWolfeWindowMeasures (baseSuccessor p G).pointAtomicModel ε
      (successorOutsideRows p G s) C β ⊆ successorBaseRows p G := by
  rintro μ ⟨U, hUC, hU⟩
  obtain ⟨z, hz, rfl⟩ :=
    (wolfeFamily_subset_base (baseSuccessor p G).pointAtomicModel ε _ β hU).1
  rcases alspachGraft_cases id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) z with
    ⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
  · exact mem_range_self i
  · have hi : i ∉ s := (alspachGraftSpine_mem_outsideSpines_iff id
      (fun _ : K => {j : G.Index // j ≠ G.rows.index}) s ⟨i, j⟩).mp hz
    have hl := alspach_wolfe_localize_parameter (baseSuccessor p G).pointAtomicModel ε
      (baseSuccessor p G).weakRows (baseSuccessor p G).weakRows_isClosedEmbedding.isEmbedding
      (alspachGraftOutsideSpines id _ s) (alspachGraftOpenSpine id _ i)
      (alspachGraftOpenSpine_isOpen id _ i) (alspachGraftSpine _ _ ⟨i, j⟩)
      (show alspachGraftSpine id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) ⟨i, j⟩ ∈
        alspachGraftOpenSpine id (fun _ : K => {j : G.Index // j ≠ G.rows.index}) i from ⟨j, rfl⟩)
      U β hU
    have hs : (baseSuccessor p G).weakRows ''
        (alspachGraftOutsideSpines id _ s ∩ alspachGraftOpenSpine id _ i) ⊆
        range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j)) := by
      rintro μ ⟨z, ⟨_, ⟨j, rfl⟩⟩, rfl⟩
      exact ⟨j, congrArg (baseSuccessor p G).weakRows (fiberIndex_nonroot p G i j)⟩
    have hf := wolfeFamily_mono (baseSuccessor p G).pointAtomicModel le_rfl hs β hl
    have hf' : ((baseSuccessor p G).weakRows (fiberIndex p G i j), U) ∈
        wolfeFamily (baseSuccessor p G).pointAtomicModel ε
          (range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j))) β := by
      convert hf using 1
      exact congrArg (fun z => ((baseSuccessor p G).weakRows z, U)) (fiberIndex_nonroot p G i j)
    obtain ⟨b, hb⟩ := hcontrolled i hi j U hUC hf'
    rw [hempty] at hb
    exact hb.elim

theorem exists_outside_wolfeWindow_subset_base {ε : ℝ}
    (C : Set (baseSuccessor p G).Point) (hC : IsClosed C)
    (hp : alspachGraftBase _ _ p ∉ C) (β : Ordinal)
    (hempty : wolfeFamily G.pointAtomicModel (2 * ε) (range G.weakRows) β = ∅) :
    ∃ s : Finset K, alspachWolfeWindowMeasures (baseSuccessor p G).pointAtomicModel ε
      (successorOutsideRows p G s) C β ⊆ successorBaseRows p G := by
  obtain ⟨s, hs⟩ := fiber_wolfe_doubled_threshold p G C hC hp
  exact ⟨s, outside_wolfeWindow_subset_base p G C s β
    (fun i hi => hs i hi β) hempty⟩

end AlspachCompactRows
end Posets
