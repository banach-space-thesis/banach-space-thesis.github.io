import Posets.AlspachCounterexampleFiberRows
import Posets.WolfePositiveMixture

/-! Every completed successor row spine pulls back to the previous family.
The two branches have the same threshold in general, and the surviving
branch has twice the threshold away from the finitely many exceptions. -/

noncomputable section
open Set Topology
namespace Posets
namespace AlspachCompactRows
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [CompactSpace K] [T2Space K] [Countable K]
variable (p : K) (G : AlspachCompactRows 𝕜)

abbrev baseSuccessor := (base (𝕜 := 𝕜) K p).successor G

abbrev fiberIndex (i : K) : G.Index → (baseSuccessor p G).Index :=
  AlspachPointedRows.baseIndexAttach p G.rows i

abbrev fiberPoint (i : K) (b : Bool) : G.Point → (baseSuccessor p G).Point :=
  AlspachPointedRows.baseAttach p G.rows (if b then i else p) i

theorem fiber_wolfe_pullback {ε δ : ℝ} (i : K) (C : Set (baseSuccessor p G).Point)
    (hselect : ∀ j : G.Index, ∀ U : Set (baseSuccessor p G).Point, IsOpen U → U ⊆ C →
      ε ≤ ((baseSuccessor p G).rows.row (fiberIndex p G i j)).mass U →
        ∃ b : Bool, δ ≤ (G.rows.row j).mass (fiberPoint p G i b ⁻¹' U))
    (α : Ordinal) (j : G.Index) (U : Set (baseSuccessor p G).Point) (hUC : U ⊆ C)
    (h : ((baseSuccessor p G).weakRows (fiberIndex p G i j), U) ∈
      wolfeFamily (baseSuccessor p G).pointAtomicModel ε
        (range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j))) α) :
    ∃ b : Bool, (G.weakRows j, fiberPoint p G i b ⁻¹' U) ∈
      wolfeFamily G.pointAtomicModel δ (range G.weakRows) α := by
  apply wolfe_positive_mixture_pullback G.pointAtomicModel (baseSuccessor p G).pointAtomicModel
    (alspach_countable_compact_scattered G.Point) G.rows.row
    (fun j => (baseSuccessor p G).rows.row (fiberIndex p G i j))
    (fiberPoint p G i) (fun b => alspachCompactGraftAttach_continuous _ _ _ _)
    G.weakRows_continuous
    (((baseSuccessor p G).weakRows_isClosedEmbedding.isEmbedding).comp
      (alspachCompactGraftAttach_isClosedEmbedding id (fun _ : K => G.Index)
        (fun _ => G.rows.index) i).isEmbedding)
    C hselect α j U hUC h

theorem fiber_wolfe_same_threshold {ε : ℝ} (i : K) (α : Ordinal)
    (j : G.Index) (U : Set (baseSuccessor p G).Point)
    (h : ((baseSuccessor p G).weakRows (fiberIndex p G i j), U) ∈
      wolfeFamily (baseSuccessor p G).pointAtomicModel ε
        (range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j))) α) :
    ∃ b : Bool, (G.weakRows j, fiberPoint p G i b ⁻¹' U) ∈
      wolfeFamily G.pointAtomicModel ε (range G.weakRows) α := by
  apply fiber_wolfe_pullback p G i univ ?_ α j U (subset_univ U) h
  intro j U _ _ hm
  change ε ≤ (((AlspachPointedRows.base p).topologicalSuccessor G.rows).row
    (AlspachPointedRows.baseIndexAttach p G.rows i j)).mass U at hm
  rw [AlspachPointedRows.baseSuccessor_mass_attach p G.rows i j U] at hm
  by_cases ht : ε ≤ (G.rows.row j).mass (fiberPoint p G i true ⁻¹' U)
  · exact ⟨true, ht⟩
  · refine ⟨false, ?_⟩
    change ε ≤ (G.rows.row j).mass (AlspachPointedRows.baseAttach p G.rows p i ⁻¹' U)
    change ¬ ε ≤ (G.rows.row j).mass (AlspachPointedRows.baseAttach p G.rows i i ⁻¹' U) at ht
    linarith

theorem fiber_wolfe_doubled_threshold {ε : ℝ}
    (C : Set (baseSuccessor p G).Point) (hC : IsClosed C)
    (hp : alspachGraftBase _ _ p ∉ C) :
    ∃ s : Finset K, ∀ i ∉ s, ∀ α : Ordinal, ∀ j : G.Index,
      ∀ U : Set (baseSuccessor p G).Point, U ⊆ C →
      ((baseSuccessor p G).weakRows (fiberIndex p G i j), U) ∈
        wolfeFamily (baseSuccessor p G).pointAtomicModel ε
          (range (fun j => (baseSuccessor p G).weakRows (fiberIndex p G i j))) α →
      ∃ b : Bool, (G.weakRows j, fiberPoint p G i b ⁻¹' U) ∈
        wolfeFamily G.pointAtomicModel (2 * ε) (range G.weakRows) α := by
  obtain ⟨s, hs⟩ := AlspachPointedRows.baseSuccessor_mass_doubling_attach p G.rows C hC hp
  refine ⟨s, ?_⟩
  intro i hi α j U hUC h
  apply fiber_wolfe_pullback p G i C ?_ α j U hUC h
  intro j V _ hVC hm
  change ε ≤ (((AlspachPointedRows.base p).topologicalSuccessor G.rows).row
    (AlspachPointedRows.baseIndexAttach p G.rows i j)).mass V at hm
  rw [hs i hi j V hVC] at hm
  refine ⟨true, ?_⟩
  change 2 * ε ≤ (G.rows.row j).mass (AlspachPointedRows.baseAttach p G.rows i i ⁻¹' V)
  linarith

end AlspachCompactRows
end Posets
