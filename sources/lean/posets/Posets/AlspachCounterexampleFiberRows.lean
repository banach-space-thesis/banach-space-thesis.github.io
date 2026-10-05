import Posets.AlspachCounterexampleWeakRows
import Posets.AlspachCounterexampleSuccessorMass
import Posets.WolfeLocalization

/-! The completed row spines are embedded copies of the preceding row
family. Their measures are exactly the two continuous push-forwards used
in the positive-mixture step. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
namespace Posets
namespace AlspachPointedRows
variable {𝕜 K X J : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace J]
  [CompactSpace X] [T2Space X] [CompactSpace J] [T2Space J]
variable (p : K) (G : AlspachPointedRows 𝕜 X J)

abbrev baseIndexAttach (i : K) : J → (base (𝕜 := 𝕜) p).SuccessorIndexGraft G :=
  alspachCompactGraftAttach id (fun _ : K => J) (fun _ => G.index) i

theorem baseSuccessor_mass_base (i : K)
    (U : Set ((base (𝕜 := 𝕜) p).SuccessorPointGraft G)) :
    (((base (𝕜 := 𝕜) p).topologicalSuccessor G).row
      (alspachGraftBase _ _ i)).mass U =
      (1 / 2 : ℝ) * ((if alspachGraftBase _ _ i ∈ U then 1 else 0) +
        (if alspachGraftBase _ _ p ∈ U then 1 else 0)) := by
  change (((alspachBaseRow p i).map Sum.inl).map
    ((base p).successorPointEquiv G)).mass U = _
  simp only [AlspachProbability.mass_map]
  exact alspachBaseRow_mass p i _

theorem baseSuccessor_mass_attach (i : K) (j : J)
    (U : Set ((base (𝕜 := 𝕜) p).SuccessorPointGraft G)) :
    (((base (𝕜 := 𝕜) p).topologicalSuccessor G).row (baseIndexAttach p G i j)).mass U =
      (1 / 2 : ℝ) * ((G.row j).mass (baseAttach p G i i ⁻¹' U) +
        (G.row j).mass (baseAttach p G p i ⁻¹' U)) := by
  by_cases hj : j = G.index
  · subst j
    simp only [baseIndexAttach, alspachCompactGraftAttach_root]
    rw [baseSuccessor_mass_base, G.row_root]
    simp only [AlspachProbability.mass, mem_preimage, baseAttach,
      alspachCompactGraftAttach_root, id_eq]
  · rw [baseIndexAttach, alspachCompactGraftAttach_nonroot id (fun _ : K => J)
      (fun _ => G.index) i j hj]
    exact baseSuccessor_mass_spine p G i ⟨j, hj⟩ U

theorem baseSuccessor_mass_doubling_attach [CompactSpace K] [T2Space K]
    (C : Set ((base (𝕜 := 𝕜) p).SuccessorPointGraft G)) (hC : IsClosed C)
    (hp : alspachGraftBase _ _ p ∉ C) :
    ∃ s : Finset K, ∀ i ∉ s, ∀ j : J, ∀ U ⊆ C,
      (((base (𝕜 := 𝕜) p).topologicalSuccessor G).row (baseIndexAttach p G i j)).mass U =
        (1 / 2 : ℝ) * (G.row j).mass (baseAttach p G i i ⁻¹' U) := by
  obtain ⟨s, hs⟩ := baseSuccessor_mass_doubling p G C hC hp
  refine ⟨s, ?_⟩
  intro i hi j U hUC
  by_cases hj : j = G.index
  · subst j
    rw [baseSuccessor_mass_attach, G.row_root]
    have he : alspachGraftBase Prod.fst (fun _ : K × K => {x : X // x ≠ G.point}) p ∉ U :=
      fun h => hp (hUC h)
    simp only [AlspachProbability.mass, mem_preimage, baseAttach,
      alspachCompactGraftAttach_root, he, if_false, add_zero]
  · rw [baseIndexAttach, alspachCompactGraftAttach_nonroot id (fun _ : K => J)
      (fun _ => G.index) i j hj]
    exact hs i hi ⟨j, hj⟩ U hUC

end AlspachPointedRows

theorem alspach_wolfe_localize_parameter {𝕜 K P : Type*} [RCLike 𝕜]
    [TopologicalSpace K] [TopologicalSpace P]
    (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (r : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hr : IsEmbedding r)
    (A U : Set P) (hU : IsOpen U) (p : P) (hp : p ∈ U)
    (G : Set K) (α : Ordinal)
    (h : (r p, G) ∈ wolfeFamily M ε (r '' A) α) :
    (r p, G) ∈ wolfeFamily M ε (r '' (A ∩ U)) α := by
  obtain ⟨W, hW, he⟩ := hr.isInducing.isOpen_iff.mp hU
  have hpW : r p ∈ W := by rw [← he] at hp; exact hp
  have hh := wolfeFamily_localize_measures M ε (r '' A) α (r p, G) h W hW hpW
  apply wolfeFamily_mono M le_rfl _ α hh
  rintro μ ⟨⟨q, hq, rfl⟩, hqW⟩
  exact ⟨q, ⟨hq, by rw [← he]; exact hqW⟩, rfl⟩

end Posets
