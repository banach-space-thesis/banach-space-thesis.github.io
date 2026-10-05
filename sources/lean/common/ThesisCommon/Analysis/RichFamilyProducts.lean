import ThesisCommon.Analysis.RichFamilies
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.Normed.Operator.Basic

/-! Product and operator-image facts for the actual closures used in rich
families of pairs of subspaces. -/
noncomputable section
open Set Topology
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem richChainClosure_prod (V : ℕ → Submodule ℝ E) (W : ℕ → Submodule ℝ F)
    (hV : Monotone V) (hW : Monotone W) :
    richChainClosure (fun n => (V n).prod (W n)) =
      (richChainClosure V).prod (richChainClosure W) := by
  have hprod : Monotone (fun n => (V n).prod (W n)) := by
    intro i j hij p hp
    exact ⟨hV hij hp.1, hW hij hp.2⟩
  apply SetLike.coe_injective
  rw [richChainClosure_coe _ hprod]
  change closure (⋃ n, ((V n).prod (W n) : Set (E × F))) =
    (richChainClosure V : Set E) ×ˢ (richChainClosure W : Set F)
  rw [
    richChainClosure_coe V hV, richChainClosure_coe W hW, ← closure_prod_eq]
  congr 1
  ext p
  simp only [mem_iUnion, Submodule.mem_prod, mem_prod]
  constructor
  · rintro ⟨n, hx, hy⟩
    exact ⟨⟨n, hx⟩, ⟨n, hy⟩⟩
  · rintro ⟨⟨i, hx⟩, ⟨j, hy⟩⟩
    exact ⟨max i j, hV (le_max_left i j) hx, hW (le_max_right i j) hy⟩

theorem continuousLinearMap_maps_richChainClosure (S : E →L[ℝ] F)
    (V : ℕ → Submodule ℝ E) (W : ℕ → Submodule ℝ F) (hV : Monotone V)
    (hmap : ∀ n, ∀ f ∈ V n, S f ∈ W n) :
    ∀ f ∈ richChainClosure V, S f ∈ richChainClosure W := by
  intro f hf
  change f ∈ (richChainClosure V : Set E) at hf
  rw [richChainClosure_coe V hV] at hf
  apply closure_minimal _
    ((Submodule.isClosed_topologicalClosure (⨆ n, W n)).preimage S.continuous) hf
  intro g hg
  obtain ⟨n, hn⟩ := mem_iUnion.mp hg
  exact ((le_iSup W n).trans (Submodule.le_topologicalClosure _)) (hmap n g hn)

end ThesisCommon
