import Posets.AlspachCounterexampleGraft
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Metrizable.Urysohn

/-! Countability makes every compact Hausdorff graft metrizable. The proof
embeds the space into a countable product of real intervals by functions
separating its ordered pairs of distinct points. -/

noncomputable section
open Set Topology TopologicalSpace
namespace Posets

theorem alspach_countable_compact_metrizable (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [Countable K] : MetrizableSpace K := by
  let P := {p : K × K // p.1 ≠ p.2}
  have hex (p : P) : ∃ f : C(K, ℝ), f p.val.1 = 0 ∧ f p.val.2 = 1 := by
    obtain ⟨f, hf, hg, _⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := p.val.1)) (isClosed_singleton (x := p.val.2))
      (disjoint_singleton.mpr p.property)
    exact ⟨f, hf (mem_singleton _), hg (mem_singleton _)⟩
  choose f hf hg using hex
  let g : K → (P → ℝ) := fun x p => f p x
  have hgc : Continuous g := continuous_pi fun p => (f p).continuous
  have hgi : Function.Injective g := by
    intro x y hxy
    by_contra hne
    let p : P := ⟨(x, y), hne⟩
    have he := congrFun hxy p
    change f p x = f p y at he
    rw [show f p x = 0 from hf p, show f p y = 1 from hg p] at he
    exact zero_ne_one he
  exact (hgc.isClosedEmbedding hgi).isEmbedding.metrizableSpace

end Posets

