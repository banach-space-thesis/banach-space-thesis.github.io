import Posets.TopologyStatements
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Metrizable.Urysohn

/-! Separability of C(K) forces a compact Hausdorff K to be metrizable.
A countable dense set of functions still separates points. -/

noncomputable section
open Set Topology TopologicalSpace ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem continuousMap_separates_points {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] {x y : K} (hxy : x ≠ y) :
    ∃ f : C(K, 𝕜), f x ≠ f y := by
  obtain ⟨g, hgx, hgy, _⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := x)) (isClosed_singleton (x := y))
    (Set.disjoint_singleton.mpr hxy)
  let f : C(K, 𝕜) := ⟨fun z => (g z : 𝕜), RCLike.continuous_ofReal.comp g.continuous⟩
  refine ⟨f, ?_⟩
  have hx : g x = 0 := hgx (Set.mem_singleton x)
  have hy : g y = 1 := hgy (Set.mem_singleton y)
  change (g x : 𝕜) ≠ (g y : 𝕜)
  simp [hx, hy]

theorem metrizable_of_separable_continuousMap (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [SeparableSpace C(K, 𝕜)] : MetrizableSpace K := by
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense C(K, 𝕜)
  letI : Countable D := hDcount.to_subtype
  let e : K → (D → 𝕜) := fun x f => f.val x
  have he : Continuous e := continuous_pi (fun f => f.val.continuous)
  have hinj : Function.Injective e := by
    intro x y hxy
    by_contra hne
    have hclosed : IsClosed {f : C(K, 𝕜) | f x = f y} :=
      isClosed_eq (continuous_eval_const x) (continuous_eval_const y)
    have hsub : D ⊆ {f : C(K, 𝕜) | f x = f y} := fun f hf =>
      congrFun hxy ⟨f, hf⟩
    have hall := closure_minimal hsub hclosed
    obtain ⟨f, hf⟩ := continuousMap_separates_points (𝕜 := 𝕜) hne
    apply hf
    exact hall (hDdense.closure_eq.symm ▸ Set.mem_univ f)
  exact (he.isClosedEmbedding hinj).isEmbedding.metrizableSpace

/-- Proposition 1.10 follows from the exact Section 3 results; metrizability
is derived, not added as a hypothesis on the compact space. -/
theorem proposition_1_10_of_section_3 (h33 : Corollary_3_3 𝕜)
    (h34 : Proposition_3_4 𝕜) : Proposition_1_10 𝕜 := by
  refine ⟨?_, h34.2⟩
  intro K _ _ _ _ hsep
  letI := hsep
  letI : MetrizableSpace K := metrizable_of_separable_continuousMap (𝕜 := 𝕜) K
  letI : MetricSpace K := metrizableSpaceMetric K
  exact h33 K

end Posets
