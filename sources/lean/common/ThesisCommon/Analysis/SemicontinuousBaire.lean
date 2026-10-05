import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! An upper semicontinuous extended-nonnegative-real function is
continuous on a dense G-delta subset of any Baire space. Remove the
frontiers of its countably many rational superlevel sets. -/
noncomputable section
open Filter Set Topology
open scoped ENNReal
namespace ThesisCommon
variable {E : Type*} [TopologicalSpace E] [BaireSpace E]

theorem upperSemicontinuous_ennreal_continuity_points {f : E → ℝ≥0∞}
    (hf : UpperSemicontinuous f) :
    ∃ D : Set E, IsGδ D ∧ Dense D ∧ ∀ x ∈ D, ContinuousAt f x := by
  let C : ℚ → Set E := fun q => {x | (Real.toNNReal (q : ℝ) : ℝ≥0∞) ≤ f x}
  have hC : ∀ q, IsClosed (C q) := fun q => hf.isClosed_preimage _
  let U : ℚ → Set E := fun q => (frontier (C q))ᶜ
  have hU : ∀ q, IsOpen (U q) := fun q => isClosed_frontier.isOpen_compl
  have hd : ∀ q, Dense (U q) := by
    intro q
    rw [dense_iff_closure_eq]
    change closure (frontier (C q))ᶜ = univ
    rw [closure_compl, interior_frontier (hC q), compl_empty]
  refine ⟨⋂ q, U q, IsGδ.iInter_of_isOpen hU,
    dense_iInter_of_isOpen hU hd, ?_⟩
  intro x hx
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨q, hq0, haq, hqx⟩ := ENNReal.lt_iff_exists_rat_btwn.1 ha
    have hxC : x ∈ C q := hqx.le
    have hxU : x ∉ frontier (C q) := mem_iInter.1 hx q
    have hxint : x ∈ interior (C q) := by
      by_contra hn
      exact hxU (by rw [(hC q).frontier_eq]; exact ⟨hxC, hn⟩)
    filter_upwards [isOpen_interior.mem_nhds hxint] with y hy
    exact haq.trans_le (interior_subset hy)
  · intro b hb
    exact hf x b hb

theorem upperSemicontinuous_ennreal_exists_continuity_point {f : E → ℝ≥0∞}
    (hf : UpperSemicontinuous f) {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ContinuousAt f x := by
  obtain ⟨D, hDG, hD, hc⟩ := upperSemicontinuous_ennreal_continuity_points hf
  obtain ⟨x, hxU, hxD⟩ := hD.inter_open_nonempty U hU hne
  exact ⟨x, hxU, hc x hxD⟩

end ThesisCommon
