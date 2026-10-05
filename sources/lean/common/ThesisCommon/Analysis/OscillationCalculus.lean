import Mathlib.Analysis.Oscillation
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Normed.Group.Uniform

/-! Neighborhood-diameter oscillation is upper semicontinuous and
subadditive. These facts do not require continuity of the original map. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {E F : Type*} [TopologicalSpace E] [PseudoEMetricSpace F]

theorem oscillation_eq_iInf_image (f : E → F) (x : E) :
    oscillation f x = ⨅ U ∈ 𝓝 x, EMetric.diam (f '' U) := by
  apply le_antisymm
  · apply le_iInf
    intro U
    apply le_iInf
    intro hU
    exact biInf_le EMetric.diam (Filter.image_mem_map hU)
  · apply le_iInf
    intro S
    apply le_iInf
    intro hS
    have hpre : f ⁻¹' S ∈ 𝓝 x := hS
    apply (show (⨅ U ∈ 𝓝 x, EMetric.diam (f '' U)) ≤
        EMetric.diam (f '' (f ⁻¹' S)) from
      iInf_le_of_le (f ⁻¹' S) (iInf_le_of_le hpre le_rfl)).trans
    exact EMetric.diam_mono (Set.image_preimage_subset f S)

theorem upperSemicontinuous_oscillation (f : E → F) : UpperSemicontinuous (oscillation f) := by
  intro x b hb
  rw [oscillation, iInf_lt_iff] at hb
  obtain ⟨S, hS⟩ := hb
  rw [iInf_lt_iff] at hS
  obtain ⟨hS, hdiam⟩ := hS
  obtain ⟨U, hUS, hU, hx⟩ := mem_nhds_iff.1 hS
  filter_upwards [hU.mem_nhds hx] with y hy
  apply lt_of_le_of_lt _ hdiam
  have hyS : S ∈ Filter.map f (𝓝 y) :=
    (show f ⁻¹' S ∈ 𝓝 y from mem_of_superset (hU.mem_nhds hy) hUS)
  exact biInf_le EMetric.diam hyS

theorem oscillation_add_le {Y : Type*} [SeminormedAddCommGroup Y]
    (f g : E → Y) (x : E) :
    oscillation (fun t => f t+g t) x ≤ oscillation f x + oscillation g x := by
  rw [oscillation_eq_iInf_image f, oscillation_eq_iInf_image g]
  apply ENNReal.le_iInf₂_add_iInf₂
  intro U hU V hV
  apply (show oscillation (fun t => f t+g t) x ≤
    EMetric.diam ((fun t => f t+g t) '' (U ∩ V)) from
      (oscillation_eq_iInf_image _ x).trans_le
        (iInf_le_of_le (U ∩ V) (iInf_le_of_le (inter_mem hU hV) le_rfl))).trans
  apply EMetric.diam_image_le_iff.2
  intro a ha b hb
  exact (edist_add_add_le (f a) (g a) (f b) (g b)).trans
    (add_le_add (EMetric.edist_le_diam_of_mem (Set.mem_image_of_mem f ha.1) (Set.mem_image_of_mem f hb.1))
      (EMetric.edist_le_diam_of_mem (Set.mem_image_of_mem g ha.2) (Set.mem_image_of_mem g hb.2)))

end ThesisCommon
