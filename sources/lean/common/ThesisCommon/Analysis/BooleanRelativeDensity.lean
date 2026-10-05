import ThesisCommon.Analysis.BooleanDensityHomogeneity
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Topology.MetricSpace.Isometry

/-! The genuine nowhere-density consequence of cardinal homogeneity.  A
subalgebra of strictly smaller density cannot generate all fragments in any
nonzero principal ideal of a homogeneous element.  In a metric algebra this
gives an actual positive distance from one fragment to every restricted
subalgebra element. -/
noncomputable section
open Set
namespace ThesisCommon
universe u

theorem topologicalDensity_le_of_continuous_denseRange {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (hfd : DenseRange f) :
    topologicalDensity Y ≤ topologicalDensity X := by
  obtain ⟨s, hs, hcard⟩ := exists_dense_card_eq_topologicalDensity X
  calc
    topologicalDensity Y ≤ Cardinal.mk (f '' s) :=
      topologicalDensity_le_card_of_dense (hfd.dense_image hf hs)
    _ ≤ Cardinal.mk s := Cardinal.mk_image_le
    _ = topologicalDensity X := hcard

theorem homogeneous_not_denseRange_restricted_subalgebra {B : Type u}
    [BooleanAlgebra B] [TopologicalSpace B] [ContinuousInf B]
    {a : B} (ha : IsDensityHomogeneous a) (S : BooleanSubalgebra B)
    (hS : topologicalDensity S < principalDensity a)
    {b : B} (hb : b ≠ ⊥) (hba : b ≤ a) :
    ¬ DenseRange (fun s : S => (⟨s.val ⊓ b, inf_le_right⟩ : Iic b)) := by
  intro hd
  have hc : Continuous (fun s : S => (⟨s.val ⊓ b, inf_le_right⟩ : Iic b)) :=
    (continuous_subtype_val.inf continuous_const).subtype_mk _
  have hle := topologicalDensity_le_of_continuous_denseRange hc hd
  change principalDensity b ≤ topologicalDensity S at hle
  rw [ha.2 b hb hba] at hle
  exact hS.not_ge hle

theorem homogeneous_exists_positive_distance_from_subalgebra {B : Type u}
    [BooleanAlgebra B] [MetricSpace B] [ContinuousInf B]
    {a : B} (ha : IsDensityHomogeneous a) (S : BooleanSubalgebra B)
    (hS : topologicalDensity S < principalDensity a)
    {b : B} (hb : b ≠ ⊥) (hba : b ≤ a) :
    ∃ c : B, c ≤ b ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ s : S, ε ≤ dist c (s.val ⊓ b) := by
  have hn := homogeneous_not_denseRange_restricted_subalgebra ha S hS hb hba
  change ¬ ∀ c : Iic b, c ∈ closure
    (range (fun s : S => (⟨s.val ⊓ b, inf_le_right⟩ : Iic b))) at hn
  push_neg at hn
  obtain ⟨c, hc⟩ := hn
  rw [Metric.mem_closure_iff] at hc
  push_neg at hc
  obtain ⟨ε, hε, hsep⟩ := hc
  refine ⟨c.val, c.property, ε, hε, ?_⟩
  intro s
  exact hsep _ ⟨s, rfl⟩

end ThesisCommon
