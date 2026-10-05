import Posets.WolfePreservationNecessaryPullback
import ThesisCommon.Analysis.OrdinalExtension

/-! A closed relation with at most one source point above each target point
is a continuous map on its compact projection. On an ordinal target that map
extends using the proved retraction onto a nonempty closed subset. This proves
the one-fibre case of the support-selection argument, with no rank loss. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u v
namespace Posets

theorem wolfe_closed_single_relation_map
    {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
    {R : Set (K × L)} (hR : IsClosed R)
    (hunique : ∀ y x z, (y, x) ∈ R → (y, z) ∈ R → x = z) :
    ∃ π : (Prod.fst '' R) → L, Continuous π ∧
      ∀ y : (Prod.fst '' R), (y.val, π y) ∈ R := by
  classical
  have hex (y : (Prod.fst '' R)) : ∃ x : L, (y.val, x) ∈ R := by
    obtain ⟨⟨z, x⟩, hz, he⟩ := y.property
    exact ⟨x, he ▸ hz⟩
  let π : (Prod.fst '' R) → L := fun y => (hex y).choose
  have hπ (y : (Prod.fst '' R)) : (y.val, π y) ∈ R := (hex y).choose_spec
  refine ⟨π, ?_, hπ⟩
  apply continuous_iff_isClosed.mpr
  intro B hB
  have heq : π ⁻¹' B = Subtype.val ⁻¹' (Prod.fst '' (R ∩ Prod.snd ⁻¹' B)) := by
    ext y
    constructor
    · intro hy
      exact ⟨(y.val, π y), ⟨hπ y, hy⟩, rfl⟩
    · rintro ⟨⟨z, x⟩, ⟨hz, hx⟩, he⟩
      have hzx : (y.val, x) ∈ R := he ▸ hz
      change π y ∈ B
      rwa [hunique y.val (π y) x (hπ y) hzx]
  rw [heq]
  exact ((hR.inter (hB.preimage continuous_snd)).isCompact.image continuous_fst).isClosed.preimage
    continuous_subtype_val

theorem wolfe_closed_single_relation_extension
    {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
    {R : Set (K × L)} (hR : IsClosed R)
    (hunique : ∀ y x z, (y, x) ∈ R → (y, z) ∈ R → x = z)
    (r : K → (Prod.fst '' R)) (hr : Continuous r)
    (hretract : ∀ y : (Prod.fst '' R), r y.val = y) :
    ∃ π : K → L, Continuous π ∧ ∀ y x, (y, x) ∈ R → π y = x := by
  obtain ⟨π, hπ, hgraph⟩ := wolfe_closed_single_relation_map hR hunique
  refine ⟨π ∘ r, hπ.comp hr, ?_⟩
  intro y x hy
  let z : (Prod.fst '' R) := ⟨y, ⟨(y, x), hy, rfl⟩⟩
  have heq : r y = z := hretract z
  change π (r y) = x
  rw [heq]
  exact hunique y (π z) x (hgraph z) hy

theorem wolfe_ordinal_closed_single_relation_extension
    {κ : Ordinal.{v}} {L : Type*} [TopologicalSpace L]
    [CompactSpace L] [T2Space L]
    {R : Set (OrdinalInterval κ × L)} (hR : IsClosed R) (hne : R.Nonempty)
    (hunique : ∀ y x z, (y, x) ∈ R → (y, z) ∈ R → x = z) :
    ∃ π : OrdinalInterval κ → L, Continuous π ∧ ∀ y x, (y, x) ∈ R → π y = x := by
  let F := Prod.fst '' R
  have hF : IsClosed F := (hR.isCompact.image continuous_fst).isClosed
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  letI : Nonempty F := (hne.image Prod.fst).to_subtype
  exact wolfe_closed_single_relation_extension hR hunique
    (ordinalIntervalRetraction F) (ordinalIntervalRetraction F).continuous
    (ordinalIntervalRetraction_apply F)

theorem wolfe_ordinal_single_relation_nonempty
    {𝕜 L : Type*} [RCLike 𝕜] [MetricSpace L] [CompactSpace L] [Countable L]
    {κ : Ordinal.{v}} (M : JLMS.AtomicDualModel 𝕜 (OrdinalInterval κ))
    {R : Set (OrdinalInterval κ × L)} (hR : IsClosed R) (hne : R.Nonempty)
    (hunique : ∀ y x z, (y, x) ∈ R → (y, z) ∈ R → x = z)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 (OrdinalInterval κ))) (hμ : Continuous μ)
    {A : Set L} (hA : IsClosed A) {ε : ℝ}
    (hmass : ∀ x ∈ A, ε ≤ wolfeMass M (μ x) {y | (y, x) ∈ R})
    {α : Ordinal.{u}} (hc : α.card ≤ Cardinal.aleph0)
    (hrank : (ordinalDerived A α).Nonempty) :
    (wolfeFamily M ε (μ '' A) α).Nonempty := by
  obtain ⟨π, hπ, hgraph⟩ := wolfe_ordinal_closed_single_relation_extension hR hne hunique
  apply wolfePullback_nonempty_of_ordinalDerived M π hπ μ hμ hA _ hc hrank
  intro x hx
  exact (hmass x hx).trans (wolfeMass_mono M (μ x) fun y hy => hgraph y x hy)

end Posets
