import Mathlib.Topology.OpenPartialHomeomorph
import Mathlib.Topology.ContinuousOn

/-! Actual local two-sided inverses with the derived local continuity data
determine an actual open partial homeomorphism. The construction shrinks both
neighborhoods explicitly; it does not assume a local chart in its premises. -/

noncomputable section
namespace BanachIsometric
open Set Filter
open scoped Topology

theorem exists_openPartialHomeomorph_of_eventual_inverses
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (g : Y → X) (x : X) (y : Y) (hfx : f x = y) (hgy : g y = x)
    (hf : Continuous f) {N : Set Y} (hN : N ∈ 𝓝 y) (hg : ContinuousOn g N)
    (hleft : ∀ᶠ z in 𝓝 x, g (f z) = z) (hright : ∀ᶠ z in 𝓝 y, f (g z) = z) :
    ∃ e : OpenPartialHomeomorph X Y,
      x ∈ e.source ∧ y ∈ e.target ∧ (e : X → Y) = f ∧ (e.symm : Y → X) = g := by
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hleft
  obtain ⟨V, hVsub, hV, hyV⟩ := mem_nhds_iff.mp (Filter.inter_mem hN hright)
  have hgV : ContinuousOn g V := hg.mono (fun _ hz => (hVsub hz).1)
  let S := U ∩ f ⁻¹' V
  let T := V ∩ g ⁻¹' U
  let e : OpenPartialHomeomorph X Y := {
    toFun := f
    invFun := g
    source := S
    target := T
    map_source' := by
      intro z hz
      refine ⟨hz.2, ?_⟩
      change g (f z) ∈ U
      rw [hUsub hz.1]
      exact hz.1
    map_target' := by
      intro z hz
      refine ⟨hz.2, ?_⟩
      change f (g z) ∈ V
      rw [(hVsub hz.1).2]
      exact hz.1
    left_inv' := fun z hz => hUsub hz.1
    right_inv' := fun z hz => (hVsub hz.1).2
    open_source := hU.inter (hV.preimage hf)
    open_target := hgV.isOpen_inter_preimage hV hU
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hgV.mono inter_subset_left }
  refine ⟨e, ⟨hxU, ?_⟩, ⟨hyV, ?_⟩, rfl, rfl⟩
  · change f x ∈ V
    rwa [hfx]
  · change g y ∈ U
    rwa [hgy]

end BanachIsometric
