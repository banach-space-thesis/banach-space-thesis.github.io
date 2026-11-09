import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Basic

/-!
# Local representatives for compact-group orbits

An orbit point close to the reference point has a representative close to the
group identity. This is a proved compactness fact, without a manifold or
quotient-metric assumption. It supplies the topological coverage step for the
explicit local orbit slice used in Lemma 2.1(iii).
-/

namespace BanachIsometric

open Set
open scoped Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousSMul G X]

/-- A neighbourhood of the identity covers an orbit-neighbourhood of the
reference point. Representatives are obtained by translating along the actual
stabiliser, not by assuming a local section of the orbit map. -/
theorem compactOrbit_local_representatives (x : X) (V : Set G)
    (hV : IsOpen V) (h1 : (1 : G) ∈ V) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, (∃ g : G, g • x = y) → ∃ g ∈ V, g • x = y := by
  let O : Set G := ⋃ h : MulAction.stabilizer G x, (fun g : G => g * h.val) ⁻¹' V
  have hO : IsOpen O :=
    isOpen_iUnion fun h => hV.preimage (continuous_id.mul continuous_const)
  have hfibre : ∀ g : G, g • x = x → g ∈ O := by
    intro g hg
    have hi : g⁻¹ • x = x := by
      calc
        g⁻¹ • x = g⁻¹ • (g • x) := congrArg (fun z => g⁻¹ • z) hg.symm
        _ = x := inv_smul_smul g x
    apply mem_iUnion.mpr
    refine ⟨⟨g⁻¹, hi⟩, ?_⟩
    simpa only [mem_preimage, mul_inv_cancel] using h1
  have hcompact : IsCompact ((fun g : G => g • x) '' Oᶜ) :=
    hO.isClosed_compl.isCompact.image (continuous_id.smul continuous_const)
  have hx : x ∉ (fun g : G => g • x) '' Oᶜ := by
    rintro ⟨g, hg, hfx⟩
    exact hg (hfibre g hfx)
  refine ⟨((fun g : G => g • x) '' Oᶜ)ᶜ, hcompact.isClosed.isOpen_compl, hx, ?_⟩
  intro y hy hOrbit
  obtain ⟨g, hgy⟩ := hOrbit
  have hgO : g ∈ O := by
    by_contra hg
    exact hy ⟨g, hg, hgy⟩
  obtain ⟨h, hh⟩ := mem_iUnion.mp hgO
  refine ⟨g * h.val, hh, ?_⟩
  rw [mul_smul, h.property, hgy]

end BanachIsometric
