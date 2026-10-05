import JFA.MrowkaTopology
import JLMS.Definitions

/-! Scatteredness of the actual Mrówka topology and its discrete amplification.
The predicate is the explicit isolated-point condition used by the checked
JLMS factorisation theorem. -/

noncomputable section
open TopologicalSpace Set
namespace JFA

theorem discrete_isScattered {D : Type*} [TopologicalSpace D] [DiscreteTopology D] :
    JLMS.IsScattered D := by
  intro s hs
  obtain ⟨x, hx⟩ := hs
  refine ⟨x, hx, {x}, isOpen_discrete _, ?_⟩
  ext p
  simp only [mem_inter_iff, mem_singleton_iff]
  exact ⟨And.right, fun h => ⟨h.symm ▸ hx, h⟩⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] Mrowka
variable {𝒜 : Set (Set ℕ)}
local instance : TopologicalSpace (Mrowka 𝒜) := mrowkaTopology 𝒜

theorem mrowka_isScattered : JLMS.IsScattered (Mrowka 𝒜) := by
  intro s hs
  by_cases hn : ∃ n : ℕ, Sum.inl n ∈ s
  · obtain ⟨n, hn⟩ := hn
    refine ⟨Sum.inl n, hn, {Sum.inl n}, mrowka_isOpen_singleton n, ?_⟩
    ext p
    simp only [mem_inter_iff, mem_singleton_iff]
    exact ⟨And.right, fun h => ⟨h.symm ▸ hn, h⟩⟩
  · obtain ⟨p, hp⟩ := hs
    cases p with
    | inl n => exact False.elim (hn ⟨n, hp⟩)
    | inr A =>
      refine ⟨Sum.inr A, hp, mrowkaNeighborhood 𝒜 A ∅,
        mrowka_isOpen_neighborhood A ∅, ?_⟩
      ext q
      cases q with
      | inl n =>
        have hn' : Sum.inl n ∉ s := fun h => hn ⟨n, h⟩
        simp only [mem_inter_iff, hn', false_and, mem_singleton_iff, Sum.inl_ne_inr]
      | inr B =>
        simp only [mem_inter_iff, mrowka_inr_mem, mem_singleton_iff, Sum.inr.injEq]
        exact ⟨And.right, fun h => ⟨h.symm ▸ hp, h⟩⟩

theorem discrete_prod_isScattered {D L : Type*}
    [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace L]
    (hL : JLMS.IsScattered L) : JLMS.IsScattered (D × L) := by
  intro s hs
  obtain ⟨⟨d, l⟩, hdl⟩ := hs
  let t : Set L := {x | (d, x) ∈ s}
  obtain ⟨x, hx, U, hU, htx⟩ := hL t ⟨l, hdl⟩
  have hxU : x ∈ U := by
    have hm : x ∈ t ∩ U := htx.symm ▸ mem_singleton x
    exact hm.2
  refine ⟨(d, x), hx, {d} ×ˢ U, (isOpen_discrete _).prod hU, ?_⟩
  ext p
  constructor
  · rintro ⟨hps, hpd, hpU⟩
    have hd : p.1 = d := hpd
    have hp : p.2 ∈ t ∩ U := ⟨by simpa only [t, mem_setOf_eq, ← hd, Prod.eta] using hps, hpU⟩
    have hpx : p.2 = x := mem_singleton_iff.mp (htx ▸ hp)
    exact Prod.ext hd hpx
  · intro hp
    have hpeq : p = (d, x) := hp
    subst p
    exact ⟨hx, mem_singleton _, hxU⟩

theorem amplifiedMrowka_isScattered : JLMS.IsScattered (ℕ × Mrowka 𝒜) :=
  discrete_prod_isScattered mrowka_isScattered

end JFA
