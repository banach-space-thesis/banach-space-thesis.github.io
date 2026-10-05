import Posets.CountableOrdinalPFPCanonicalChildren
import Posets.WolfeRankedFamily

/-! The canonical ordinal tower consists of isolated points of successive
Cantor--Bendixson levels, together with their actual ceiling fibers. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

def ordinalTowerLevel (θ α : Ordinal.{u}) : Set Ordinal.{u} :=
  ordinalDerived (Iic θ) α

theorem ordinalTowerLevel_isCompact (θ α : Ordinal.{u}) :
    IsCompact (ordinalTowerLevel θ α) := by
  apply isCompact_ordinalDerived
  have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
  rw [← heq]
  exact isCompact_Icc

theorem ordinalTowerLevel_antitone (θ : Ordinal.{u}) : Antitone (ordinalTowerLevel θ) :=
  ordinalDerived_antitone isClosed_Iic

structure OrdinalTowerNode (θ γ : Ordinal.{u}) where
  level : Iic γ
  point : Iic θ
  mem_level : point.val ∈ ordinalTowerLevel θ level.val
  isolated : IsOpen ({⟨point.val, mem_level⟩} : Set (ordinalTowerLevel θ level.val))

namespace OrdinalTowerNode
variable {θ γ : Ordinal.{u}}

def cell (p : OrdinalTowerNode θ γ) : Set (Iic θ) :=
  ordinalTowerCell θ (ordinalTowerLevel θ p.level) p.point

theorem point_mem_cell (p : OrdinalTowerNode θ γ) : p.point ∈ p.cell :=
  ordinalCeiling_eq_of_mem p.mem_level

theorem cell_nonempty (p : OrdinalTowerNode θ γ) : p.cell.Nonempty := ⟨_, p.point_mem_cell⟩

theorem cell_isClopen (p : OrdinalTowerNode θ γ) : IsClopen p.cell :=
  ordinalTowerCell_isClopen θ (ordinalTowerLevel_isCompact θ p.level)
    ⟨_, p.mem_level⟩ ⟨_, p.mem_level⟩ p.isolated

theorem cell_isCompact (p : OrdinalTowerNode θ γ) : IsCompact p.cell :=
  ordinalTowerCell_isCompact θ (ordinalTowerLevel_isCompact θ p.level)
    ⟨_, p.mem_level⟩ ⟨_, p.mem_level⟩ p.isolated

theorem cell_laminar (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p q : OrdinalTowerNode θ γ) :
    p.cell ⊆ q.cell ∨ q.cell ⊆ p.cell ∨ Disjoint p.cell q.cell := by
  have hθn (r : OrdinalTowerNode θ γ) : θ ∈ ordinalTowerLevel θ r.level :=
    ordinalTowerLevel_antitone θ r.level.property hθ
  rcases le_total p.level.val q.level.val with hpq | hqp
  · rcases ordinalTowerCell_nested_or_disjoint θ
      (ordinalTowerLevel_isCompact θ p.level) (ordinalTowerLevel_isCompact θ q.level)
      (ordinalTowerLevel_antitone θ hpq) (hθn q) p.point q.point with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases ordinalTowerCell_nested_or_disjoint θ
      (ordinalTowerLevel_isCompact θ q.level) (ordinalTowerLevel_isCompact θ p.level)
      (ordinalTowerLevel_antitone θ hqp) (hθn p) q.point p.point with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)

def toWolfeNode {𝕜 : Type*} [RCLike 𝕜]
    (μ : Iic θ → WeakDual 𝕜 (JLMS.CZero 𝕜 (Iic θ)))
    (p : OrdinalTowerNode θ γ) : WolfeNode 𝕜 (Iic θ) := (μ p.point, p.cell)

end OrdinalTowerNode
end Posets
