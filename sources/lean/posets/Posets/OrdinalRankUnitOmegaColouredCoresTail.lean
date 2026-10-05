import Posets.OrdinalRankUnitOmegaColouredCoresSource

/-! Removing the first selected block preserves the coloured cores and
their cross-mass estimate, and leaves every index positive. -/

noncomputable section
open Set Topology
universe u
namespace Posets

variable {𝕜 : Type*} [RCLike 𝕜] {ρ : Ordinal.{u}} {hρ : Ordinal.omega0 ≤ ρ}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRankUnitOmegaColouredCores

variable (F : OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ)

def tail : OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ where
  colour := F.colour
  index := fun i => F.index (i+1)
  strictMono := fun _ _ h => F.strictMono (Nat.add_lt_add_right h 1)
  band := fun i => F.band (i+1)
  core := fun i => F.core (i+1)
  compact := fun i => F.compact (i+1)
  leaf_closure := fun i => F.leaf_closure (i+1)
  block := fun i => F.block (i+1)
  rank := fun i => F.rank (i+1)
  cross := by
    intro i x hx
    apply lt_of_le_of_lt (wolfeMass_mono M _ ?_) (F.cross (i+1) x hx)
    intro y hy
    obtain ⟨j, hji, hyj⟩ := (mem_wolfeCrossUnion _ i y).mp hy
    exact (mem_wolfeCrossUnion _ (i+1) y).mpr ⟨j+1, by omega, hyj⟩

theorem tail_index_pos (i : ℕ) : 0 < F.tail.index i := by
  have h := F.strictMono.id_le (i+1)
  change i+1 ≤ F.index (i+1) at h
  change 0 < F.index (i+1)
  omega

theorem tail_target_start : 2 ≤ F.tail.index 0 + 1 := by
  have h := F.tail_index_pos 0
  omega

end OrdinalRankUnitOmegaColouredCores
end Posets

