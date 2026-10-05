import JLMS.BlockComposition
import JLMS.DualAsymptoticRadius

/-!
# Infimum of asymptotic radii under normalized blocking

The infimum is nonnegative and can be approached by a further block system.
Further blocking can only increase this infimum, because block composition
is again normalized. These are the numerical ingredients of the nested
stabilization used in the Hagler–Johnson argument.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def blockRadiusInfimum (f : ℕ → (X →L[𝕜] 𝕜)) : ℝ :=
  sInf {r : ℝ | ∃ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = r}

theorem blockRadius_set_nonempty (f : ℕ → (X →L[𝕜] 𝕜)) :
    ({r : ℝ | ∃ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = r} : Set ℝ).Nonempty :=
  ⟨dualAsymptoticRadius ((NormalizedBlockSystem.units (𝕜 := 𝕜)).applyDual f),
    NormalizedBlockSystem.units, rfl⟩

theorem blockRadius_set_bddBelow (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    BddBelow {r : ℝ | ∃ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨b, rfl⟩
  exact dualAsymptoticRadius_nonneg _ hC (b.norm_applyDual_le f hf)

theorem blockRadiusInfimum_nonneg (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) : 0 ≤ blockRadiusInfimum f := by
  apply le_csInf (s := {r : ℝ | ∃ b : NormalizedBlockSystem 𝕜,
    dualAsymptoticRadius (b.applyDual f) = r}) (blockRadius_set_nonempty f)
  rintro r ⟨b, rfl⟩
  exact dualAsymptoticRadius_nonneg _ hC (b.norm_applyDual_le f hf)

theorem blockRadiusInfimum_le_block (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (b : NormalizedBlockSystem 𝕜) :
    blockRadiusInfimum f ≤ dualAsymptoticRadius (b.applyDual f) :=
  csInf_le (blockRadius_set_bddBelow f hC hf) ⟨b, rfl⟩

theorem blockRadiusInfimum_le_radius (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) : blockRadiusInfimum f ≤ dualAsymptoticRadius f := by
  have h := blockRadiusInfimum_le_block f hC hf (NormalizedBlockSystem.units (𝕜 := 𝕜))
  have heq : (NormalizedBlockSystem.units (𝕜 := 𝕜)).applyDual f = f := by
    funext n; exact NormalizedBlockSystem.units_applyDual f n
  simpa only [heq] using h

theorem exists_block_radius_lt (f : ℕ → (X →L[𝕜] 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : NormalizedBlockSystem 𝕜,
      dualAsymptoticRadius (b.applyDual f) < blockRadiusInfimum f + ε := by
  obtain ⟨r, ⟨b, hr⟩, hsmall⟩ := exists_lt_of_csInf_lt (blockRadius_set_nonempty f)
    (show blockRadiusInfimum f < blockRadiusInfimum f + ε by linarith)
  exact ⟨b, hr ▸ hsmall⟩

theorem blockRadiusInfimum_blocks_ge (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (b : NormalizedBlockSystem 𝕜) :
    blockRadiusInfimum f ≤ blockRadiusInfimum (b.applyDual f) := by
  apply le_csInf (s := {r : ℝ | ∃ c : NormalizedBlockSystem 𝕜,
    dualAsymptoticRadius (c.applyDual (b.applyDual f)) = r}) (blockRadius_set_nonempty _)
  rintro r ⟨c, rfl⟩
  have heq : (b.compose c).applyDual f = c.applyDual (b.applyDual f) := by
    funext n; exact b.compose_applyDual c f n
  rw [← heq]
  exact blockRadiusInfimum_le_block f hC hf _

end JLMS
