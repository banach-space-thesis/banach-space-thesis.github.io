import ThesisCommon.Analysis.JamesTreeMaskLimits

/-! Norm-one initial-level projections converging strongly to the identity
for both recorded James-tree segment conventions. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def dyadicInitialLevels (N : ℕ) : Set DyadicTreeNode := {t | t.length ≤ N}

theorem literalJamesTreeMaskClosed_levels (N : ℕ) :
    JamesTreeMaskClosed literalTreeSegmentFamily (dyadicInitialLevels N) := by
  intro A hA hne
  refine ⟨hne, ?_⟩
  intro s hs t ht
  exact hA.2 s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

theorem consecutiveJamesTreeMaskClosed_levels (N : ℕ) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily (dyadicInitialLevels N) := by
  intro A hA hne
  refine ⟨literalJamesTreeMaskClosed_levels N A hA.1 hne, ?_⟩
  intro s hs t ht v hsv hvt
  obtain ⟨hsA, _⟩ := Finset.mem_filter.mp hs
  obtain ⟨htA, htN⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hA.2 s hsA t htA v hsv hvt, hvt.length_le.trans htN⟩

abbrev literalJamesTreeLevelProjection {𝕜 : Type*} [RCLike 𝕜]
    (p : BanachExponent) (N : ℕ) : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜]
      LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeMask (dyadicInitialLevels N) (literalJamesTreeMaskClosed_levels N)

abbrev consecutiveJamesTreeLevelProjection {𝕜 : Type*} [RCLike 𝕜]
    (p : BanachExponent) (N : ℕ) : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜]
      ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeMask (dyadicInitialLevels N) (consecutiveJamesTreeMaskClosed_levels N)

theorem literalJamesTreeLevelProjection_norm {𝕜 : Type*} [RCLike 𝕜]
    (p : BanachExponent) (N : ℕ) :
    ‖literalJamesTreeLevelProjection (𝕜 := 𝕜) p N‖ = 1 :=
  norm_jamesTreeMask_eq_one _ _ ⟨[], Nat.zero_le N⟩

theorem consecutiveJamesTreeLevelProjection_norm {𝕜 : Type*} [RCLike 𝕜]
    (p : BanachExponent) (N : ℕ) :
    ‖consecutiveJamesTreeLevelProjection (𝕜 := 𝕜) p N‖ = 1 :=
  norm_jamesTreeMask_eq_one _ _ ⟨[], Nat.zero_le N⟩

theorem literalJamesTreeLevelProjection_tendsto {𝕜 : Type*} [RCLike 𝕜]
    (p : BanachExponent) (x : LiteralChainJamesTreeSpace 𝕜 p) :
    Tendsto (fun N => literalJamesTreeLevelProjection p N x) atTop (𝓝 x) :=
  jamesTreeMask_tendsto _ _ (fun t => eventually_ge_atTop t.length) x

theorem consecutiveJamesTreeLevelProjection_tendsto {𝕜 : Type*} [RCLike 𝕜]
    (p : BanachExponent) (x : ConsecutiveJamesTreeSpace 𝕜 p) :
    Tendsto (fun N => consecutiveJamesTreeLevelProjection p N x) atTop (𝓝 x) :=
  jamesTreeMask_tendsto _ _ (fun t => eventually_ge_atTop t.length) x

end ThesisCommon
