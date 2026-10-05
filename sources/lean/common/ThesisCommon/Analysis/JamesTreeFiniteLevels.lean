import ThesisCommon.Analysis.JamesTreeFiniteMasks
import ThesisCommon.Analysis.JamesTreeLevels
import Mathlib.Data.Set.Finite.List

/-! Finite-dimensional initial-level ranges and their genuine dense
decomposition of both completed James-tree models. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem dyadicInitialLevels_finite (N : ℕ) : (dyadicInitialLevels N).Finite :=
  List.finite_length_le Bool N

def dyadicInitialFinset (N : ℕ) : Finset DyadicTreeNode := (dyadicInitialLevels_finite N).toFinset

@[simp] theorem coe_dyadicInitialFinset (N : ℕ) :
    (dyadicInitialFinset N : Set DyadicTreeNode) = dyadicInitialLevels N :=
  Set.Finite.coe_toFinset _

@[simp] theorem mem_dyadicInitialFinset (t : DyadicTreeNode) (N : ℕ) :
    t ∈ dyadicInitialFinset N ↔ t.length ≤ N := by
  change t ∈ (dyadicInitialFinset N : Set DyadicTreeNode) ↔ _
  rw [coe_dyadicInitialFinset]
  rfl

theorem jamesTreeLevelProjection_finite_sum (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicInitialLevels N))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeMask (dyadicInitialLevels N) hN x =
      ∑ t ∈ dyadicInitialFinset N, jamesTreeCoordinate t x • jamesTreeUnit t := by
  have hF : JamesTreeMaskClosed S (dyadicInitialFinset N : Set DyadicTreeNode) := by
    simpa only [coe_dyadicInitialFinset] using hN
  simpa only [coe_dyadicInitialFinset] using jamesTreeMask_finite_sum (dyadicInitialFinset N) hF x

theorem jamesTreeLevelProjection_range (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicInitialLevels N)) :
    LinearMap.range (jamesTreeMask (𝕜 := 𝕜) (p := p) (dyadicInitialLevels N) hN).toLinearMap =
      jamesTreeFiniteSpan (dyadicInitialFinset N) := by
  have hF : JamesTreeMaskClosed S (dyadicInitialFinset N : Set DyadicTreeNode) := by
    simpa only [coe_dyadicInitialFinset] using hN
  simpa only [coe_dyadicInitialFinset] using
    jamesTreeMask_range_eq_finiteSpan (𝕜 := 𝕜) (p := p) (dyadicInitialFinset N) hF

theorem jamesTreeLevelProjection_finiteDimensional (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicInitialLevels N)) :
    FiniteDimensional 𝕜
      (LinearMap.range (jamesTreeMask (𝕜 := 𝕜) (p := p) (dyadicInitialLevels N) hN).toLinearMap) := by
  rw [jamesTreeLevelProjection_range]
  infer_instance

theorem literalJamesTreeLevelProjection_finiteDimensional (p : BanachExponent) (N : ℕ) :
    FiniteDimensional 𝕜
      (LinearMap.range (literalJamesTreeLevelProjection (𝕜 := 𝕜) p N).toLinearMap) :=
  jamesTreeLevelProjection_finiteDimensional N (literalJamesTreeMaskClosed_levels N)

theorem consecutiveJamesTreeLevelProjection_finiteDimensional (p : BanachExponent) (N : ℕ) :
    FiniteDimensional 𝕜
      (LinearMap.range (consecutiveJamesTreeLevelProjection (𝕜 := 𝕜) p N).toLinearMap) :=
  jamesTreeLevelProjection_finiteDimensional N (consecutiveJamesTreeMaskClosed_levels N)

theorem jamesTree_level_sums_tendsto
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    Tendsto (fun N => ∑ t ∈ dyadicInitialFinset N, jamesTreeCoordinate t x • jamesTreeUnit t)
      atTop (𝓝 x) := by
  simpa only [jamesTreeLevelProjection_finite_sum] using
    jamesTreeMask_tendsto dyadicInitialLevels hS (fun t => eventually_ge_atTop t.length) x

theorem jamesTreeCoordinate_ext
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    {x y : SegmentJamesTreeSpace 𝕜 p S}
    (h : ∀ t, jamesTreeCoordinate t x = jamesTreeCoordinate t y) : x = y := by
  have hx := jamesTree_level_sums_tendsto hS x
  have hy := jamesTree_level_sums_tendsto hS y
  simp only [h] at hx
  exact tendsto_nhds_unique hx hy

theorem jamesTreeUnit_linearIndependent :
    LinearIndependent 𝕜 (jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro F c h t ht
  have hh := congrArg (jamesTreeCoordinate (𝕜 := 𝕜) (p := p) (S := S) t) h
  simpa [map_sum, map_smul, jamesTreeCoordinate_unit, ht] using hh

theorem jamesTree_finite_levels_dense
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)) :
    Dense (⋃ N : ℕ, (jamesTreeFiniteSpan (𝕜 := 𝕜) (p := p) (S := S)
      (dyadicInitialFinset N) : Set (SegmentJamesTreeSpace 𝕜 p S))) := by
  intro x
  apply mem_closure_of_tendsto (jamesTreeMask_tendsto dyadicInitialLevels hS
    (fun t => eventually_ge_atTop t.length) x)
  apply Filter.Eventually.of_forall
  intro N
  apply Set.mem_iUnion.mpr
  refine ⟨N, ?_⟩
  rw [← jamesTreeLevelProjection_range N (hS N)]
  exact ⟨x, rfl⟩

theorem literalJamesTree_level_sums_tendsto (p : BanachExponent)
    (x : LiteralChainJamesTreeSpace 𝕜 p) :
    Tendsto (fun N => ∑ t ∈ dyadicInitialFinset N, jamesTreeCoordinate t x • jamesTreeUnit t)
      atTop (𝓝 x) := jamesTree_level_sums_tendsto literalJamesTreeMaskClosed_levels x

theorem consecutiveJamesTree_level_sums_tendsto (p : BanachExponent)
    (x : ConsecutiveJamesTreeSpace 𝕜 p) :
    Tendsto (fun N => ∑ t ∈ dyadicInitialFinset N, jamesTreeCoordinate t x • jamesTreeUnit t)
      atTop (𝓝 x) := jamesTree_level_sums_tendsto consecutiveJamesTreeMaskClosed_levels x

end ThesisCommon
