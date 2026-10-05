import Posets.CountableSeparableBlocks
import Posets.OperatorLemmas

/-! Separable off-diagonal operators between sums with different index types. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon Filter Topology
open scoped Filter
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜]

theorem productSums_hasSeparableRange_of_blocks
    {P Q : Type*} [Countable P] [Countable Q]
    (X : P → Type*) (Z : Q → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ q, NormedAddCommGroup (Z q)] [∀ q, NormedSpace 𝕜 (Z q)]
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z)
    (hblock : ∀ s t, HasSeparableRange 𝕜 (X t) (Z s) (operatorBlock 𝕜 X Z T s t)) :
    HasSeparableRange 𝕜 (DependentCZeroSum 𝕜 X) (DependentCZeroSum 𝕜 Z) T := by
  let S (F : Finset Q × Finset P) :=
    (finiteProjection 𝕜 Z F.1).comp (T.comp (finiteProjection 𝕜 X F.2))
  apply countableStrongLimit_separable
    (l := (atTop : Filter (Finset Q)) ×ˢ (atTop : Filter (Finset P))) S T
  · intro F
    have heq : S F = ∑ s ∈ F.1, ∑ t ∈ F.2,
        (sumInjection 𝕜 Z s).comp ((operatorBlock 𝕜 X Z T s t).comp (sumProjection 𝕜 X t)) := by
      ext x
      simp [S, finiteProjection, operatorBlock, map_sum]
    rw [heq]
    apply hasSeparableRange_sum
    intro s _
    apply hasSeparableRange_sum
    intro t _
    exact ((hblock s t).comp_right (sumProjection 𝕜 X t)).comp_left (sumInjection 𝕜 Z s)
  · intro x
    have hin := (T.continuous.continuousAt.tendsto.comp
      (finiteProjection_tendsto 𝕜 X x)).comp
        (tendsto_snd : Tendsto (fun F : Finset Q × Finset P => F.2)
          ((atTop : Filter (Finset Q)) ×ˢ (atTop : Filter (Finset P))) atTop)
    have hout := (finiteProjection_tendsto 𝕜 Z (T x)).comp
      (tendsto_fst : Tendsto (fun F : Finset Q × Finset P => F.1)
        ((atTop : Filter (Finset Q)) ×ˢ (atTop : Filter (Finset P))) atTop)
    have hbound : ∀ F : Finset Q × Finset P,
        ‖S F x - T x‖ ≤ ‖T (finiteProjection 𝕜 X F.2 x) - T x‖ +
          ‖finiteProjection 𝕜 Z F.1 (T x) - T x‖ := by
      intro F
      change ‖finiteProjection 𝕜 Z F.1 (T (finiteProjection 𝕜 X F.2 x)) - T x‖ ≤ _
      calc
        _ ≤ ‖finiteProjection 𝕜 Z F.1 (T (finiteProjection 𝕜 X F.2 x)) -
            finiteProjection 𝕜 Z F.1 (T x)‖ + ‖finiteProjection 𝕜 Z F.1 (T x) - T x‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (finiteProjection 𝕜 Z F.1 (T (finiteProjection 𝕜 X F.2 x)))
            (finiteProjection 𝕜 Z F.1 (T x)) (T x)
        _ ≤ _ := by
          rw [← map_sub]
          exact add_le_add_right (finiteProjection_norm_le 𝕜 Z _ _) _
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) hbound
    simpa only [Function.comp_apply, add_zero] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hin).add
        (tendsto_iff_norm_sub_tendsto_zero.mp hout)

theorem fewOperators_component_hasFewOperators
    {P : Type*} [PartialOrder P] {X : P → Type*}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) (p : P) :
    JFA.HasFewOperators 𝕜 (X p) := by
  intro T
  obtain ⟨a, S, hS, hT⟩ := h.2.2.2.2.1 p p le_rfl T
  exact ⟨a, S, hS, by rwa [fewOperators_self h p] at hT⟩

end Posets
