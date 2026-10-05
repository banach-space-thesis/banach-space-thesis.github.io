import Posets.SeparableBlocks

noncomputable section
set_option maxHeartbeats 1500000
open Filter Topology TopologicalSpace ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem countableStrongLimit_separable {I E F : Type*} [Countable I]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {l : Filter I} [l.NeBot] (S : I → E →L[𝕜] F) (T : E →L[𝕜] F)
    (hsep : ∀ i, HasSeparableRange 𝕜 E F (S i))
    (hlim : ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x))) : HasSeparableRange 𝕜 E F T := by
  apply (IsSeparable.iUnion hsep).closure.mono
  rintro _ ⟨x, rfl⟩
  apply isClosed_closure.mem_of_tendsto (hlim x)
  exact Eventually.of_forall (fun i => subset_closure (Set.mem_iUnion.mpr ⟨i, x, rfl⟩))

variable {P : Type*} (X Z : P → Type*)
  [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, NormedAddCommGroup (Z p)] [∀ p, NormedSpace 𝕜 (Z p)]

def finiteBlockTruncation (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) (F : Finset P) :
    DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z :=
  ∑ s ∈ F, ∑ t ∈ F,
    (sumInjection 𝕜 Z s).comp ((operatorBlock 𝕜 X Z T s t).comp (sumProjection 𝕜 X t))

theorem finiteBlockTruncation_eq (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) (F : Finset P) :
    finiteBlockTruncation X Z T F =
      (finiteProjection 𝕜 Z F).comp (T.comp (finiteProjection 𝕜 X F)) := by
  ext x
  simp [finiteBlockTruncation, finiteProjection, operatorBlock, map_sum]

theorem finiteBlockTruncation_tendsto (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z)
    (x : DependentCZeroSum 𝕜 X) :
    Tendsto (fun F => finiteBlockTruncation X Z T F x) atTop (𝓝 (T x)) := by
  have hin := T.continuous.continuousAt.tendsto.comp (finiteProjection_tendsto 𝕜 X x)
  have hout := finiteProjection_tendsto 𝕜 Z (T x)
  have hbound : ∀ F,
      ‖finiteBlockTruncation X Z T F x - T x‖ ≤
      ‖T (finiteProjection 𝕜 X F x) - T x‖ + ‖finiteProjection 𝕜 Z F (T x) - T x‖ := by
    intro F
    rw [finiteBlockTruncation_eq]
    change ‖finiteProjection 𝕜 Z F (T (finiteProjection 𝕜 X F x)) - T x‖ ≤ _
    calc
      _ ≤ ‖finiteProjection 𝕜 Z F (T (finiteProjection 𝕜 X F x)) - finiteProjection 𝕜 Z F (T x)‖ +
          ‖finiteProjection 𝕜 Z F (T x) - T x‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          (finiteProjection 𝕜 Z F (T (finiteProjection 𝕜 X F x)))
          (finiteProjection 𝕜 Z F (T x)) (T x)
      _ ≤ _ := by
        rw [← map_sub]
        exact add_le_add_right (finiteProjection_norm_le 𝕜 Z _ _) _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hin).add
    (tendsto_iff_norm_sub_tendsto_zero.mp hout)

theorem countable_blocks_separable_iff [Countable P]
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) :
    HasSeparableRange 𝕜 (DependentCZeroSum 𝕜 X) (DependentCZeroSum 𝕜 Z) T ↔
      ∀ s t, HasSeparableRange 𝕜 (X t) (Z s) (operatorBlock 𝕜 X Z T s t) := by
  constructor
  · intro hT s t
    exact (hT.comp_right (sumInjection 𝕜 X t)).comp_left (sumProjection 𝕜 Z s)
  · intro hblock
    apply countableStrongLimit_separable (l := atTop) (finiteBlockTruncation X Z T) T
    · intro F
      apply hasSeparableRange_sum
      intro s _
      apply hasSeparableRange_sum
      intro t _
      exact ((hblock s t).comp_right (sumProjection 𝕜 X t)).comp_left (sumInjection 𝕜 Z s)
    · exact finiteBlockTruncation_tendsto X Z T

end Posets
