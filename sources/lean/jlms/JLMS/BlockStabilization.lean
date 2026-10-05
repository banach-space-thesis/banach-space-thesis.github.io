import JLMS.BlockDiagonal

/-!
# Stabilizing the pointwise radius under all further normalized blocks

The diagonal of an improving nested sequence retains each stage after a
finite shift. Translating coefficients past that finite prefix shows that
every further block has radius at least the infimum at each earlier stage.
The improving errors tend to zero, so the diagonal radius is unchanged by
any further normalized blocking.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem NormalizedBlockSystem.shiftInput_applyDual_tail
    (b : NormalizedBlockSystem 𝕜) (m : ℕ)
    (hm : ∀ n k, k ∈ b.support n → m ≤ k)
    (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) :
    (b.shiftInput m hm).applyDual (fun k => f (k + m)) n = b.applyDual f n := by
  rw [b.shiftInput_applyDual]
  change (∑ k ∈ b.support n, b.coefficient n k • f ((k - m) + m)) = _
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.sub_add_cancel (hm n k hk)]

theorem blockRadiusInfimum_le_block_of_tail
    (f g : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (d : NormalizedBlockSystem 𝕜) (m : ℕ)
    (ht : d.applyDual f = fun n => g (n + m)) (b : NormalizedBlockSystem 𝕜) :
    blockRadiusInfimum f ≤ dualAsymptoticRadius (b.applyDual g) := by
  let bt := b.reindex (fun n => n + m) (by
    intro i j hij
    change i + m < j + m
    omega)
  have hm : ∀ n k, k ∈ bt.support n → m ≤ k := by
    intro n k hk
    have h := b.index_le_support (n + m) k hk
    omega
  let a := bt.shiftInput m hm
  have heq : (d.compose a).applyDual f = fun n => b.applyDual g (n + m) := by
    funext n
    rw [d.compose_applyDual, ht]
    exact bt.shiftInput_applyDual_tail m hm g n
  have h := blockRadiusInfimum_le_block f hC hf (d.compose a)
  rw [heq, dualAsymptoticRadius_shift] at h
  exact h

theorem exists_block_radius_stable (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ d : NormalizedBlockSystem 𝕜, ∀ a : NormalizedBlockSystem 𝕜,
      dualAsymptoticRadius (a.applyDual (d.applyDual f)) =
        dualAsymptoticRadius (d.applyDual f) := by
  let ε : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  obtain ⟨b, c, hb0, hbs, hsmall⟩ := exists_radius_improving_blocks f ε
    (fun n => pow_pos (by norm_num) n)
  have hb (n : ℕ) : b n = blockIteration c 0 n := by
    induction n with
    | zero => exact hb0
    | succ n ih => rw [hbs, ih, blockIteration_succ, zero_add]
  let d := blockDiagonal c 0
  refine ⟨d, fun a => le_antisymm
    (dualAsymptoticRadius_blocks_le _ hC (d.norm_applyDual_le f hf) a) ?_⟩
  have hn (n : ℕ) : dualAsymptoticRadius (d.applyDual f) ≤
      dualAsymptoticRadius (a.applyDual (d.applyDual f)) + ε n := by
    have hlow := blockRadiusInfimum_le_block_of_tail
      ((blockIteration c 0 n).applyDual f) (d.applyDual f)
      hC ((blockIteration c 0 n).norm_applyDual_le f hf)
      (blockDiagonal c n) n (blockDiagonal_tail_apply c f n) a
    have hup := blockDiagonal_radius_le_stage c f hC hf (n + 1)
    have hs := hsmall n
    rw [hb (n + 1), hb n] at hs
    exact hup.trans (hs.le.trans (add_le_add_right hlow _))
  have ht : Tendsto ε atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht' : Tendsto (fun n => dualAsymptoticRadius (a.applyDual (d.applyDual f)) + ε n)
      atTop (𝓝 (dualAsymptoticRadius (a.applyDual (d.applyDual f)) + 0)) :=
    tendsto_const_nhds.add ht
  simpa only [add_zero] using ge_of_tendsto ht' (Filter.Eventually.of_forall hn)

end JLMS
