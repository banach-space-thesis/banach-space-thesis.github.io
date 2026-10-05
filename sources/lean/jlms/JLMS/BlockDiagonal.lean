import JLMS.BlockTails

/-!
# A diagonal block sequence retaining every nested-stage tail

At stage n keep a finite history of all coordinate supports used in earlier
representations. Choose the next row beyond that history. The resulting
diagonal is a normalized block of the original sequence; its tail from
stage m is a normalized block of the m-th refined sequence.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
attribute [local instance] Classical.decEq

def blockDiagonalHistory (c : ℕ → NormalizedBlockSystem 𝕜) : ℕ → Finset ℕ :=
  Nat.rec ∅ (fun n H => H ∪ (Finset.range (n + 1)).biUnion
    (fun m => (blockIteration c m (n - m)).support (H.sup id + 1)))

def blockDiagonalIndex (c : ℕ → NormalizedBlockSystem 𝕜) (n : ℕ) : ℕ :=
  (blockDiagonalHistory c n).sup id + 1

theorem blockDiagonalHistory_monotone (c : ℕ → NormalizedBlockSystem 𝕜) :
    Monotone (blockDiagonalHistory c) := monotone_nat_of_le_succ (fun n => Finset.subset_union_left)

theorem blockDiagonal_support_in_history (c : ℕ → NormalizedBlockSystem 𝕜)
    {m i j k : ℕ} (hmi : m ≤ i) (hij : i < j)
    (hk : k ∈ (blockIteration c m (i - m)).support (blockDiagonalIndex c i)) :
    k ∈ blockDiagonalHistory c j := by
  apply blockDiagonalHistory_monotone c (Nat.succ_le_of_lt hij)
  change k ∈ blockDiagonalHistory c i ∪ (Finset.range (i + 1)).biUnion _
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega), hk⟩

theorem blockDiagonalIndex_gt_history (c : ℕ → NormalizedBlockSystem 𝕜)
    {n k : ℕ} (hk : k ∈ blockDiagonalHistory c n) : k < blockDiagonalIndex c n :=
  lt_of_le_of_lt (Finset.le_sup (f := id) hk) (Nat.lt_succ_self _)

def blockDiagonal (c : ℕ → NormalizedBlockSystem 𝕜) (m : ℕ) : NormalizedBlockSystem 𝕜 where
  support n := (blockIteration c m n).support (blockDiagonalIndex c (n + m))
  coefficient n := (blockIteration c m n).coefficient (blockDiagonalIndex c (n + m))
  mass_one n := (blockIteration c m n).mass_one _
  ordered := by
    intro n p hnp i hi j hj
    have hi' : i ∈ (blockIteration c m ((n + m) - m)).support (blockDiagonalIndex c (n + m)) := by
      simpa only [Nat.add_sub_cancel] using hi
    have hpast := blockDiagonal_support_in_history c (m := m) (i := n + m) (j := p + m)
      (by omega) (by omega) hi'
    have hil := blockDiagonalIndex_gt_history c hpast
    have hlj := (blockIteration c m p).index_le_support _ j hj
    exact hil.trans_le hlj

theorem blockDiagonal_tail_apply (c : ℕ → NormalizedBlockSystem 𝕜)
    (f : ℕ → (X →L[𝕜] 𝕜)) (m : ℕ) :
    (blockDiagonal c m).applyDual ((blockIteration c 0 m).applyDual f) =
      fun n => (blockDiagonal c 0).applyDual f (n + m) := by
  funext n
  change (blockIteration c m n).applyDual ((blockIteration c 0 m).applyDual f)
      (blockDiagonalIndex c (n + m)) =
    (blockIteration c 0 (n + m)).applyDual f (blockDiagonalIndex c ((n + m) + 0))
  have h := blockIteration_apply_split c 0 m n f
  simp only [zero_add, Nat.add_zero, Nat.add_comm m n] at h ⊢
  exact (congrArg (fun g : ℕ → (X →L[𝕜] 𝕜) => g (blockDiagonalIndex c (n + m))) h).symm

theorem blockDiagonal_radius_le_stage (c : ℕ → NormalizedBlockSystem 𝕜)
    (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (m : ℕ) :
    dualAsymptoticRadius ((blockDiagonal c 0).applyDual f) ≤
      dualAsymptoticRadius ((blockIteration c 0 m).applyDual f) := by
  rw [← dualAsymptoticRadius_shift ((blockDiagonal c 0).applyDual f) m,
    ← blockDiagonal_tail_apply c f m]
  exact dualAsymptoticRadius_blocks_le _ hC ((blockIteration c 0 m).norm_applyDual_le f hf) _

end JLMS
