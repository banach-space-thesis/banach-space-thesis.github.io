import JLMS.BlockRadiusInfimum

/-!
# Nested normalized blocking with improving asymptotic radii

Iterated blocks retain their normalized coefficient representation in the
original sequence. Each stage can approach the infimum of all further block
radii by a prescribed positive error. The same construction is reusable
for stabilization and diagonal selection.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def NormalizedBlockSystem.reindex (b : NormalizedBlockSystem 𝕜)
    (s : ℕ → ℕ) (hs : StrictMono s) : NormalizedBlockSystem 𝕜 where
  support n := b.support (s n)
  coefficient n := b.coefficient (s n)
  mass_one n := b.mass_one (s n)
  ordered n m hnm := b.ordered (s n) (s m) (hs hnm)

@[simp] theorem NormalizedBlockSystem.reindex_applyDual (b : NormalizedBlockSystem 𝕜)
    (s : ℕ → ℕ) (hs : StrictMono s) (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) :
    (b.reindex s hs).applyDual f n = b.applyDual f (s n) := rfl

def blockIteration (c : ℕ → NormalizedBlockSystem 𝕜) (start : ℕ) : ℕ → NormalizedBlockSystem 𝕜 :=
  Nat.rec NormalizedBlockSystem.units (fun n b => b.compose (c (start + n)))

@[simp] theorem blockIteration_zero (c : ℕ → NormalizedBlockSystem 𝕜) (start : ℕ) :
    blockIteration c start 0 = NormalizedBlockSystem.units := rfl

@[simp] theorem blockIteration_succ (c : ℕ → NormalizedBlockSystem 𝕜) (start n : ℕ) :
    blockIteration c start (n + 1) = (blockIteration c start n).compose (c (start + n)) := rfl

theorem blockIteration_apply_split (c : ℕ → NormalizedBlockSystem 𝕜) (start m n : ℕ)
    (f : ℕ → (X →L[𝕜] 𝕜)) :
    (blockIteration c start (m + n)).applyDual f =
      (blockIteration c (start + m) n).applyDual ((blockIteration c start m).applyDual f) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero, blockIteration_zero]
    funext i
    exact (NormalizedBlockSystem.units_applyDual _ i).symm
  | succ n ih =>
    simp only [Nat.add_succ, blockIteration_succ]
    have heq (b d : NormalizedBlockSystem 𝕜) (g : ℕ → (X →L[𝕜] 𝕜)) :
        (b.compose d).applyDual g = d.applyDual (b.applyDual g) := by
      funext i; exact b.compose_applyDual d g i
    rw [heq, heq, ih, Nat.add_assoc]

theorem exists_radius_improving_blocks (f : ℕ → (X →L[𝕜] 𝕜))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ b c : ℕ → NormalizedBlockSystem 𝕜,
      b 0 = NormalizedBlockSystem.units ∧
      (∀ n, b (n + 1) = (b n).compose (c n)) ∧
      ∀ n, dualAsymptoticRadius ((b (n + 1)).applyDual f) <
        blockRadiusInfimum ((b n).applyDual f) + ε n := by
  classical
  have hex (n : ℕ) (b : NormalizedBlockSystem 𝕜) :=
    exists_block_radius_lt (b.applyDual f) (hε n)
  choose next hnext using hex
  let b : ℕ → NormalizedBlockSystem 𝕜 :=
    Nat.rec NormalizedBlockSystem.units (fun n b => b.compose (next n b))
  let c (n : ℕ) := next n (b n)
  refine ⟨b, c, rfl, fun n => rfl, ?_⟩
  intro n
  have heq : (b (n + 1)).applyDual f = (c n).applyDual ((b n).applyDual f) := by
    funext i
    exact (b n).compose_applyDual (c n) f i
  rw [heq]
  exact hnext n (b n)

end JLMS
