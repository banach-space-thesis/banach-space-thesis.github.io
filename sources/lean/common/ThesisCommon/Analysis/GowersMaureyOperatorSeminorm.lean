import ThesisCommon.Analysis.BoundedSequenceOperatorLimsup
import ThesisCommon.Analysis.GowersMaureyCoordinates
import ThesisCommon.Analysis.GowersMaureyIntervalNorms

/-! The source's actual operator seminorm |||T||| (arXiv:math/9407209,
printed p.7). Its tests are successive finite-support sequences in the
given subspace, with the n-th interval norm at most one. The indexing
starts at zero here, so the interval parameter is n+1. The definition
does not include representation, multiplicativity or a kernel assertion. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 : Type*} [RCLike 𝕜]

structure BlockTestSequence (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D)) where
  vector : ℕ → C00 𝕜
  mem_subspace : ∀ n, denseEmbedding D (vector n) ∈ Y
  successive : ∀ i j, i < j → Before (vector i) (vector j)
  norm_bound : ∀ n, intervalNorm D (n+1) (vector n) ≤ 1

namespace BlockTestSequence
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}

def zero (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D)) : BlockTestSequence D Y where
  vector _ := 0
  mem_subspace _ := by simp
  successive := by intro i j hij n hn; simp at hn
  norm_bound _ := by simp

instance : Nonempty (BlockTestSequence D Y) := ⟨zero D Y⟩

def inSubspace (u : BlockTestSequence D Y) (n : ℕ) : Y :=
  ⟨denseEmbedding D (u.vector n), u.mem_subspace n⟩

theorem norm_inSubspace_le_one (u : BlockTestSequence D Y) (n : ℕ) :
    ‖u.inSubspace n‖ ≤ 1 := by
  change ‖denseEmbedding D (u.vector n)‖ ≤ 1
  rw [denseEmbedding_norm]
  exact (implicitNorm_le_intervalNorm D (Nat.succ_pos n) (u.vector n)).trans (u.norm_bound n)

def operatorSeminorm (u : BlockTestSequence D Y) : Seminorm 𝕜 (Y →L[𝕜] ShiftSpace D) :=
  operatorSequenceSeminorm u.inSubspace u.norm_inSubspace_le_one

theorem operatorSeminorm_apply (u : BlockTestSequence D Y) (T : Y →L[𝕜] ShiftSpace D) :
    u.operatorSeminorm T = limsup (fun n => ‖T (u.inSubspace n)‖) atTop := rfl

theorem operatorSeminorm_le_norm (u : BlockTestSequence D Y) (T : Y →L[𝕜] ShiftSpace D) :
    u.operatorSeminorm T ≤ ‖T‖ :=
  operatorSequenceSeminorm_le_norm u.inSubspace u.norm_inSubspace_le_one T

end BlockTestSequence

theorem blockTestSeminorms_bddAbove (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D)) :
    BddAbove (Set.range (fun u : BlockTestSequence D Y => u.operatorSeminorm)) := by
  refine ⟨normSeminorm 𝕜 (Y →L[𝕜] ShiftSpace D), ?_⟩
  rintro _ ⟨u, rfl⟩ T
  exact u.operatorSeminorm_le_norm T

def blockOperatorSeminorm (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D)) :
    Seminorm 𝕜 (Y →L[𝕜] ShiftSpace D) := ⨆ u : BlockTestSequence D Y, u.operatorSeminorm

theorem blockOperatorSeminorm_apply (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    (T : Y →L[𝕜] ShiftSpace D) :
    blockOperatorSeminorm D Y T = sSup (Set.range (fun u : BlockTestSequence D Y =>
      limsup (fun n => ‖T (u.inSubspace n)‖) atTop)) := by
  rw [blockOperatorSeminorm, Seminorm.iSup_apply (blockTestSeminorms_bddAbove D Y), sSup_range]
  rfl

theorem blockOperatorSeminorm_le_norm (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    (T : Y →L[𝕜] ShiftSpace D) : blockOperatorSeminorm D Y T ≤ ‖T‖ := by
  rw [blockOperatorSeminorm, Seminorm.iSup_apply (blockTestSeminorms_bddAbove D Y)]
  exact ciSup_le (fun u => u.operatorSeminorm_le_norm T)

theorem BlockTestSequence.limsup_le_blockOperatorSeminorm
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (T : Y →L[𝕜] ShiftSpace D) :
    limsup (fun n => ‖T (u.inSubspace n)‖) atTop ≤ blockOperatorSeminorm D Y T := by
  rw [blockOperatorSeminorm, Seminorm.iSup_apply (blockTestSeminorms_bddAbove D Y)]
  exact le_ciSup (show BddAbove (Set.range (fun v : BlockTestSequence D Y =>
    v.operatorSeminorm T)) from ⟨‖T‖, by rintro _ ⟨v, rfl⟩; exact v.operatorSeminorm_le_norm T⟩) u

theorem blockOperatorSeminorm_continuous (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) : Continuous (blockOperatorSeminorm D Y) := by
  apply Seminorm.continuous_of_le (q := normSeminorm 𝕜 (Y →L[𝕜] ShiftSpace D))
    (@continuous_norm (Y →L[𝕜] ShiftSpace D) _)
  intro T
  exact blockOperatorSeminorm_le_norm D Y T

end ThesisCommon.GowersMaurey
