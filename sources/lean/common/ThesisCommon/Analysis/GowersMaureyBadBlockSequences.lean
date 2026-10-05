import ThesisCommon.Analysis.GowersMaureyOperatorSeminorm
import ThesisCommon.Analysis.GowersMaureyBlockTails

/-! Actual witnesses for a strict lower bound on the block operator seminorm.
The witnesses remain genuine block tests after extraction and after discarding
any finite coordinate head. This is the initial selection in source Lemma 9;
no finite-support condition is imposed on the images of the operator. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

namespace BlockTestSequence
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}

def subsequence (u : BlockTestSequence D Y) (a : ℕ → ℕ) (ha : StrictMono a) :
    BlockTestSequence D Y where
  vector n := u.vector (a n)
  mem_subspace n := u.mem_subspace (a n)
  successive _ _ hij := u.successive _ _ (ha hij)
  norm_bound n := (intervalNorm_mono D (Nat.add_le_add_right (ha.id_le n) 1) _).trans
    (u.norm_bound (a n))

@[simp] theorem subsequence_inSubspace (u : BlockTestSequence D Y)
    (a : ℕ → ℕ) (ha : StrictMono a) (n : ℕ) :
    (u.subsequence a ha).inSubspace n = u.inSubspace (a n) := rfl

theorem exists_subsequence_norm_gt (u : BlockTestSequence D Y)
    (T : Y →L[𝕜] ShiftSpace D) {r : ℝ} (hr : r < u.operatorSeminorm T) :
    ∃ a : ℕ → ℕ, ∃ ha : StrictMono a,
      ∀ n, r < ‖T ((u.subsequence a ha).inSubspace n)‖ := by
  obtain ⟨a,ha,hbad⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_lt_limsup (operator_sequence_cobounded u.inSubspace T) hr)
  exact ⟨a,ha,hbad⟩

end BlockTestSequence

theorem exists_bad_blockTestSequence (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (T : Y →L[𝕜] ShiftSpace D)
    {r : ℝ} (hr : r < blockOperatorSeminorm D Y T) :
    ∃ u : BlockTestSequence D Y, ∀ n, r < ‖T (u.inSubspace n)‖ := by
  rw [blockOperatorSeminorm_apply] at hr
  have hb : BddAbove (Set.range (fun u : BlockTestSequence D Y =>
      limsup (fun n => ‖T (u.inSubspace n)‖) atTop)) := by
    refine ⟨‖T‖, ?_⟩
    rintro _ ⟨u,rfl⟩
    exact u.operatorSeminorm_le_norm T
  obtain ⟨_,⟨u,rfl⟩,hu⟩ := (lt_csSup_iff hb (Set.range_nonempty _)).mp hr
  obtain ⟨a,ha,hbad⟩ := u.exists_subsequence_norm_gt T hu
  exact ⟨u.subsequence a ha,hbad⟩

theorem exists_bad_blockTestSequence_after (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (T : Y →L[𝕜] ShiftSpace D)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < blockOperatorSeminorm D Y T) (K : ℕ) :
    ∃ u : BlockTestSequence D Y, (∀ n, u.vector n ≠ 0) ∧
      (∀ n, u.vector n ∈ afterCutoff K) ∧ ∀ n, r < ‖T (u.inSubspace n)‖ := by
  obtain ⟨u,hu⟩ := exists_bad_blockTestSequence D Y T hr
  have hne : ∀ n, u.vector n ≠ 0 := by
    intro n hn
    have hv : u.inSubspace n = 0 := by
      apply Subtype.ext
      change denseEmbedding D (u.vector n) = 0
      rw [hn,map_zero]
    have hh := hu n
    rw [hv,map_zero,norm_zero] at hh
    exact (not_lt_of_ge hr0) hh
  have ha : StrictMono (fun n : ℕ => K+1+n) := fun _ _ h => Nat.add_lt_add_left h _
  refine ⟨u.subsequence (fun n => K+1+n) ha, fun n => hne _, ?_, fun n => hu _⟩
  intro n
  exact block_tail_mem_afterCutoff u.vector u.successive hne K n

end ThesisCommon.GowersMaurey
