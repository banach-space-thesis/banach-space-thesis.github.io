import ThesisCommon.Analysis.GowersMaureyEndomorphismSeminorm
import ThesisCommon.Analysis.GowersMaureyBlockTails

/-! A lower-bound criterion for the actual block operator seminorm.
Independent finite vectors after every coordinate cutoff are assembled
into a genuine successive test sequence, with increasing interval orders. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem le_spaceOperatorSeminorm_of_tail_tests (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (b : ℝ)
    (htest : ∀ n : ℕ, 0 < n → ∀ B : ℕ, ∃ x : C00 𝕜,
      x ∈ afterCutoff B ∧ intervalNorm D n x ≤ 1 ∧ b ≤ ‖T (denseEmbedding D x)‖) :
    b ≤ spaceOperatorSeminorm D T := by
  classical
  let P (a : ℕ × C00 𝕜) := 0 < a.1 ∧ intervalNorm D a.1 a.2 ≤ 1 ∧
    b ≤ ‖T (denseEmbedding D a.2)‖
  let R (a c : ℕ × C00 𝕜) := a.1 < c.1 ∧ Before a.2 c.2
  have hselect : ∀ s : Finset (ℕ × C00 𝕜), (∀ a ∈ s, P a) →
      ∃ c, P c ∧ ∀ a ∈ s, R a c := by
    intro s _
    let n := s.sup Prod.fst + 1
    let B := s.sup (fun a => a.2.support.sup id)
    obtain ⟨x, hxB, hxnorm, hxT⟩ := htest n (Nat.succ_pos _) B
    refine ⟨(n,x), ⟨Nat.succ_pos _, hxnorm, hxT⟩, ?_⟩
    intro a ha
    refine ⟨(Finset.le_sup (f := Prod.fst) ha).trans_lt (Nat.lt_succ_self _), ?_⟩
    apply before_of_mem_afterCutoff (K := B) _ hxB
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      (Finset.le_sup (f := fun a : ℕ × C00 𝕜 => a.2.support.sup id) ha)
  obtain ⟨v, hv, hvr⟩ := exists_seq_of_forall_finset_exists P R hselect
  have hn : ∀ i : ℕ, i + 1 ≤ (v i).1 := by
    intro i
    induction i with
    | zero => exact (hv 0).1
    | succ i ih => have hh := (hvr i (i+1) (Nat.lt_succ_self i)).1; omega
  let u : BlockTestSequence D ⊤ := {
    vector := fun i => (v i).2
    mem_subspace := fun _ => Submodule.mem_top
    successive := fun i j hij => (hvr i j hij).2
    norm_bound := fun i => (intervalNorm_mono D (hn i) _).trans (hv i).2.1
  }
  have hb : b ≤ limsup (fun i => ‖T (denseEmbedding D (u.vector i))‖) atTop := by
    refine le_limsup_of_frequently_le
      (Eventually.frequently (Eventually.of_forall (fun i => (hv i).2.2))) ?_
    exact operator_sequence_boundedAbove (fun i => denseEmbedding D (u.vector i))
      (fun i => u.norm_inSubspace_le_one i) T
  exact hb.trans (u.limsup_le_spaceOperatorSeminorm T)

end ThesisCommon.GowersMaurey
