import ThesisCommon.Analysis.GowersMaureySubspaceTailApproximation

/-! A genuine gliding-hump construction for arbitrary infinite-dimensional
subspaces. The finite blocks stay close to unit vectors of the original
subspace, with any prescribed positive decreasing error sequence. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_approximating_block_sequence (D : ConstructionData 𝕜)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hanti : Antitone ε) :
    ∃ u : ℕ → C00 𝕜, ∃ v : ℕ → ShiftSpace D,
      (∀ i j, i < j → Before (u i) (u j)) ∧
      (∀ i, v i ∈ E) ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ i, ‖denseEmbedding D (u i) - v i‖ < ε i) ∧
      (∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i)) := by
  classical
  let P (a : ℕ × C00 𝕜 × ShiftSpace D) :=
    a.2.2 ∈ E ∧ ‖a.2.2‖ = 1 ∧
    ‖denseEmbedding D a.2.1 - a.2.2‖ < ε a.1 ∧ (1 : ℝ)/2 ≤ implicitNorm D a.2.1
  let R (a b : ℕ × C00 𝕜 × ShiftSpace D) := a.1 < b.1 ∧ Before a.2.1 b.2.1
  have hselect : ∀ s : Finset (ℕ × C00 𝕜 × ShiftSpace D), (∀ a ∈ s, P a) →
      ∃ b, P b ∧ ∀ a ∈ s, R a b := by
    intro s _
    let n := s.sup Prod.fst + 1
    let B := s.sup (fun a => a.2.1.support.sup id)
    have hδ : 0 < min ((1 : ℝ)/2) (ε n) := lt_min (by norm_num) (hε n)
    obtain ⟨x, y, hxB, hy, hynorm, herr⟩ := exists_subspace_tail_approximation D E hE B hδ
    have herrHalf : ‖denseEmbedding D x - y‖ < (1 : ℝ)/2 := herr.trans_le (min_le_left _ _)
    have hxnorm : (1 : ℝ)/2 ≤ implicitNorm D x := by
      have hh := norm_le_insert' y (denseEmbedding D x)
      rw [hynorm, norm_sub_rev, denseEmbedding_norm] at hh
      change 1 ≤ implicitNorm D x + ‖denseEmbedding D x-y‖ at hh
      linarith
    refine ⟨(n,x,y), ⟨hy, hynorm, herr.trans_le (min_le_right _ _), hxnorm⟩, ?_⟩
    intro a ha
    refine ⟨(Finset.le_sup (f := Prod.fst) ha).trans_lt (Nat.lt_succ_self _), ?_⟩
    apply before_of_mem_afterCutoff (K := B) _ hxB
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      (Finset.le_sup (f := fun a : ℕ × C00 𝕜 × ShiftSpace D => a.2.1.support.sup id) ha)
  obtain ⟨w, hw, hwr⟩ := exists_seq_of_forall_finset_exists P R hselect
  have hindex : ∀ i : ℕ, i ≤ (w i).1 := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have hh := (hwr i (i+1) (Nat.lt_succ_self i)).1; omega
  refine ⟨fun i => (w i).2.1, fun i => (w i).2.2,
    fun i j hij => (hwr i j hij).2,
    fun i => (hw i).1, fun i => (hw i).2.1,
    fun i => (hw i).2.2.1.trans_le (hanti (hindex i)), fun i => (hw i).2.2.2⟩

end ThesisCommon.GowersMaurey
