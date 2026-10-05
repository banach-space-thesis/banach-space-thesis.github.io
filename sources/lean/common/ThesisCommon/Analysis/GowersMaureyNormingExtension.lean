import ThesisCommon.Analysis.GowersMaureyTailNorming
import ThesisCommon.Analysis.GowersMaureyBadBlockSequences

/-! One genuine gliding-hump extension for source Lemma 9. Both directions
of every cross pairing for a finite family of bounded operators are made
small. The new functional nearly norms the actual completed image. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_norming_block_after_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ n, u.vector n ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) {r δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hbad : ∀ n, r+2*δ < ‖T (u.inSubspace n)‖)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Y) (a : ι → C00 𝕜) (V : κ → Y →L[𝕜] ShiftSpace D)
    (B L : ℕ) :
    ∃ n : ℕ, ∃ b : C00 𝕜, L < n ∧ u.vector n ∈ afterCutoff B ∧
      b ∈ afterCutoff B ∧ DualUnit (implicitNorm D) b ∧
      r < RCLike.re (completedPairing D b (T (u.inSubspace n))) ∧
      (∀ i, Before (a i) b) ∧ ∀ i j,
        ‖completedPairing D (a i) (V j (u.inSubspace n))‖ < η ∧
        ‖completedPairing D b (V j (x i))‖ < η := by
  classical
  let K₀ := max B (Finset.univ.sup (fun i => (a i).support.sup id))
  have htail : ∀ᶠ K : ℕ in atTop, K₀ ≤ K ∧ ∀ i j, ∀ b : C00 𝕜,
      b ∈ afterCutoff K → DualUnit (implicitNorm D) b →
        ‖completedPairing D b (V j (x i))‖ < η := by
    apply (eventually_ge_atTop K₀).and
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    exact eventually_tail_dualUnit_small D _ hη
  obtain ⟨K,hK,htailK⟩ := htail.exists
  have hfront : ∀ᶠ n : ℕ in atTop, ∀ i j,
      ‖completedPairing D (a i) (V j (u.inSubspace n))‖ < η := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hh := u.tendsto_subspace_functional_zero ((completedPairing D (a i)).comp (V j))
    exact hh.norm.eventually_lt_const (by simpa only [norm_zero] using hη)
  have hex := ((u.eventually_finite_tail_near_norming T K hδ).and hfront).and
    (eventually_gt_atTop (max L B))
  obtain ⟨n,⟨⟨b,hbK,hbu,hbnorm⟩,hfrontn⟩,hn⟩ := hex.exists
  have hBK : B ≤ K := (le_max_left _ _).trans hK
  have hnb : B < n := (le_max_right _ _).trans_lt hn
  have hun : u.vector n ∈ afterCutoff B := by
    intro s hs
    apply Finsupp.notMem_support_iff.mp
    intro hsn
    have hi := block_index_le_support u.vector u.successive hne n s hsn
    omega
  refine ⟨n,b,(le_max_left _ _).trans_lt hn,hun,
    (fun s hs => hbK s (hs.trans hBK)),hbu,?_,?_,?_⟩
  · have hh := hbad n
    linarith
  · intro i
    apply before_of_mem_afterCutoff (K := K) _ hbK
    intro s hs
    exact (Finset.le_sup (f := id) hs).trans ((Finset.le_sup
      (f := fun i => (a i).support.sup id) (Finset.mem_univ i)).trans
        ((le_max_right _ _).trans hK))
  · intro i j
    exact ⟨hfrontn i j,htailK i j b hbK hbu⟩

end ThesisCommon.GowersMaurey
