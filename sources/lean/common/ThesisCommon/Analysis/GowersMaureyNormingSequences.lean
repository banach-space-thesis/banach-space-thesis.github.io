import ThesisCommon.Analysis.GowersMaureyNormingExtension

/-! Successive genuine near-norming functionals for actual block tests.
Cross terms are controlled for every member of an arbitrary finite operator
family, including interactions with a previously selected finite family. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_norming_block_sequence_after_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ n, u.vector n ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) {r δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hbad : ∀ n, r+2*δ < ‖T (u.inSubspace n)‖)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Y) (a : ι → C00 𝕜) (V : κ → Y →L[𝕜] ShiftSpace D)
    (B L : ℕ) :
    ∃ c : ℕ → ℕ, ∃ b : ℕ → C00 𝕜, StrictMono c ∧
      (∀ n, L < c n) ∧ (∀ n, u.vector (c n) ∈ afterCutoff B) ∧
      (∀ n, b n ∈ afterCutoff B) ∧
      (∀ i j, i < j → Before (b i) (b j)) ∧
      (∀ n, DualUnit (implicitNorm D) (b n)) ∧
      (∀ n, r < RCLike.re (completedPairing D (b n) (T (u.inSubspace (c n))))) ∧
      (∀ i n, Before (a i) (b n)) ∧
      (∀ i n j, ‖completedPairing D (a i) (V j (u.inSubspace (c n)))‖ < η ∧
        ‖completedPairing D (b n) (V j (x i))‖ < η) ∧
      ∀ i n, i ≠ n → ∀ j,
        ‖completedPairing D (b i) (V j (u.inSubspace (c n)))‖ < η := by
  classical
  let A := ℕ × C00 𝕜
  let P (v : A) := L < v.1 ∧ u.vector v.1 ∈ afterCutoff B ∧
    v.2 ∈ afterCutoff B ∧ DualUnit (implicitNorm D) v.2 ∧
    r < RCLike.re (completedPairing D v.2 (T (u.inSubspace v.1))) ∧
    (∀ i, Before (a i) v.2) ∧ ∀ i j,
      ‖completedPairing D (a i) (V j (u.inSubspace v.1))‖ < η ∧
      ‖completedPairing D v.2 (V j (x i))‖ < η
  let R (v w : A) := v.1 < w.1 ∧ Before v.2 w.2 ∧ ∀ j,
    ‖completedPairing D v.2 (V j (u.inSubspace w.1))‖ < η ∧
    ‖completedPairing D w.2 (V j (u.inSubspace v.1))‖ < η
  have hselect : ∀ s : Finset A, (∀ v ∈ s, P v) → ∃ w, P w ∧ ∀ v ∈ s, R v w := by
    intro s _
    let x' : ι ⊕ s → Y := Sum.elim x (fun v => u.inSubspace v.val.1)
    let a' : ι ⊕ s → C00 𝕜 := Sum.elim a (fun v => v.val.2)
    obtain ⟨n,b,hn,hun,hb,hbu,hdet,hbefore,hcross⟩ := exists_norming_block_after_family
      u hne T hδ hη hbad x' a' V B (max L (s.sup Prod.fst))
    refine ⟨(n,b),⟨(le_max_left _ _).trans_lt hn,hun,hb,hbu,hdet,
      fun i => hbefore (Sum.inl i),fun i j => hcross (Sum.inl i) j⟩,?_⟩
    intro v hv
    refine ⟨(Finset.le_sup (f := Prod.fst) hv).trans_lt
      ((le_max_right _ _).trans_lt hn),hbefore (Sum.inr ⟨v,hv⟩),?_⟩
    intro j
    exact hcross (Sum.inr ⟨v,hv⟩) j
  obtain ⟨w,hw,hwr⟩ := exists_seq_of_forall_finset_exists P R hselect
  refine ⟨fun n => (w n).1,fun n => (w n).2,
    fun i j hij => (hwr i j hij).1,fun n => (hw n).1,fun n => (hw n).2.1,
    fun n => (hw n).2.2.1,fun i j hij => (hwr i j hij).2.1,
    fun n => (hw n).2.2.2.1,fun n => (hw n).2.2.2.2.1,
    fun i n => (hw n).2.2.2.2.2.1 i,
    fun i n j => (hw n).2.2.2.2.2.2 i j,?_⟩
  intro i n hin j
  rcases lt_or_gt_of_ne hin with h | h
  · exact ((hwr i n h).2.2 j).1
  · exact ((hwr n i h).2.2 j).2

end ThesisCommon.GowersMaurey
