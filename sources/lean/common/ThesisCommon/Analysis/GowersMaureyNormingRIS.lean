import ThesisCommon.Analysis.GowersMaureyNormingSequences
import ThesisCommon.Analysis.GowersMaureyNPairConstruction

/-! Actual norm-detecting RIS blocks, with successive finite norming
functionals and simultaneous small cross pairings. This selection uses
only a genuine large-image block sequence, not orbit separation. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_norming_RIS_after_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ n, u.vector n ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) {r δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hbad : ∀ n, r+2*δ < ‖T (u.inSubspace n)‖)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Y) (a : ι → C00 𝕜) (V : κ → Y →L[𝕜] ShiftSpace D)
    (B L N : ℕ) :
    ∃ c : Fin N → ℕ, ∃ b : Fin N → C00 𝕜, StrictMono c ∧
      (∀ n, L < c n) ∧ (∀ n, u.vector (c n) ∈ afterCutoff B) ∧
      (∀ n, b n ∈ afterCutoff B) ∧ Successive b ∧
      IsRIS D 1 (fun n => u.vector (c n)) ∧
      (∀ n, DualUnit (implicitNorm D) (b n)) ∧
      (∀ n, r < RCLike.re (completedPairing D (b n) (T (u.inSubspace (c n))))) ∧
      (∀ i n, Before (a i) (b n)) ∧
      (∀ i n j, ‖completedPairing D (a i) (V j (u.inSubspace (c n)))‖ < η ∧
        ‖completedPairing D (b n) (V j (x i))‖ < η) ∧
      ∀ i n, i ≠ n → ∀ j,
        ‖completedPairing D (b i) (V j (u.inSubspace (c n)))‖ < η := by
  obtain ⟨c,b,hc,hcL,hvB,hbB,hbs,hbu,hdet,hbefore,hcross,hinternal⟩ :=
    exists_norming_block_sequence_after_family u hne T hδ hη hbad x a V B L
  have hbound (n : ℕ) : intervalNorm D (n+1) (u.vector (c n)) ≤ 1 :=
    (intervalNorm_mono D (Nat.add_le_add_right (hc.id_le n) 1) _).trans (u.norm_bound _)
  obtain ⟨d,hd,hRIS⟩ := exists_RIS_subsequence D (fun n => u.vector (c n))
    (fun n => n+1) (fun i j hij => u.successive _ _ (hc hij))
    (fun n => hne _) (fun _ _ h => Nat.add_lt_add_right h 1) hbound N
    (ε := 1) (by norm_num) (le_refl 1)
  refine ⟨fun n => c (d n),fun n => b (d n),hc.comp hd,
    fun n => hcL _,fun n => hvB _,fun n => hbB _,
    fun i j hij => hbs _ _ (hd hij),hRIS,fun n => hbu _,fun n => hdet _,
    fun i n => hbefore i _,fun i n j => hcross i _ j,?_⟩
  intro i n hin j
  exact hinternal _ _ (hd.injective.ne hin) j

theorem exists_norming_RIS_of_lt_seminorm
    (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    (T : Y →L[𝕜] ShiftSpace D) {r η : ℝ} (hr0 : 0 ≤ r) (hη : 0 < η)
    (hr : r < blockOperatorSeminorm D Y T)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Y) (a : ι → C00 𝕜) (V : κ → Y →L[𝕜] ShiftSpace D)
    (B N : ℕ) :
    ∃ v b : Fin N → C00 𝕜, ∃ hv : ∀ n, denseEmbedding D (v n) ∈ Y,
      (∀ n, v n ∈ afterCutoff B) ∧ (∀ n, b n ∈ afterCutoff B) ∧
      Successive b ∧ IsRIS D 1 v ∧
      (∀ n, DualUnit (implicitNorm D) (b n)) ∧
      (∀ n, r < RCLike.re (completedPairing D (b n)
        (T ⟨denseEmbedding D (v n),hv n⟩))) ∧
      (∀ i n, Before (a i) (b n)) ∧
      (∀ i n j, ‖completedPairing D (a i)
          (V j ⟨denseEmbedding D (v n),hv n⟩)‖ < η ∧
        ‖completedPairing D (b n) (V j (x i))‖ < η) ∧
      ∀ i n, i ≠ n → ∀ j,
        ‖completedPairing D (b i) (V j ⟨denseEmbedding D (v n),hv n⟩)‖ < η := by
  let δ := (blockOperatorSeminorm D Y T-r)/4
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hgap : r+2*δ < blockOperatorSeminorm D Y T := by dsimp only [δ]; linarith
  obtain ⟨u,hne,_,hbad⟩ := exists_bad_blockTestSequence_after D Y T
    (show 0 ≤ r+2*δ by positivity) hgap B
  obtain ⟨c,b,_,_,hvB,hbB,hbs,hRIS,hbu,hdet,hbefore,hcross,hinternal⟩ :=
    exists_norming_RIS_after_family u hne T hδ hη hbad x a V B 0 N
  exact ⟨fun n => u.vector (c n),b,fun n => u.mem_subspace _,hvB,hbB,
    hbs,hRIS,hbu,hdet,hbefore,hcross,hinternal⟩

end ThesisCommon.GowersMaurey
