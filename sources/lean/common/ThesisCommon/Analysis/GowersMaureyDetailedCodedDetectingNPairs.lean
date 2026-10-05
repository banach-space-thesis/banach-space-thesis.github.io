import ThesisCommon.Analysis.GowersMaureyDetailedDetectingNPairs
import ThesisCommon.Analysis.GowersMaureyCompletedPairingMass
import ThesisCommon.Analysis.GowersMaureyAveragedCodeApproximation

/-! Refined detecting N-pairs retaining the actual normalized RIS vector.
Detecting N-pairs with genuine Gaussian-rational coding functionals.
The perturbation has an explicit mass budget preserving detection and the
small finite-orbit evaluations, while its actual code can be arbitrarily large. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_coded_detecting_NPair_with_RIS
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖) (m B M : ℕ) (W : C00 𝕜 → ℝ)
    (xs : List (C00 𝕜)) (hxs : CodingDomain xs)
    (hxsB : ∀ a ∈ xs, ∀ j ∈ a.support, j ≤ B) :
    ∃ x : C00 𝕜, ∃ hx : denseEmbedding D x ∈ Y, ∃ a : C00 𝕜,
      x ∈ afterCutoff B ∧ a ∈ afterCutoff B ∧ implicitNorm D x ≤ 4 ∧
      (∃ v : Fin (D.j (2*m+1)) → C00 𝕜, IsRIS D 1 v ∧ x = normalizedPairVector v) ∧
      (∃ b : Fin (D.j (2*m+1)) → ℕ, StrictMono b ∧ (∀ i, B < b i) ∧
        x = normalizedPairVector (fun i => u.vector (b i))) ∧
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ) →
        intervalNorm D n x ≤ 8) ∧
      AveragedFunctional (implicitNorm D) (D.j (2*m+1)) a ∧ a ≠ 0 ∧
      RationalUnitSequence a ∧ CodingDomain (xs ++ [a]) ∧
      M < D.sigma (xs ++ [a]) ∧
      pairingSpreadCutoff a x < D.sigma (xs ++ [a]) ∧
      W x < logarithmicWeight (D.sigma (xs ++ [a])) ∧
      ε/16 < RCLike.re (completedPairing D a (T ⟨denseEmbedding D x,hx⟩)) ∧
      ∀ z ∈ spreadParameterSquare (D.j (2*m+1)),
        ‖pairing a (spread z.1 z.2 x)‖ ≤ (‖T‖+1) / (D.j (2*m+1) : ℝ)^2 := by
  obtain ⟨x,hx,a,hxB,haB,hxnorm,hRIS,hsource,hinterval,ha,ha0,hdetect,horbit⟩ :=
    exists_detecting_NPair_with_RIS u hne T q hq hε hsep m B
  let N := D.j (2*m+1)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast D.j_positive (2*m+1)
  let C := 5+4*‖T‖
  have hC : 0 < C := by dsimp [C]; positivity
  let τ := min (ε/16) (1/(N : ℝ)^2)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  obtain ⟨b,hb0,hb,hr,hs,hcode,hmass,hM,hW⟩ := D.exists_large_code_averaged_near
    hxs ha ha0 (fun a' ha' => before_of_mem_afterCutoff (hxsB a' ha') haB)
    (div_pos hτ hC) (max M (pairingSpreadCutoff a x)) (W x)
  have hbB : b ∈ afterCutoff B := by
    intro j hj
    apply Finsupp.notMem_support_iff.mp
    intro hjb
    exact Finsupp.mem_support_iff.mp (hs hjb) (haB j hj)
  have herr (y : ShiftSpace D) (hy : ‖y‖ ≤ C) :
      ‖completedPairing D b y - completedPairing D a y‖ < τ := by
    calc
      _ ≤ mass (b-a)*‖y‖ := completedPairing_sub_norm_le_mass_mul D b a y
      _ ≤ mass (b-a)*C := mul_le_mul_of_nonneg_left hy (apply_nonneg _ _)
      _ < (τ/C)*C := mul_lt_mul_of_pos_right hmass hC
      _ = τ := div_mul_cancel₀ _ hC.ne'
  have hxy : ‖(⟨denseEmbedding D x,hx⟩ : Y)‖ ≤ 4 := by
    change ‖denseEmbedding D x‖ ≤ 4
    rw [denseEmbedding_norm]
    exact hxnorm
  have hTy : ‖T ⟨denseEmbedding D x,hx⟩‖ ≤ C := by
    apply (T.le_opNorm _).trans
    apply (mul_le_mul_of_nonneg_left hxy (norm_nonneg T)).trans
    dsimp [C]
    nlinarith
  have herrT := (herr (T ⟨denseEmbedding D x,hx⟩) hTy).trans_le (min_le_left _ _)
  have hdetb : ε/16 < RCLike.re (completedPairing D b (T ⟨denseEmbedding D x,hx⟩)) := by
    have hre := RCLike.re_le_norm (completedPairing D a (T ⟨denseEmbedding D x,hx⟩) -
      completedPairing D b (T ⟨denseEmbedding D x,hx⟩))
    rw [map_sub,norm_sub_rev] at hre
    linarith
  have hcut : pairingSpreadCutoff b x ≤ pairingSpreadCutoff a x :=
    max_le_max_right _ (Finset.sup_mono hs)
  refine ⟨x,hx,b,hxB,hbB,hxnorm,hRIS,hsource,hinterval,hb,hb0,hr,hcode,
    (le_max_left _ _).trans_lt hM,hcut.trans_lt ((le_max_right _ _).trans_lt hM),hW,hdetb,?_⟩
  intro z hz
  have hyv : ‖completedSpread D z.1 z.2 (denseEmbedding D x)‖ ≤ C := by
    apply (completedSpread_norm_le D _ _ _).trans
    rw [denseEmbedding_norm]
    apply hxnorm.trans
    dsimp [C]
    have ht := norm_nonneg T
    linarith
  have he := (herr _ hyv).trans_le (min_le_right _ _)
  have hea : completedPairing D a (completedSpread D z.1 z.2 (denseEmbedding D x)) =
      pairing a (spread z.1 z.2 x) := by
    rw [completedSpread_denseEmbedding, completedPairing_denseEmbedding]
    rfl
  have heb : completedPairing D b (completedSpread D z.1 z.2 (denseEmbedding D x)) =
      pairing b (spread z.1 z.2 x) := by
    rw [completedSpread_denseEmbedding, completedPairing_denseEmbedding]
    rfl
  rw [hea,heb] at he
  calc
    _ = ‖(pairing b (spread z.1 z.2 x)-pairing a (spread z.1 z.2 x)) +
        pairing a (spread z.1 z.2 x)‖ := by rw [sub_add_cancel]
    _ ≤ ‖pairing b (spread z.1 z.2 x)-pairing a (spread z.1 z.2 x)‖ +
        ‖pairing a (spread z.1 z.2 x)‖ := norm_add_le _ _
    _ ≤ 1/(N : ℝ)^2 + ‖T‖/(N : ℝ)^2 := add_le_add he.le (horbit z hz)
    _ = (‖T‖+1)/(N : ℝ)^2 := by ring

end ThesisCommon.GowersMaurey


