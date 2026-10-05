import ThesisCommon.Analysis.UncountableSchauderCompression
import ThesisCommon.Analysis.CardinalFactorSelection

/-! Fibre factorisations assemble into bounded diagonal maps on the actual
sum. Exact coordinate compression transfers them without enlarging the
constant. Full-cardinality and cofinality selection are separate checked
ingredients, so the uniform result has no cofinality restriction. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon.UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

theorem diagonal_factorsIdentityWith (F : Γ → X →L[𝕜] X)
    (M : ℝ) (hM : 0 ≤ M) (hF : ∀ i, ‖F i‖ ≤ M)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, FactorsIdentityWith (F i) X C) :
    FactorsIdentityWith (diagonal (b := b) (hb := hb) F M hM hF)
      (UncountableSchauderSum b hb X) C := by
  classical
  choose U V hUV hU hV using fun i => (hf i).normalized
  refine ⟨diagonal U C hC hU, diagonal V 1 zero_le_one hV, ?_, ?_⟩
  · ext x i
    change U i (F i (V i (x i))) = x i
    exact DFunLike.congr_fun (hUV i) (x i)
  · have h := mul_le_mul (norm_diagonal_le (b := b) (hb := hb) U C hC hU)
      (norm_diagonal_le (b := b) (hb := hb) V 1 zero_le_one hV)
      (norm_nonneg (diagonal (b := b) (hb := hb) V 1 zero_le_one hV)) hC
    simpa only [mul_one] using h

/-- Uniform fibre factorizations on a full-size diagonal coordinate set
factor the identity of the whole sum through the original operator. -/
theorem factorsIdentityWith_of_full_diagonal_set [Nonempty Γ]
    (hs : b.HasSymmetricNorm)
    (T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X)
    (H : Set Γ) (hcard : Cardinal.mk H = Cardinal.mk Γ)
    (hoff : ∀ α ∈ H, ∀ β ∈ H, α ≠ β → fibreEntry T β α = 0)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ α ∈ H, FactorsIdentityWith (fibreEntry T α α) X C) :
    FactorsIdentityWith T (UncountableSchauderSum b hs.1 X) C := by
  classical
  obtain ⟨e⟩ := Cardinal.eq.mp hcard.symm
  let f : Γ ↪ Γ := ⟨fun i => (e i).val, fun _ _ h => e.injective (Subtype.ext h)⟩
  have hfH (i : Γ) : f i ∈ H := (e i).property
  obtain ⟨A, B, _hAB, hA, hB, hAx, hBx, _hBn⟩ :=
    exists_reindexed_compression (X := X) hs f
  have hD := compression_eq_diagonal f T A B hAx hBx
    (fun i j hij => hoff (f i) (hfH i) (f j) (hfH j) (fun he => hij (f.injective he)))
  have hfact : FactorsIdentityWith ((A.comp T).comp B)
      (UncountableSchauderSum b hs.1 X) C := by
    rw [hD]
    exact diagonal_factorsIdentityWith _ _ (norm_nonneg T)
      (fun i => norm_fibreEntry_le T (f i) (f i)) hC (fun i => hf (f i) (hfH i))
  apply (hfact.of_compression A B).mono
  have hAB : ‖A‖ * ‖B‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hA hB (norm_nonneg B) zero_le_one
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hAB hC

theorem factorsIdentityWith_complement_of_full_diagonal_set [Nonempty Γ]
    (hs : b.HasSymmetricNorm)
    (T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X)
    (H : Set Γ) (hcard : Cardinal.mk H = Cardinal.mk Γ)
    (hoff : ∀ α ∈ H, ∀ β ∈ H, α ≠ β → fibreEntry T β α = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ α ∈ H, FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - fibreEntry T α α) X C) :
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T)
      (UncountableSchauderSum b hs.1 X) C := by
  apply factorsIdentityWith_of_full_diagonal_set hs _ H hcard
  · intro α hα β hβ hne
    rw [fibreEntry_complement_offDiagonal T (Ne.symm hne), hoff α hα β hβ hne, neg_zero]
  · exact hC
  · intro α hα
    rw [fibreEntry_complement_diagonal]
    exact hf α hα

/-- Transfer a fixed uniform bound, assuming the proved exact diagonal
selection conclusion for each actual bounded operator. -/
theorem hasCPFP_of_diagonal_selection (hs : b.HasSymmetricNorm)
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hsel : ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
        ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β → coordinateEntry T β α = 0)
    {C : ℝ} (hC : 0 ≤ C) (hX : HasCPFP 𝕜 X C) :
    HasCPFP 𝕜 (UncountableSchauderSum b hs.1 X) C := by
  haveI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ
  intro T
  obtain ⟨Λ, hΛ, hoff⟩ := hsel T
  rcases full_cardinal_factor_branch hΓ Λ hΛ (fun γ => fibreEntry T γ γ)
    (fun γ _ => hX (fibreEntry T γ γ)) with h | h
  · obtain ⟨H, hH, hcard, hf⟩ := h
    exact Or.inl (factorsIdentityWith_of_full_diagonal_set hs T H hcard
      (fun α hα β hβ hne => fibreEntry_eq_zero_of_coordinateEntry_eq_zero T β α
        (hoff α (hH hα) β (hH hβ) hne)) hC hf)
  · obtain ⟨H, hH, hcard, hf⟩ := h
    exact Or.inr (factorsIdentityWith_complement_of_full_diagonal_set hs T H hcard
      (fun α hα β hβ hne => fibreEntry_eq_zero_of_coordinateEntry_eq_zero T β α
        (hoff α (hH hα) β (hH hβ) hne)) hC hf)

/-- Nonuniform PFP needs uncountable cofinality only to obtain one uniform
bound on a full-cardinality coordinate set. -/
theorem hasPFP_of_diagonal_selection (hs : b.HasSymmetricNorm)
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof)
    (hsel : ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
        ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β → coordinateEntry T β α = 0)
    (hX : HasPFP 𝕜 X) : HasPFP 𝕜 (UncountableSchauderSum b hs.1 X) := by
  haveI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ
  intro T
  obtain ⟨Λ, hΛ, hoff⟩ := hsel T
  obtain ⟨C, hC, h⟩ := full_cardinal_bounded_factor_branch hΓ hcof Λ hΛ
    (fun γ => fibreEntry T γ γ) (fun γ _ => hX (fibreEntry T γ γ))
  rcases h with h | h
  · obtain ⟨H, hH, hcard, hf⟩ := h
    exact Or.inl (factorsIdentityWith_of_full_diagonal_set hs T H hcard
      (fun α hα β hβ hne => fibreEntry_eq_zero_of_coordinateEntry_eq_zero T β α
        (hoff α (hH hα) β (hH hβ) hne)) (zero_le_one.trans hC) hf).forget_bound
  · obtain ⟨H, hH, hcard, hf⟩ := h
    exact Or.inr (factorsIdentityWith_complement_of_full_diagonal_set hs T H hcard
      (fun α hα β hβ hne => fibreEntry_eq_zero_of_coordinateEntry_eq_zero T β α
        (hoff α (hH hα) β (hH hβ) hne)) (zero_le_one.trans hC) hf).forget_bound

end ThesisCommon.UncountableSchauderSum
