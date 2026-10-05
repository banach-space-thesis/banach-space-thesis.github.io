import ThesisCommon.Analysis.SchauderSumReindex

/-! The recursive step for compressing a full infinitely splitting subtree:
restrict outer coordinates, compress each inner coordinate, and reverse those
steps for insertion. All operators act on the actual vector-valued sum.
-/
noncomputable section
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem diagonal_single (F : ℕ → Y →L[𝕜] Y) (C : ℝ) (hC hF) (n : ℕ) (y : Y) :
    diagonal (b := b) (hb := hb) F C hC hF (single n y) = single n (F n y) := by
  classical
  ext i
  simp only [diagonal_apply, single_apply]
  by_cases hi : i = n
  · subst i; simp
  · simp [hi]

/-- Compression and insertion when each selected coordinate has its own
contractive retraction pair. -/
theorem exists_reindexed_compression (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ)
    (A B : ℕ → Y →L[𝕜] Y)
    (hAB : ∀ i, (A i).comp (B i) = ContinuousLinearMap.id 𝕜 Y)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ∀ i, ‖B i‖ ≤ 1) :
    ∃ R E : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y,
      R.comp E = ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 1 ∧ ‖E‖ ≤ 1 ∧
      (∀ n y, E (single n y) = single (f n) (B n y)) ∧
      ∀ n y, R y n = A n (y (f n)) := by
  let DA := diagonal (b := b) (hb := hb) A 1 zero_le_one hA
  let DB := diagonal (b := b) (hb := hb) B 1 zero_le_one hB
  let R := DA.comp (restrictL (hb := hb) (Y := Y) hs f)
  let E := (extendL (hb := hb) (Y := Y) hs f).comp DB
  have hDA : ‖DA‖ ≤ 1 := norm_diagonal_le A 1 zero_le_one hA
  have hDB : ‖DB‖ ≤ 1 := norm_diagonal_le B 1 zero_le_one hB
  refine ⟨R, E, ?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro y
    change DA (restrictL (hb := hb) (Y := Y) hs f
      (extendL (hb := hb) (Y := Y) hs f (DB y))) = y
    rw [restrictL_extendL]
    ext i
    change A i (B i (y i)) = y i
    exact DFunLike.congr_fun (hAB i) (y i)
  · calc
      ‖R‖ ≤ ‖DA‖ * ‖restrictL (hb := hb) (Y := Y) hs f‖ := DA.opNorm_comp_le _
      _ ≤ 1 * 1 := mul_le_mul hDA (norm_restrictL_le hs f) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · calc
      ‖E‖ ≤ ‖extendL (hb := hb) (Y := Y) hs f‖ * ‖DB‖ :=
        (extendL (hb := hb) (Y := Y) hs f).opNorm_comp_le DB
      _ ≤ 1 * 1 := mul_le_mul (norm_extendL_le hs f) hDB (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · intro n y
    change extendL (hb := hb) (Y := Y) hs f (DB (single n y)) = _
    rw [show DB (single n y) = single n (B n y) from diagonal_single B 1 zero_le_one hB n y]
    exact extendL_single hs f n (B n y)
  · intro n y
    rfl

end SchauderSum

/-- A contractive insertion with a contractive left inverse preserves norms. -/
theorem norm_eq_of_contractive_retraction {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] X) (B : X →L[𝕜] Y) (hAB : A.comp B = ContinuousLinearMap.id 𝕜 X)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (x : X) : ‖B x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (B.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hB (norm_nonneg x)).trans_eq (one_mul _))
  · have heq : A (B x) = x := DFunLike.congr_fun hAB x
    calc
      ‖x‖ = ‖A (B x)‖ := congrArg norm heq.symm
      _ ≤ ‖B x‖ := (A.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans_eq (one_mul _))

end ThesisCommon
