import ThesisCommon.Analysis.MatrixSumOperators

/-! Actual contractive copies in full subsequence coordinate subspaces of the
bounded product of finite matrix blocks. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000

private def initialMatrixEmbedding {a b : ℕ} (h : a ≤ b) : Fin (a+1) ↪ Fin (b+1) :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right h 1)⟩,
    fun _ _ hij => Fin.ext (congrArg (fun j : Fin (b+1) => j.val) hij)⟩

private theorem matrixInsert_apply_norm_le (p : BanachExponent) {a b : ℕ}
    (α τ : Fin a ↪ Fin b) (x : FiniteMatrixBlock 𝕜 p a) :
    ‖matrixInsert p α τ x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using ((matrixInsert (𝕜 := 𝕜) p α τ).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_matrixInsert_le (𝕜 := 𝕜) p α τ) (norm_nonneg x))

private theorem matrixRestrict_apply_norm_le (p : BanachExponent) {a b : ℕ}
    (α τ : Fin a ↪ Fin b) (x : FiniteMatrixBlock 𝕜 p b) :
    ‖matrixRestrict p α τ x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using ((matrixRestrict (𝕜 := 𝕜) p α τ).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_matrixRestrict_le (𝕜 := 𝕜) p α τ) (norm_nonneg x))

private def matrixSubsequenceValue (p : BanachExponent) (n : ℕ → ℕ)
    (hn : ∀ i, i ≤ n i) (x : FiniteMatrixSum 𝕜 p) (j : ℕ) :
    FiniteMatrixBlock 𝕜 p (j+1) := by
  classical
  exact if h : j ∈ Set.range n then
    matrixInsert p (initialMatrixEmbedding ((hn h.choose).trans_eq h.choose_spec))
      (initialMatrixEmbedding ((hn h.choose).trans_eq h.choose_spec)) (x h.choose)
    else 0

private theorem matrixSubsequenceValue_norm_le (p : BanachExponent) (n : ℕ → ℕ)
    (hn : ∀ i, i ≤ n i) (x : FiniteMatrixSum 𝕜 p) (j : ℕ) :
    ‖matrixSubsequenceValue p n hn x j‖ ≤ ‖x‖ := by
  classical
  unfold matrixSubsequenceValue
  split_ifs with h
  · exact (matrixInsert_apply_norm_le p _ _ (x h.choose)).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x h.choose)
  · simpa only [norm_zero] using norm_nonneg x

def matrixSubsequenceInsert (p : BanachExponent) (n : ℕ → ℕ) (hn : ∀ i, i ≤ n i) :
    FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun x => ⟨matrixSubsequenceValue p n hn x, memℓp_infty ⟨‖x‖, ?_⟩⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · rintro _ ⟨j, rfl⟩
    exact matrixSubsequenceValue_norm_le p n hn x j
  · intro x y
    apply lp.ext
    funext j
    change matrixSubsequenceValue p n hn (x+y) j =
      matrixSubsequenceValue p n hn x j + matrixSubsequenceValue p n hn y j
    unfold matrixSubsequenceValue
    split_ifs <;> simp only [lp.coeFn_add, Pi.add_apply, map_add, add_zero]
  · intro a x
    apply lp.ext
    funext j
    change matrixSubsequenceValue p n hn (a • x) j = a • matrixSubsequenceValue p n hn x j
    unfold matrixSubsequenceValue
    split_ifs <;> simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_zero]
  · intro x
    rw [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg _) (matrixSubsequenceValue_norm_le p n hn x)

theorem matrixSubsequenceInsert_support (p : BanachExponent) (n : ℕ → ℕ)
    (hn : ∀ i, i ≤ n i) (x : FiniteMatrixSum 𝕜 p) :
    matrixSubsequenceInsert p n hn x ∈ matrixSumSupport p (Set.range n) := by
  classical
  intro j hj
  change matrixSubsequenceValue p n hn x j = 0
  simp only [matrixSubsequenceValue, dif_neg hj]

private theorem matrixSubsequenceInsert_apply_eq (p : BanachExponent) (n : ℕ → ℕ)
    (hinj : Function.Injective n) (hn : ∀ i, i ≤ n i) (x : FiniteMatrixSum 𝕜 p)
    (i j : ℕ) (hij : n i = j) :
    matrixSubsequenceInsert p n hn x j =
      matrixInsert p (initialMatrixEmbedding ((hn i).trans_eq hij))
        (initialMatrixEmbedding ((hn i).trans_eq hij)) (x i) := by
  classical
  change matrixSubsequenceValue p n hn x j = _
  unfold matrixSubsequenceValue
  have hi : j ∈ Set.range n := ⟨i, hij⟩
  rw [dif_pos hi]
  have heq : hi.choose = i := hinj (hi.choose_spec.trans hij.symm)
  subst i
  rfl

theorem matrixSubsequenceInsert_apply_image (p : BanachExponent) (n : ℕ → ℕ)
    (hinj : Function.Injective n) (hn : ∀ i, i ≤ n i) (x : FiniteMatrixSum 𝕜 p) (i : ℕ) :
    matrixSubsequenceInsert p n hn x (n i) =
      matrixInsert p (initialMatrixEmbedding (hn i)) (initialMatrixEmbedding (hn i)) (x i) :=
  matrixSubsequenceInsert_apply_eq p n hinj hn x i (n i) rfl

theorem norm_matrixSubsequenceInsert_le (p : BanachExponent) (n : ℕ → ℕ)
    (hn : ∀ i, i ≤ n i) : ‖matrixSubsequenceInsert (𝕜 := 𝕜) p n hn‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

def matrixSubsequenceRead (p : BanachExponent) (n : ℕ → ℕ) (hn : ∀ i, i ≤ n i) :
    FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => matrixRestrict p (initialMatrixEmbedding (hn i))
          (initialMatrixEmbedding (hn i)) (x (n i)), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact (matrixRestrict_apply_norm_le p _ _ (x (n i))).trans
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x (n i))⟩⟩
      map_add' := by intros; apply lp.ext; funext i; exact map_add _ _ _
      map_smul' := by
        intro a x
        apply lp.ext
        funext i
        exact map_smul (matrixRestrict (𝕜 := 𝕜) p
          (initialMatrixEmbedding (hn i)) (initialMatrixEmbedding (hn i))) a (x (n i)) }
    1 (fun x => by
      rw [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro i
      exact (matrixRestrict_apply_norm_le p _ _ (x (n i))).trans
        (lp.norm_apply_le_norm ENNReal.top_ne_zero x (n i)))

theorem norm_matrixSubsequenceRead_le (p : BanachExponent) (n : ℕ → ℕ)
    (hn : ∀ i, i ≤ n i) : ‖matrixSubsequenceRead (𝕜 := 𝕜) p n hn‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem matrixSubsequenceRead_comp_insert (p : BanachExponent) (n : ℕ → ℕ)
    (hinj : Function.Injective n) (hn : ∀ i, i ≤ n i) :
    (matrixSubsequenceRead (𝕜 := 𝕜) p n hn).comp (matrixSubsequenceInsert p n hn) =
      ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  change matrixRestrict p _ _ (matrixSubsequenceInsert p n hn x (n i)) = x i
  rw [matrixSubsequenceInsert_apply_image p n hinj hn]
  exact DFunLike.congr_fun (matrixRestrict_comp_insert p _ _) (x i)

end ThesisCommon
