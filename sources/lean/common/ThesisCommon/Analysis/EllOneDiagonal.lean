import ThesisCommon.Analysis.BoundedColumnSelection
import ThesisCommon.Analysis.PositiveMatrix
import ThesisCommon.Analysis.SequenceEntryAlgebra
import ThesisCommon.Analysis.SharpFactorization
import ThesisCommon.Analysis.ScalarPFP

/-! Theorem 3.11 of Primariness and the Primary Factorisation Property.
Select nested infinite sets with small future row entries and small column
tails, compress to a diagonal, and apply the scalar dichotomy and Neumann
correction. This is the manuscript's method, with a summable error budget.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The two simultaneous estimates in the recursive construction in 3.11.
The tail estimate controls every finite subsum, which suffices for the norm. -/
theorem ellOne_two_sided_selection
    (T : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ f : ℕ ↪ ℕ, StrictMono f ∧
      (∀ i j, i < j → ‖T (lp.single 1 (f j) (1 : 𝕜)) (f i)‖ < δ i) ∧
      (∀ j (F : Finset ℕ), (∀ i ∈ F, j < i) →
        ∑ i ∈ F, ‖T (lp.single 1 (f j) (1 : 𝕜)) (f i)‖ < δ j) := by
  obtain ⟨f, hf, _, hfuture, htail⟩ := bounded_columns_two_sided_selection
    (fun n m => ‖T (lp.single 1 m (1 : 𝕜)) n‖) (fun _ _ => norm_nonneg _)
    (ellOne_column_sum_le T) δ hδ (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  exact ⟨f, hf, hfuture, htail⟩

/-- Every ℓ₁ operator has an arbitrarily close diagonal compression by
the paper's coordinate restriction and insertion maps. -/
theorem ellOne_diagonal_compression
    (T : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ f : ℕ ↪ ℕ, ‖((lpRestrict 1 f).comp T).comp (lpExtend 1 f) -
      lpDiagonalPart (((lpRestrict 1 f).comp T).comp (lpExtend 1 f))‖ < η := by
  classical
  let δ : ℕ → ℝ := fun k => (η / 4) * (1 / 2 : ℝ) ^ k
  have hδ : ∀ k, 0 < δ k := fun k => mul_pos (by positivity) (pow_pos (by norm_num) k)
  have hsum : HasSum δ (η / 2) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (η / 4) using 1
    norm_num
    ring
  obtain ⟨f, _, hfuture, htail⟩ := ellOne_two_sided_selection T δ hδ
  let S := ((lpRestrict (𝕜 := 𝕜) 1 f).comp T).comp (lpExtend 1 f)
  let R := S - lpDiagonalPart S
  have hentry (i j : ℕ) :
      R (lp.single 1 j (1 : 𝕜)) i =
        if i = j then 0 else T (lp.single 1 (f j) (1 : 𝕜)) (f i) := by
    change S (lp.single 1 j 1) i -
      lpEntry S i i ((lp.single 1 j (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) 1) i) = _
    by_cases hij : i = j
    · subst i
      simp only [lp.single_apply_self, lpEntry_apply, sub_self, ite_true]
    · rw [lp.single_apply_ne 1 j 1 hij, map_zero, sub_zero, if_neg hij]
      change T (lpExtend (𝕜 := 𝕜) 1 f (lp.single 1 j 1)) (f i) = _
      rw [lpExtend_single]
  have hR : ‖R‖ ≤ 3 * η / 4 := by
    apply ellOne_norm_le_of_columns R (by positivity)
    intro j
    apply lp.norm_le_of_forall_sum_le (by simp : 0 < (1 : ℝ≥0∞).toReal) (by positivity)
    intro F
    simp only [ENNReal.toReal_one, Real.rpow_one]
    let past := F.filter (fun i => i < j)
    let rest := F.filter (fun i => ¬ i < j)
    have hpast : ∑ i ∈ past, ‖R (lp.single 1 j (1 : 𝕜)) i‖ ≤ η / 2 := by
      calc
        _ ≤ ∑ i ∈ past, δ i := Finset.sum_le_sum (by
          intro i hi
          have hij := (Finset.mem_filter.mp hi).2
          rw [hentry, if_neg (ne_of_lt hij)]
          exact (hfuture i j hij).le)
        _ ≤ ∑' i, δ i := hsum.summable.sum_le_tsum _ (fun i _ => (hδ i).le)
        _ = η / 2 := hsum.tsum_eq
    have hrest : ∑ i ∈ rest, ‖R (lp.single 1 j (1 : 𝕜)) i‖ < δ j := by
      let later := rest.erase j
      have heq : ∑ i ∈ rest, ‖R (lp.single 1 j (1 : 𝕜)) i‖ =
          ∑ i ∈ later, ‖T (lp.single 1 (f j) (1 : 𝕜)) (f i)‖ := by
        calc
          _ = ∑ i ∈ later, ‖R (lp.single 1 j (1 : 𝕜)) i‖ := by
            symm
            exact Finset.sum_erase rest (by simp [hentry])
          _ = _ := Finset.sum_congr rfl (by
            intro i hi
            rw [hentry, if_neg (Finset.mem_erase.mp hi).1])
      rw [heq]
      apply htail j later
      intro i hi
      have hne := (Finset.mem_erase.mp hi).1
      have hnlt := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
      omega
    have hδle : δ j ≤ η / 4 := by
      apply mul_le_of_le_one_right (by positivity)
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun i => i < j)
      (fun i => ‖R (lp.single 1 j (1 : 𝕜)) i‖)
    change (∑ i ∈ past, _) + (∑ i ∈ rest, _) = _ at hsplit
    linarith
  refine ⟨f, ?_⟩
  exact hR.trans_lt (by linarith)

/-- The exact original Theorem 3.11, over either real or complex scalars. -/
theorem ellOne_hasCPlusPFP_two : HasCPlusPFP 𝕜 (lp (fun _ : ℕ => 𝕜) 1) 2 := by
  apply hasCPlusPFP_of_approximate_compressions (by norm_num : (0 : ℝ) < 2) IsLpDiagonal
  · exact fun D hD => lp_diagonal_dichotomy (by norm_num) scalar_hasCPFP_two D hD
  · intro T η hη
    obtain ⟨f, hf⟩ := ellOne_diagonal_compression T hη
    exact ⟨lpRestrict 1 f, lpExtend 1 f,
      lpDiagonalPart (((lpRestrict 1 f).comp T).comp (lpExtend 1 f)),
      lpRestrict_comp_extend f, norm_lpRestrict_le f, norm_lpExtend_le f,
      isLpDiagonal_lpDiagonalPart _, hf⟩

end ThesisCommon

