import Posets.MatrixDomination
import JLMS.MatrixCompactness
import Mathlib.Analysis.Normed.Group.Tannery

/-! Noncompact bounded-row matrices have a coordinate-convergent sequence of
nonzero rows which stays uniformly away from its summable limit in ℓ¹. -/

noncomputable section
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

/-- The absolute mass of a scalar row beyond a column cutoff. -/
def absoluteRowTail (f : ℕ → 𝕜) (j : ℕ) : ℝ :=
  ∑' i, if j < i then ‖f i‖ else 0

theorem summable_absoluteRowTail {f : ℕ → 𝕜}
    (hf : Summable (fun i => ‖f i‖)) (j : ℕ) :
    Summable (fun i => if j < i then ‖f i‖ else 0) := by
  exact Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (fun i => by split_ifs <;> simp) hf

theorem absoluteRowTail_antitone {f : ℕ → 𝕜}
    (hf : Summable (fun i => ‖f i‖)) : Antitone (absoluteRowTail f) := by
  intro j l hjl
  exact (summable_absoluteRowTail hf l).tsum_le_tsum
    (fun i => by split_ifs <;> first | exact le_rfl | positivity | omega)
    (summable_absoluteRowTail hf j)

theorem absoluteRowTail_tendsto_zero {f : ℕ → 𝕜}
    (hf : Summable (fun i => ‖f i‖)) :
    Tendsto (absoluteRowTail f) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun j i => if j < i then ‖f i‖ else 0) (g := fun _ => (0 : ℝ)) hf
    (fun i => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop i] with j hj
      simp [not_lt.mpr hj]))
    (Eventually.of_forall (fun j i => by dsimp only; split_ifs <;> simp))
  simpa [absoluteRowTail] using h

theorem matrixTail_rowSum_eq (M : ScalarMatrix 𝕜) (j k : ℕ) :
    (∑' i, ‖matrixTail 𝕜 M j k i‖) = absoluteRowTail (M k) j := by
  unfold matrixTail absoluteRowTail
  apply tsum_congr
  intro i
  split_ifs <;> simp

theorem noncompactMatrix_exists_large_row_tails (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (hnc : ¬ IsCompactMatrix 𝕜 M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j, ∃ k, ε < absoluteRowTail (M k) j := by
  by_contra h
  push_neg at h
  apply hnc
  refine ⟨hM, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨j, hj⟩ := h (ε / 2) (by positivity)
  refine ⟨j, fun l hjl => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (matrixNorm_nonneg _ (boundedRows_matrixTail M hM l))]
  have hb : matrixNorm 𝕜 (matrixTail 𝕜 M l) ≤ ε / 2 := by
    apply ciSup_le
    intro k
    rw [matrixTail_rowSum_eq]
    exact (absoluteRowTail_antitone (hM.1 k) hjl).trans (hj k)
  linarith

theorem noncompactMatrix_exists_increasing_large_tails (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (hnc : ¬ IsCompactMatrix 𝕜 M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ n, ε < absoluteRowTail (M (r n)) n := by
  obtain ⟨ε, hε, hlarge⟩ := noncompactMatrix_exists_large_row_tails M hM hnc
  have hfreq (n : ℕ) : ∃ᶠ k in atTop, ε < absoluteRowTail (M k) n := by
    rw [frequently_atTop']
    intro K
    have he : ∀ᶠ j in atTop, ∀ k ∈ Finset.range (K + 1),
        absoluteRowTail (M k) j < ε := by
      exact (eventually_all_finset _).mpr (fun k _ =>
        (absoluteRowTail_tendsto_zero (hM.1 k)).eventually (gt_mem_nhds hε))
    obtain ⟨j, hj, hnj⟩ := (he.and (eventually_ge_atTop n)).exists
    obtain ⟨k, hk⟩ := hlarge j
    refine ⟨k, ?_, hk.trans_le (absoluteRowTail_antitone (hM.1 k) hnj)⟩
    by_contra hnot
    exact (not_lt_of_ge (hj k (Finset.mem_range.mpr (by omega))).le) hk
  obtain ⟨r, hr, hmass⟩ := extraction_forall_of_frequently hfreq
  exact ⟨ε, hε, r, hr, hmass⟩

theorem absoluteRowTail_le_sub_mass_add {f g : ℕ → 𝕜}
    (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖)) (j : ℕ) :
    absoluteRowTail f j ≤ (∑' i, ‖f i - g i‖) + absoluteRowTail g j := by
  have hd : Summable (fun i => ‖f i - g i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_sub_le _ _)
      (hf.add hg)
  simp only [absoluteRowTail]
  rw [← hd.tsum_add (summable_absoluteRowTail hg j)]
  apply (summable_absoluteRowTail hf j).tsum_le_tsum _
    (hd.add (summable_absoluteRowTail hg j))
  intro i
  split_ifs
  · simpa only [sub_add_cancel] using norm_add_le (f i - g i) (g i)
  · simp

/-- The coordinate compactness input for the noncompact branch of Lemma 5.2.
The selected rows are nonzero, which also retains membership in a row restriction. -/
theorem noncompactMatrix_exists_separated_row_limit (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (hnc : ¬ IsCompactMatrix 𝕜 M) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ b : ℕ → 𝕜,
      Summable (fun i => ‖b i‖) ∧
      (∀ i, Tendsto (fun n => M (k n) i) atTop (𝓝 (b i))) ∧
      ∃ δ : ℝ, 0 < δ ∧ (∀ n, δ ≤ ∑' i, ‖M (k n) i - b i‖) ∧
        (∀ n, ∃ i, M (k n) i ≠ 0) := by
  obtain ⟨ε, hε, r, hr, hmass⟩ := noncompactMatrix_exists_increasing_large_tails M hM hnc
  have hbound (n : ℕ) (t : Finset ℕ) : ∑ i ∈ t, ‖M (r n) i‖ ≤ matrixNorm 𝕜 M := by
    exact ((hM.1 (r n)).sum_le_tsum t (fun i _ => norm_nonneg _)).trans
      (rowSum_le_matrixNorm M hM (r n))
  obtain ⟨b, hb, s, hs, hcol⟩ := JLMS.exists_summable_matrix_column_limit
    (fun n i => M (r n) i) (matrixNorm_nonneg M hM) hbound
  obtain ⟨J, hJ⟩ := ((absoluteRowTail_tendsto_zero hb).eventually
    (gt_mem_nhds (show 0 < ε / 2 by positivity))).exists
  let a : ℕ → ℕ := fun n => n + J
  have ha : StrictMono a := fun _ _ h => Nat.add_lt_add_right h J
  let k := r ∘ s ∘ a
  have hk : StrictMono k := hr.comp (hs.comp ha)
  have hm (n : ℕ) : ε < absoluteRowTail (M (k n)) J := by
    exact (hmass (s (a n))).trans_le (absoluteRowTail_antitone (hM.1 (k n))
      ((Nat.le_add_left J n).trans (hs.id_le (a n))))
  refine ⟨k, hk, b, hb, fun i => (hcol i).comp ha.tendsto_atTop,
    ε / 2, by positivity, ?_, ?_⟩
  · intro n
    have hle := absoluteRowTail_le_sub_mass_add (hM.1 (k n)) hb J
    have hlt := hm n
    linarith
  · intro n
    by_contra hz
    push_neg at hz
    have ht := hm n
    simp only [absoluteRowTail, hz, norm_zero, ite_self, tsum_zero] at ht
    linarith

end Posets
