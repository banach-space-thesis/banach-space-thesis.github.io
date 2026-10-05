import ThesisCommon.Analysis.SchauderOperators

/-! Coordinate solidity of a one-unconditional Schauder norm. These lemmas
construct vectors with prescribed dominated coefficients; they are the
analytic input for the paper's genuine vector-valued basis sums.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : NormalizedSchauderBasis 𝕜 X)

/-- Coefficientwise norm domination implies norm domination in the space. -/
theorem norm_le_of_coord_le (hb : b.IsOneUnconditional) {x y : X}
    (h : ∀ n, ‖b.coord n x‖ ≤ ‖b.coord n y‖) : ‖x‖ ≤ ‖y‖ := by
  apply le_of_tendsto_of_tendsto' (b.expansion x).norm (b.expansion y).norm
  intro N
  simpa only [one_mul] using hb.2 (Finset.range N)
    (fun n => b.coord n x) (fun n => b.coord n y) (fun n _ => h n)

/-- Diagonal action on the basis determines diagonal action on all coordinates. -/
theorem coord_diagonal (D : X →L[𝕜] X) (d : ℕ → 𝕜)
    (hD : ∀ n, D (b.vector n) = d n • b.vector n) (i : ℕ) (x : X) :
    b.coord i (D x) = d i * b.coord i x := by
  have heq : (b.coord i).comp D = d i • b.coord i := by
    apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hD, map_smul,
      ContinuousLinearMap.smul_apply, b.biorthogonal, smul_eq_mul]
    by_cases hn : i = n
    · subst n; rfl
    · simp [hn]
  exact DFunLike.congr_fun heq x

/-- Any sequence dominated by the coordinates of a vector is itself the
coordinate sequence of a vector, with no increase in norm. -/
theorem exists_of_coord_domination [CompleteSpace X] (hb : b.IsOneUnconditional)
    (x : X) (a : ℕ → 𝕜) (ha : ∀ n, ‖a n‖ ≤ ‖b.coord n x‖) :
    ∃ y : X, (∀ n, b.coord n y = a n) ∧ ‖y‖ ≤ ‖x‖ := by
  let d : ℕ → 𝕜 := fun n => a n / b.coord n x
  have hd (n : ℕ) : ‖d n‖ ≤ 1 := by
    dsimp [d]
    by_cases hn : b.coord n x = 0
    · simp [hn]
    · rw [norm_div, div_le_one (norm_pos_iff.mpr hn)]
      exact ha n
  obtain ⟨D, hD, hDe⟩ := b.exists_diagonal hb d zero_le_one hd
  refine ⟨D x, ?_, ?_⟩
  · intro n
    rw [b.coord_diagonal D d hDe]
    dsimp [d]
    by_cases hn : b.coord n x = 0
    · have han : a n = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hn] using ha n)
        (norm_nonneg _))
      simp [hn, han]
    · exact div_mul_cancel₀ _ hn
  · exact (D.le_opNorm x).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (norm_nonneg x))

/-- Finite coordinate suppression is contractive, derived from unconditionality. -/
theorem finite_projection_norm_le (hb : b.IsOneUnconditional) (F : Finset ℕ) (x : X) :
    ‖∑ n ∈ F, b.coord n x • b.vector n‖ ≤ ‖x‖ := by
  classical
  apply b.norm_le_of_coord_le hb
  intro n
  rw [b.coord_finite_sum]
  by_cases hn : n ∈ F
  · simp [hn]
  · simp [hn]

end NormalizedSchauderBasis
end ThesisCommon
