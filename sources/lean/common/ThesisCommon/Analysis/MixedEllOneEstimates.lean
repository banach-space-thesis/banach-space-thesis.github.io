import ThesisCommon.Analysis.FiniteColumnInterference
import ThesisCommon.Analysis.SchauderSumMatrix
import ThesisCommon.Analysis.SchauderSumWeaklyNull
import ThesisCommon.Analysis.SchauderSymmetry
import ThesisCommon.Analysis.LpSchauderBasis

/-! Interference and norm estimates for the actual mixed sum X(ell_1).
Only the outer-row finiteness statement needs symmetry and non-ell_1.
The other estimates hold for every normalized one-unconditional outer basis.
-/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

/-- Actual scalar matrix entry, with target row/column followed by source row/column. -/
def ellOneEntry (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) (r s i j : ℕ) : 𝕜 :=
  T (single i (lp.single 1 j (1 : 𝕜))) r s

theorem ellOneEntry_eq_productCoordinate
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) (r s i j : ℕ) :
    ellOneEntry T r s i j =
      productCoordinate (scalarLpSchauderBasis 1 (by simp)) (r, s)
        (T (productVector (scalarLpSchauderBasis 1 (by simp)) (i, j))) := rfl

/-- Finitely many entire source rows can affect a fixed target coordinate. -/
theorem ellOne_finite_interfering_rows (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) (i j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {r | ∃ s, ε ≤ ‖ellOneEntry T i j r s‖}.Finite := by
  let c := scalarLpSchauderBasis (𝕜 := 𝕜) 1 (by simp)
  obtain ⟨N, hN⟩ := product_uniform_row_bound c
    (b.weakly_null_of_not_equivalentEllOne hs hnot)
    ((productCoordinate c (i, j)).comp T) hε
  apply (Finset.finite_toSet (Finset.range N)).subset
  rintro r ⟨s, hrs⟩
  apply Finset.mem_range.mpr
  by_contra hr
  exact (not_le_of_gt (hN r (by omega) s)) hrs

/-- Only finitely many product coordinates of a fixed vector are large. -/
theorem product_finite_large_coordinates {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (c : NormalizedSchauderBasis 𝕜 Y) (hc : c.IsOneUnconditional)
    (y : SchauderSum b hb Y) {ε : ℝ} (hε : 0 < ε) :
    {t : ℕ × ℕ | ε ≤ ‖productCoordinate c t y‖}.Finite := by
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    ((productBasis c hc e).coord_tendsto_zero y) ε hε
  apply ((Finset.finite_toSet (Finset.range N)).image e).subset
  intro t ht
  refine ⟨e.symm t, Finset.mem_range.mpr ?_, e.apply_symm_apply t⟩
  by_contra hn
  have hh := hN (e.symm t) (by omega)
  change dist (productCoordinate c (e (e.symm t)) y) 0 < ε at hh
  rw [e.apply_symm_apply, dist_zero_right] at hh
  exact (not_le_of_gt hh) ht

/-- Finite target interference from a fixed source coordinate. -/
theorem ellOne_finite_interfering_targets
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) (i j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {t : ℕ × ℕ | ε ≤ ‖ellOneEntry T t.1 t.2 i j‖}.Finite :=
  product_finite_large_coordinates (scalarLpSchauderBasis 1 (by simp))
    (scalarLpSchauderBasis_oneUnconditional 1 (by simp)) _ hε

/-- The finite-family pigeonhole step, with individual positive thresholds. -/
theorem ellOne_simultaneous_small_rows
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) (r : ℕ)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (K : Finset ℕ) (M : ℕ → Set ℕ)
    {A : Set ℕ} (hA : A.Infinite) (hM : ∀ i ∈ K, (M i).Infinite) :
    {s ∈ A | ∀ i ∈ K, {m ∈ M i | ‖ellOneEntry T r s i m‖ < ε i}.Infinite}.Infinite := by
  apply bounded_columns_simultaneous_small_rows
    (fun i s m => ‖ellOneEntry T r s i m‖) (fun i => ‖block T r i‖) ε
    (fun i m F => ellOne_column_sum_le (block T r i) m F) hε K M hA hM

/-- Absolute column sums are uniformly bounded, so the real supremum is genuine. -/
theorem ellOne_column_sums_bddAbove
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) (r i : ℕ) :
    BddAbove (Set.range (fun j => ∑' s, ‖ellOneEntry T r s i j‖)) := by
  refine ⟨‖block T r i‖, ?_⟩
  rintro _ ⟨j, rfl⟩
  change (∑' s, ‖(block T r i) (lp.single 1 j (1 : 𝕜)) s‖) ≤ _
  rw [← ellOne_norm_eq_tsum]
  simpa only [lp.norm_single (by simp : (0 : ℝ≥0∞) < 1), norm_one, mul_one]
    using (block T r i).le_opNorm (lp.single 1 j (1 : 𝕜))

/-- The manuscript's exact supremum-of-column-sums estimate. No positivity
assumption on epsilon is added: the hypothesis itself implies it. -/
theorem norm_le_of_ellOne_column_sums
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) {ε : ℝ}
    (hT : ∀ r i, (⨆ j : ℕ, ∑' s, ‖ellOneEntry T r s i j‖) ≤
      ε / (2 : ℝ) ^ (r + i + 2)) : ‖T‖ ≤ ε := by
  have hcol (r i j : ℕ) : (∑' s, ‖ellOneEntry T r s i j‖) ≤
      ε / (2 : ℝ) ^ (r + i + 2) :=
    (le_ciSup (ellOne_column_sums_bddAbove T r i) j).trans (hT r i)
  have hε : 0 ≤ ε := by
    have hh := (tsum_nonneg (fun s => norm_nonneg (ellOneEntry T 0 s 0 0))).trans
      (hcol 0 0 0)
    norm_num at hh
    linarith
  apply norm_le_of_geometric_blocks T hε
  intro r i
  apply ellOne_norm_le_of_columns (block T r i) (by positivity)
  intro j
  rw [ellOne_norm_eq_tsum]
  exact hcol r i j

end SchauderSum
end ThesisCommon
