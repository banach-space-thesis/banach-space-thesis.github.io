import SurveyStatements.P5L1VariationTerminalGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-! Exact action of the actual terminal dyadic permutations on every
coarser cell indicator. No measure-theoretic symmetry is postulated. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem terminalFiber_vector_sum (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n ≤ M) (k : Fin (2 ^ n)) :
    lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k =
      ∑ a ∈ terminalFiber M n hn k, lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ M a := by
  apply Lp.ext
  have hcoarse : (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k : ℝ → 𝕜) =ᵐ[
      volume.restrict (Icc (0 : ℝ) 1)] (lpHaarCell n k).indicator (fun _ => (1 : 𝕜)) :=
    indicatorConstLp_coeFn (p := (1 : ℝ≥0∞))
      (hs := (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc))
      (hμs := measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (c := (1 : 𝕜))
  have hterms : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ a : Fin (2 ^ M), lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ M a x =
        (lpHaarCell M a).indicator (fun _ => (1 : 𝕜)) x := by
    apply ae_all_iff.mpr
    intro a
    exact indicatorConstLp_coeFn (p := (1 : ℝ≥0∞))
      (hs := (show MeasurableSet (lpHaarCell M a) from measurableSet_Ioc))
      (hμs := measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (c := (1 : 𝕜))
  filter_upwards [hcoarse, hterms,
    lpHaar_coeFn_finset_sum (terminalFiber M n hn k)
      (fun a => lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ M a)] with x hc ht hs
  rw [hc, hs]
  simp_rw [ht]
  rw [← Finset.indicator_biUnion_apply (terminalFiber M n hn k)
    (fun a => lpHaarCell M a) (fun a _ b _ hab => lpHaarLevelCells_disjoint M hab),
    terminalFiber_cells]

theorem terminalPermutation_cell (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n ≤ M) (σ : DyadicTreePerm M) (k : Fin (2 ^ n)) :
    terminalPermutation 𝕜 M σ.val (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k) =
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n hn k) := by
  rw [terminalFiber_vector_sum 𝕜 M n hn k, map_sum]
  have hi (a : Fin (2 ^ M)) :
      terminalPermutation 𝕜 M σ.val (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ M a) =
        lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ M (σ.val a) :=
    terminalPermutation_indicator 𝕜 M σ.val a 1
  simp_rw [hi]
  rw [terminalFiber_vector_sum 𝕜 M n hn (nodeAction σ n hn k)]
  apply Finset.sum_bijective σ.val σ.val.bijective
  · intro a
    simp only [terminalFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [nodeAction_prefix]
    exact (nodeAction_injective σ n hn).eq_iff.symm
  · intro a ha
    rfl

end SurveyStatements.P5L1Variation

