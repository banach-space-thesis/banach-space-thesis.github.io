import ThesisCommon.Analysis.LpHaarStepDensity
import Mathlib.Tactic.Module

/-! The actual constant and dyadic Haar vectors have dense linear span in Lp. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace ThesisCommon

theorem lpHaarCellVector_split (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) :
    lpHaarCellVector 𝕜 p n k = lpHaarCellVector 𝕜 p (n + 1) (2 * k) +
      lpHaarCellVector 𝕜 p (n + 1) (2 * k + 1) := by
  unfold lpHaarCellVector
  have h := indicatorConstLp_disjoint_union (p := p.val)
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (show MeasurableSet (lpHaarCell (n + 1) (2 * k)) from measurableSet_Ioc)
    (show MeasurableSet (lpHaarCell (n + 1) (2 * k + 1)) from measurableSet_Ioc)
    (measure_ne_top _ _) (measure_ne_top _ _)
    (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)) (1 : 𝕜)
  simpa only [lpHaarCell_children] using h

theorem lpHaarCellVector_left (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) :
    lpHaarCellVector 𝕜 p (n + 1) (2 * k) =
      (1 / 2 : 𝕜) • (lpHaarCellVector 𝕜 p n k + lpHaarDyadic 𝕜 p n k) := by
  rw [lpHaarCellVector_split 𝕜 p n k]
  change _ = (1 / 2 : 𝕜) • (_ + (lpHaarCellVector 𝕜 p (n + 1) (2 * k) -
    lpHaarCellVector 𝕜 p (n + 1) (2 * k + 1)))
  module

theorem lpHaarCellVector_right (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) :
    lpHaarCellVector 𝕜 p (n + 1) (2 * k + 1) =
      (1 / 2 : 𝕜) • (lpHaarCellVector 𝕜 p n k - lpHaarDyadic 𝕜 p n k) := by
  rw [lpHaarCellVector_split 𝕜 p n k]
  change _ = (1 / 2 : 𝕜) • (_ - (lpHaarCellVector 𝕜 p (n + 1) (2 * k) -
    lpHaarCellVector 𝕜 p (n + 1) (2 * k + 1)))
  module

theorem lpHaarCellVector_root_eq_const (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    lpHaarCellVector 𝕜 p 0 0 = Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜) := by
  apply Lp.ext
  have hmem : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioc (0 : ℝ) 1 := by
    simpa only [lpHaarLevelCells_union] using lpHaarLevelCells_cover 0
  filter_upwards [indicatorConstLp_coeFn (p := p.val)
    (hs := show MeasurableSet (lpHaarCell 0 0) from measurableSet_Ioc)
    (hμs := measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (c := (1 : 𝕜)),
    Lp.coeFn_const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜), hmem] with x h₁ h₂ hx
  change (indicatorConstLp p.val _ _ (1 : 𝕜)) x = _
  rw [h₁, h₂]
  simpa [lpHaarCell, intervalLpDyadicRadius, hx]

def lpHaarSystemSet (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) : Set (IntervalLp 𝕜 p) :=
  insert (lpHaarCellVector 𝕜 p 0 0)
    (Set.range (fun nk : Σ n : ℕ, Fin (2 ^ n) => lpHaarDyadic 𝕜 p nk.1 nk.2))

theorem lpHaarCellVector_mem_haarSpan (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k : ℕ) (hk : k < 2 ^ n) :
    lpHaarCellVector 𝕜 p n k ∈ Submodule.span 𝕜 (lpHaarSystemSet 𝕜 p) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by simpa using hk
      subst k
      exact Submodule.subset_span (Set.mem_insert _ _)
  | succ n ih =>
      have hparent : k / 2 < 2 ^ n := by rw [pow_succ] at hk; omega
      have h₁ := ih (k / 2) hparent
      have h₂ : lpHaarDyadic 𝕜 p n (k / 2) ∈ Submodule.span 𝕜 (lpHaarSystemSet 𝕜 p) :=
        Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨n, ⟨k / 2, hparent⟩⟩, rfl⟩)
      by_cases heven : k % 2 = 0
      · have heq : 2 * (k / 2) = k := by omega
        rw [← heq, lpHaarCellVector_left]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ h₁ h₂)
      · have heq : 2 * (k / 2) + 1 = k := by omega
        rw [← heq, lpHaarCellVector_right]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h₁ h₂)

theorem lpHaarSystem_dense_span (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) : Dense (Submodule.span 𝕜 (lpHaarSystemSet 𝕜 p) : Set (IntervalLp 𝕜 p)) := by
  apply Dense.mono _ (lpHaarCellVector_dense_span 𝕜 p hp)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨n, k⟩, rfl⟩
  exact lpHaarCellVector_mem_haarSpan 𝕜 p n k k.isLt

end ThesisCommon
