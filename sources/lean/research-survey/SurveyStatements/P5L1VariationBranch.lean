import SurveyStatements.P5L1VariationCells

/-! Nested concrete dyadic cells and their disjoint rings. The root may be
any dyadic cell: all normalization and measure estimates retain its scale. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

structure DyadicBranch (rootLevel : ℕ) where
  index : (j : ℕ) → Fin (2 ^ (rootLevel + j))
  parent : ∀ j, lpHaarParentIndex (rootLevel + j) (index (j + 1)) = index j

namespace DyadicBranch
variable {r : ℕ} (B : DyadicBranch r)

def cell (j : ℕ) : Set ℝ := lpHaarCell (r + j) (B.index j)

def annulus (j : ℕ) : Set ℝ := B.cell j \ B.cell (j + 1)

theorem cell_measurable (j : ℕ) : MeasurableSet (B.cell j) := measurableSet_Ioc

theorem cell_next_subset (j : ℕ) : B.cell (j + 1) ⊆ B.cell j := by
  have hval : (B.index (j + 1)).val / 2 = (B.index j).val :=
    congrArg Fin.val (B.parent j)
  have hchild : (B.index (j + 1)).val = 2 * (B.index j).val ∨
      (B.index (j + 1)).val = 2 * (B.index j).val + 1 := by omega
  intro x hx
  change x ∈ lpHaarCell (r + j) (B.index j)
  rw [← lpHaarCell_children]
  rcases hchild with h | h
  · apply Or.inl
    change x ∈ lpHaarCell ((r + j) + 1) (2 * (B.index j).val)
    simpa only [cell, h] using hx
  · apply Or.inr
    change x ∈ lpHaarCell ((r + j) + 1) (2 * (B.index j).val + 1)
    simpa only [cell, h] using hx

theorem cell_antitone : Antitone B.cell :=
  antitone_nat_of_succ_le B.cell_next_subset

theorem annulus_measurable (j : ℕ) : MeasurableSet (B.annulus j) :=
  (B.cell_measurable j).diff (B.cell_measurable (j + 1))

theorem annulus_disjoint : Pairwise (fun i j => Disjoint (B.annulus i) (B.annulus j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 (B.cell_antitone (Nat.succ_le_of_lt h) hy.1)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 (B.cell_antitone (Nat.succ_le_of_lt h) hx.1)

theorem cell_real_measure (j : ℕ) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (B.cell j) =
      intervalLpDyadicRadius (r + j) := by
  rw [measureReal_def, cell, lpHaarCell_measure (r + j) _ (B.index j).isLt,
    ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos (r + j)).le]

theorem annulus_real_measure (j : ℕ) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (B.annulus j) =
      intervalLpDyadicRadius (r + j) / 2 := by
  rw [annulus, measureReal_diff (B.cell_next_subset j) (B.cell_measurable (j + 1)),
    B.cell_real_measure, B.cell_real_measure, show r + (j + 1) = (r + j) + 1 by omega,
    lpHaarRadius_succ]
  ring

theorem density_on_annulus (𝕜 : Type*) [RCLike 𝕜] (i j : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ B.annulus j →
      cellDensity 𝕜 (r + i) (B.index i) x =
        if i ≤ j then (2 : 𝕜) ^ (r + i) else 0 := by
  filter_upwards [cellDensity_coe 𝕜 (r + i) (B.index i)] with x hx hmem
  rw [hx]
  by_cases hi : i ≤ j
  · have hin : x ∈ lpHaarCell (r + i) (B.index i) := B.cell_antitone hi hmem.1
    simp [hi, hin]
  · have hout : x ∉ lpHaarCell (r + i) (B.index i) := by
      intro hin
      exact hmem.2 (B.cell_antitone (by omega : j + 1 ≤ i) hin)
    simp [hi, hout]

theorem sum_annulus_integral_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (N : ℕ) (f : IntervalL1 𝕜) :
    (∑ j ∈ Finset.range N, ∫ x in B.annulus j, ‖f x‖
      ∂(volume.restrict (Icc (0 : ℝ) 1))) ≤ ‖f‖ := by
  have hf : Integrable (fun x => ‖f x‖) (volume.restrict (Icc (0 : ℝ) 1)) :=
    ((Lp.memLp f).integrable (by norm_num)).norm
  rw [← integral_biUnion_finset (Finset.range N)
    (fun j _ => B.annulus_measurable j)
    (fun i _ j _ hij => B.annulus_disjoint hij)
    (fun _ _ => hf.integrableOn), L1.norm_eq_integral_norm]
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall (fun x => norm_nonneg (f x))) hf

end DyadicBranch
end SurveyStatements.P5L1Variation
