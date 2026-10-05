import ThesisCommon.Analysis.ContinuousMapCutoff

/-! A common continuous cutoff for a set of diameter at most one quarter of a radius. -/
noncomputable section
namespace ThesisCommon

def intervalLocalCutoff (t : UnitInterval) (r : ℝ) : C(UnitInterval, ℝ) :=
  ⟨fun x => max 0 (min 1 (2 - (4 / r) * dist t x)), by fun_prop⟩

theorem intervalLocalCutoff_bounds (t : UnitInterval) (r : ℝ) (x : UnitInterval) :
    0 ≤ intervalLocalCutoff t r x ∧ intervalLocalCutoff t r x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem intervalLocalCutoff_eq_one (t : UnitInterval) {r : ℝ} (hr : 0 < r)
    (x : UnitInterval) (hx : dist t x ≤ r / 4) : intervalLocalCutoff t r x = 1 := by
  have h : (4 / r) * dist t x ≤ 1 := by
    calc
      (4 / r) * dist t x = (4 * dist t x) / r := by ring
      _ ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
  change max 0 (min 1 (2 - (4 / r) * dist t x)) = 1
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem intervalLocalCutoff_eq_zero (t : UnitInterval) {r : ℝ} (hr : 0 < r)
    (x : UnitInterval) (hx : r / 2 ≤ dist t x) : intervalLocalCutoff t r x = 0 := by
  have h : 2 ≤ (4 / r) * dist t x := by
    calc
      2 ≤ (4 * dist t x) / r := (le_div_iff₀ hr).mpr (by linarith)
      _ = (4 / r) * dist t x := by ring
  change max 0 (min 1 (2 - (4 / r) * dist t x)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem intervalLocalCutoff_vanishes_outside_nearby_ball (t s : UnitInterval)
    {r : ℝ} (hr : 0 < r) (hts : dist t s ≤ r / 4) (x : UnitInterval)
    (hx : x ∉ Metric.ball s r) : intervalLocalCutoff t r x = 0 := by
  apply intervalLocalCutoff_eq_zero t hr x
  have hxs : r ≤ dist x s := le_of_not_gt hx
  have htri := dist_triangle x t s
  rw [dist_comm x t] at htri
  linarith

theorem exists_interval_cantor_local_cutoff (f : (ℕ → Bool) → UnitInterval)
    {r : ℝ} (hr : 0 < r) (hdiam : ∀ x y, dist (f x) (f y) ≤ r / 4) :
    ∃ φ : C(UnitInterval, ℝ), (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧
      (∀ x, φ (f x) = 1) ∧ ∀ x t, t ∉ Metric.ball (f x) r → φ t = 0 := by
  let z : ℕ → Bool := fun _ => false
  refine ⟨intervalLocalCutoff (f z) r, intervalLocalCutoff_bounds _ _, ?_, ?_⟩
  · exact fun x => intervalLocalCutoff_eq_one _ hr _ (hdiam z x)
  · exact fun x t ht => intervalLocalCutoff_vanishes_outside_nearby_ball _ _ hr (hdiam z x) t ht

end ThesisCommon
