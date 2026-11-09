import BanachIsometric.StarBody
import Mathlib.Analysis.Convex.PathConnected

/-! # Connected strict sublevels of a positive homogeneous gauge -/

namespace BanachIsometric

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem IsDefinitePositiveHomogeneous.starConvex_strict_sublevel {g : V → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (r : ℝ) :
    StarConvex ℝ (0 : V) {x | g x < r} := by
  intro x hx a b ha hb hab
  simp only [smul_zero, zero_add, mem_setOf_eq]
  rw [hg.smul_nonneg b hb x]
  have hble : b ≤ 1 := by linarith
  exact (mul_le_of_le_one_left (hg.nonneg x) hble).trans_lt hx

theorem IsDefinitePositiveHomogeneous.isPreconnected_strict_sublevel {g : V → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) {r : ℝ} (hr : 0 < r) :
    IsPreconnected {x | g x < r} := by
  have hzero : (0 : V) ∈ {x | g x < r} := by
    simpa only [mem_setOf_eq, (hg.eq_zero_iff 0).mpr rfl] using hr
  exact ((hg.starConvex_strict_sublevel r).isPathConnected hzero).isConnected.isPreconnected

end BanachIsometric
