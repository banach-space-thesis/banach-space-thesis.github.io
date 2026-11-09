import PL1.SchurLattice
import BanLat.Dual

/-!
# Strictly positive functionals on separable normed lattices

The positive functional constructed here detects every nonzero positive
vector. It is obtained from positive Hahn--Banach functionals on a dense
sequence in the positive cone, using a norm-convergent geometric series.
-/

noncomputable section
open Filter TopologicalSpace
open scoped Topology

namespace PL1.SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- Positivity is strict on all nonzero positive vectors. -/
def IsStrictlyPositive (φ : E →L[ℝ] ℝ) : Prop :=
  ∀ x : E, 0 < x → 0 < φ x

theorem IsStrictlyPositive.nonneg {φ : E →L[ℝ] ℝ} (hφ : IsStrictlyPositive φ) :
    0 ≤ φ := by
  apply StrongDual.nonneg_iff.mpr
  intro x hx
  by_cases h : x = 0
  · simp [h]
  · exact (hφ x (lt_of_le_of_ne hx (Ne.symm h))).le

theorem IsStrictlyPositive.eq_zero_of_nonneg {φ : E →L[ℝ] ℝ}
    (hφ : IsStrictlyPositive φ) {x : E} (hx : 0 ≤ x) (hz : φ x = 0) : x = 0 := by
  by_contra h
  have hp := hφ x (lt_of_le_of_ne hx (Ne.symm h))
  exact (ne_of_gt hp) hz

/-- Separability supplies a strictly positive continuous functional. The
result does not require completeness or a separable continuous dual. -/
theorem exists_strictlyPositive [SeparableSpace E] :
    ∃ φ : E →L[ℝ] ℝ, 0 ≤ φ ∧ IsStrictlyPositive φ := by
  classical
  let C := Set.Ici (0 : E)
  let : Nonempty C := ⟨⟨0, le_rfl⟩⟩
  let d : ℕ → C := denseSeq C
  choose g hg hgn hgd using fun n =>
    StrongDual.exists_positive_dual_norming (d n).property
  let w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hw : Summable w := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable (fun n => w n • g n) := by
    apply hw.of_norm_bounded
    intro n
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ w n)]
    exact mul_le_of_le_one_right (by positivity : 0 ≤ w n) (hgn n)
  let φ : E →L[ℝ] ℝ := ∑' n, w n • g n
  have hφ (x : E) : φ x = ∑' n, w n * g n x := by
    simpa [φ] using (ContinuousLinearMap.apply ℝ ℝ x).map_tsum hsum
  have hscalar (x : E) : Summable (fun n => w n * g n x) := by
    simpa using hsum.mapL (ContinuousLinearMap.apply ℝ ℝ x)
  have hpos : 0 ≤ φ := by
    apply StrongDual.nonneg_iff.mpr
    intro x hx
    rw [hφ]
    exact tsum_nonneg (fun n => mul_nonneg (by positivity)
      (StrongDual.apply_nonneg_of_nonneg (hg n) hx))
  refine ⟨φ, hpos, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn⟩ := (denseRange_denseSeq C).exists_dist_lt (⟨x, hx.le⟩ : C)
    (show 0 < ‖x‖ / 3 from by positivity)
  have hdist : ‖x - (d n : E)‖ < ‖x‖ / 3 := by
    simpa [d, Subtype.dist_eq, dist_eq_norm] using hn
  have hdual : |g n x - ‖(d n : E)‖| ≤ ‖x - (d n : E)‖ := by
    have hb := (g n).le_opNorm (x - (d n : E))
    rw [map_sub, hgd] at hb
    exact hb.trans (mul_le_of_le_one_left (norm_nonneg _) (hgn n))
  have htriangle : ‖x‖ ≤ ‖x - (d n : E)‖ + ‖(d n : E)‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - (d n : E)) (d n : E)
  have hgnx : 0 < g n x := by
    have hb := (abs_le.mp hdual).1
    linarith
  rw [hφ]
  exact (hscalar x).tsum_pos (fun k => mul_nonneg (by positivity)
    (StrongDual.apply_nonneg_of_nonneg (hg k) hx.le)) n
    (mul_pos (by positivity) hgnx)

end PL1.SchurLattice
