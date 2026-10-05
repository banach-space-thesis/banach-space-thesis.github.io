import JLMS.DisjointWeakNull
import JLMS.MatrixCompactness
import JLMS.MatrixSelection
import JLMS.MatrixLowerBound
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Rosenthal's c₀ restriction theorem in the required quantitative form

Choose norming functionals for the coordinate images. Their restrictions to
c₀ have uniformly bounded ℓ¹ mass. Coordinate compactness and a finite-history
gliding-hump selection produce a matrix with summably small off-diagonal
entries. The matrix lower-bound lemma gives the desired bounded-below
restriction. This follows the restriction step cited by Arnott–Laustsen.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Coordinate images uniformly above γ give a restriction bounded below
by any positive δ<γ. The inclusion of the selected coordinates is contractive. -/
theorem exists_cZero_restriction_bounded_below (R : cZero 𝕜 →L[𝕜] X)
    {δ γ : ℝ} (hδ : 0 < δ) (hδγ : δ < γ)
    (hlarge : ∀ n, γ < ‖R (cZeroUnit 𝕜 n)‖) :
    ∃ s : ℕ → ℕ, ∃ hs : StrictMono s,
      ∀ a : cZero 𝕜, δ * ‖a‖ ≤ ‖R (cZeroSubsequenceInsertion s hs a)‖ := by
  choose φ hφ he using fun n => exists_dual_vector'' 𝕜 (R (cZeroUnit 𝕜 n))
  let A (n j : ℕ) := φ n (R (cZeroUnit 𝕜 j))
  have hmass (n : ℕ) (t : Finset ℕ) : ∑ j ∈ t, ‖A n j‖ ≤ ‖R‖ := by
    have h := cZero_dual_finite_coordinate_mass ((φ n).comp R) t
    exact h.trans (((φ n).opNorm_comp_le R).trans (by
      simpa using mul_le_mul_of_nonneg_right (hφ n) (norm_nonneg R)))
  obtain ⟨b, hbs, r, hr, hcol⟩ :=
    exists_summable_matrix_column_limit A (norm_nonneg R) hmass
  have hb : Tendsto b atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := hbs.tendsto_cofinite_zero
    rwa [Nat.cofinite_eq_atTop] at h
  let B (i j : ℕ) := A (r i) (r j)
  have hBrow (i : ℕ) : Tendsto (B i) atTop (𝓝 0) :=
    (weakNull_cZero_units ((φ (r i)).comp R)).comp hr.tendsto_atTop
  have hBcol (j : ℕ) : Tendsto (fun i => B i j) atTop (𝓝 (b (r j))) := hcol (r j)
  let ε := γ - δ
  have hε : 0 < ε := sub_pos.mpr hδγ
  let w (j : ℕ) : ℝ := ε / 4 * (1 / 2 : ℝ) ^ j
  have hw (j : ℕ) : 0 < w j := mul_pos (div_pos hε (by norm_num))
    (pow_pos (by norm_num) j)
  obtain ⟨q, hq, hoff⟩ := exists_small_offDiagonal_subsequence B (fun j => b (r j))
    hBrow hBcol (hb.comp hr.tendsto_atTop) w hw
  let s := r ∘ q
  have hs : StrictMono s := hr.comp hq
  have hgeom : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hws : Summable (fun j => 2 * w j) := (hgeom.mul_left (ε / 4)).mul_left 2
  have hbudget : ∑' j, 2 * w j ≤ ε := by
    change (∑' j, 2 * (ε / 4 * (1 / 2 : ℝ) ^ j)) ≤ ε
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
    ring_nf
    exact le_rfl
  refine ⟨s, hs, ?_⟩
  intro a
  have hd (i : ℕ) : γ ≤ ‖φ (s i) (R (cZeroUnit 𝕜 (s i)))‖ := by
    rw [he, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact (hlarge (s i)).le
  have ho (i j : ℕ) (hij : i ≠ j) :
      ‖φ (s i) (R (cZeroUnit 𝕜 (s j)))‖ ≤ 2 * w j := hoff i j hij
  have h := cZero_matrix_lower_bound R s hs (fun i => φ (s i)) (fun i => hφ (s i))
    (hδ.trans hδγ) hε.le (fun j => 2 * w j) (fun j => by positivity)
    hws hbudget hd ho a
  simpa only [ε, sub_sub_cancel] using h

end JLMS
