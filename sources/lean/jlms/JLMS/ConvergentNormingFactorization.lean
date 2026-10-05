import JLMS.ConvergentNormingMatrix
import JLMS.PairedDiagonal
import JLMS.ApproximateDiagonalFactorization
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact quantitative factorization from convergent norming functionals

Select a nearly diagonal subsequence, pair its rows and columns, and invert
the small error. The positive margin between δ and γ supplies a geometric
error budget. The resulting identity factorization has norm product <1/δ.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem factorization_of_convergent_norming (R : cZero 𝕜 →L[𝕜] X)
    {δ γ : ℝ} (hδ : 0 < δ) (hδγ : δ < γ)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hdiag : ∀ n, γ ≤ RCLike.re (φ n (R (cZeroUnit 𝕜 n))))
    (halign : ∀ n, φ n (R (cZeroUnit 𝕜 n)) =
      (RCLike.re (φ n (R (cZeroUnit 𝕜 n))) : 𝕜))
    (ψ : X →L[𝕜] 𝕜) (r : ℕ → ℕ) (hr : StrictMono r)
    (ht : ∀ x, Tendsto (fun n => φ (r n) x) atTop (𝓝 (ψ x))) :
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] cZero 𝕜,
      (U.comp R).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧ ‖U‖ * ‖V‖ < 1 / δ := by
  let ε := (γ - δ) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hδγ) (by norm_num)
  have hγ : 0 < γ := hδ.trans hδγ
  have hεγ : ε < γ := by dsimp [ε]; linarith
  let w (j : ℕ) : ℝ := ε / 4 * (1 / 2 : ℝ) ^ j
  let v (j : ℕ) : ℝ := ε / 8 * (1 / 2 : ℝ) ^ (j / 2)
  have hw (j : ℕ) : 0 < w j := mul_pos (div_pos hε (by norm_num)) (pow_pos (by norm_num) j)
  have hv (j : ℕ) : 0 < v j := mul_pos (div_pos hε (by norm_num)) (pow_pos (by norm_num) _)
  obtain ⟨s, hs, hoff, hst⟩ := exists_small_convergent_norming_matrix R φ ψ r hr ht v hv
  have hgeom : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hws : Summable w := hgeom.mul_left (ε / 4)
  have hbudget : (∑' j, 2 * w j) = ε := by
    change (∑' j, 2 * (ε / 4 * (1 / 2 : ℝ) ^ j)) = ε
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
    ring
  let d := pairedRealDiagonal R φ s
  have hd (n : ℕ) : γ ≤ d n := pairedRealDiagonal_lower R φ s hdiag n
  have hdb (n : ℕ) : ‖(d n : 𝕜)‖ ≤ ‖R‖ := by
    rw [RCLike.norm_ofReal, abs_of_pos (hγ.trans_le (hd n))]
    exact pairedRealDiagonal_upper R φ hφ s n
  let D := cZeroMultiplier (fun n => (d n : 𝕜)) ‖R‖ (norm_nonneg R) hdb
  let Dinv := cZeroReciprocalMultiplier (𝕜 := 𝕜) d hγ hd
  let U := pairedNormingOperator (φ ∘ s) (fun n => hφ (s n)) ψ hst
  let V := cZeroPairInsertion (𝕜 := 𝕜) s hs
  have hU : ‖U‖ ≤ 1 := norm_pairedNormingOperator_le _ _ _ _
  have hV : ‖V‖ ≤ 1 := norm_cZeroPairInsertion_le _ _
  have hInvD : Dinv.comp D = ContinuousLinearMap.id 𝕜 (cZero 𝕜) :=
    cZeroReciprocalMultiplier_leftInverse d hγ hd (norm_nonneg R) hdb
  have he : ‖D - (U.comp R).comp V‖ ≤ ε := by
    rw [← hbudget]
    apply pairedNormingOperator_error R φ hφ ψ s hs hst halign D
      (fun a i => cZeroMultiplier_apply _ _ _ _ a i) w (fun j => (hw j).le) hws
    intro i j hij
    have h := hoff i j hij
    convert h using 1 <;> dsimp [v, w] <;> ring
  obtain ⟨W, hW, hnW⟩ := exists_factorization_of_approximate_diagonal R U V D Dinv
    hγ hε.le hεγ hU hV (norm_cZeroReciprocalMultiplier_le d hγ hd) hInvD he
  refine ⟨W, V, hW, ?_⟩
  have hδε : δ < γ - ε := by dsimp [ε]; linarith
  calc
    ‖W‖ * ‖V‖ ≤ (1 / (γ - ε)) * 1 :=
      mul_le_mul hnW hV (norm_nonneg V) (one_div_pos.mpr (sub_pos.mpr hεγ)).le
    _ = 1 / (γ - ε) := mul_one _
    _ < 1 / δ := one_div_lt_one_div_of_lt hδ hδε

end JLMS
