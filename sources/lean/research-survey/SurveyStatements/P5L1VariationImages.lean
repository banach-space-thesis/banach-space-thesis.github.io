import SurveyStatements.P5L1VariationBranch
import SurveyStatements.P5L1VariationRecurrence
import SurveyStatements.P5Support.LpHaarLevelVariation

/-! Exact images of normalized dyadic leaf tests under an actual bounded
Haar multiplier, and their values on all preceding disjoint rings. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
namespace DyadicBranch
variable {r : ℕ} (B : DyadicBranch r) (𝕜 : Type*) [RCLike 𝕜]

def density (j : ℕ) : IntervalL1 𝕜 := cellDensity 𝕜 (r + j) (B.index j)

def leafTest (N : ℕ) : IntervalL1 𝕜 := B.density 𝕜 N - B.density 𝕜 0

def symbol (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (j : ℕ) : 𝕜 :=
  d (r + j) (B.index j)

theorem leafTest_norm_le (N : ℕ) : ‖B.leafTest 𝕜 N‖ ≤ 2 :=
  cellDensity_difference_norm_le 𝕜 (r + N) (B.index N) (r + 0) (B.index 0)
    (B.index N).isLt (B.index 0).isLt

theorem leafTest_eq_sum (N : ℕ) :
    B.leafTest 𝕜 N = ∑ j ∈ Finset.range N, (B.density 𝕜 (j + 1) - B.density 𝕜 j) := by
  induction N with
  | zero => simp [leafTest]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [leafTest]
      abel

theorem leafTest_image_eq_sum
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    (N : ℕ) :
    D (B.leafTest 𝕜 N) = ∑ j ∈ Finset.range N,
      B.symbol 𝕜 d j • (B.density 𝕜 (j + 1) - B.density 𝕜 j) := by
  rw [B.leafTest_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact cellDensity_multiplier_difference 𝕜 D d hD (r + j)
    (B.index j) (B.index (j + 1)) (B.parent j)

theorem leafTest_image_on_annulus
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    (N j : ℕ) (hj : j < N) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ B.annulus j →
      D (B.leafTest 𝕜 N) x =
        (2 : 𝕜) ^ (r + j) * defect (B.symbol 𝕜 d) j := by
  rw [B.leafTest_image_eq_sum 𝕜 D d hD N]
  have hterms : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ i : ℕ,
      (B.symbol 𝕜 d i • (B.density 𝕜 (i + 1) - B.density 𝕜 i)) x =
        B.symbol 𝕜 d i * (B.density 𝕜 (i + 1) x - B.density 𝕜 i x) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (B.symbol 𝕜 d i)
        (B.density 𝕜 (i + 1) - B.density 𝕜 i),
      Lp.coeFn_sub (B.density 𝕜 (i + 1)) (B.density 𝕜 i)] with x hsmul hsub
    simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hsub] using hsmul
  have hvalues : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ i : ℕ,
      x ∈ B.annulus j → B.density 𝕜 i x =
        if i ≤ j then (2 : 𝕜) ^ (r + i) else 0 :=
    ae_all_iff.mpr (fun i => B.density_on_annulus 𝕜 i j)
  filter_upwards [lpHaar_coeFn_finset_sum (Finset.range N)
      (fun i => B.symbol 𝕜 d i • (B.density 𝕜 (i + 1) - B.density 𝕜 i)),
    hterms, hvalues] with x hsum hterm hvalue hx
  rw [hsum]
  simp_rw [hterm]
  have hzero : ∀ i ∈ Finset.range N, i ∉ Finset.range (j + 1) →
      B.symbol 𝕜 d i * (B.density 𝕜 (i + 1) x - B.density 𝕜 i x) = 0 := by
    intro i _ hi
    have hi' : j < i := by
      simp only [Finset.mem_range, not_lt] at hi
      omega
    rw [hvalue (i + 1) hx, hvalue i hx, if_neg (by omega), if_neg (by omega)]
    ring
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj)) hzero,
    Finset.sum_range_succ]
  have hbefore : ∀ i ∈ Finset.range j,
      B.symbol 𝕜 d i * (B.density 𝕜 (i + 1) x - B.density 𝕜 i x) =
        (2 : 𝕜) ^ (r + i) * B.symbol 𝕜 d i := by
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    rw [hvalue (i + 1) hx, hvalue i hx, if_pos (by omega), if_pos hi'.le]
    change _ = (2 : 𝕜) ^ (r + i) * B.symbol 𝕜 d i
    rw [show r + (i + 1) = (r + i) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hbefore, hvalue (j + 1) hx, hvalue j hx,
    if_neg (by omega), if_pos le_rfl, ← prefixAverage_weighted_sum]
  simp only [defect]
  ring

end DyadicBranch
end SurveyStatements.P5L1Variation
