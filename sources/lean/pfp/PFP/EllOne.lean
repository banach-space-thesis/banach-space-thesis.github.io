import ThesisCommon.Analysis.EllOneDiagonal
import PFP.MainStatements

namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Source `lmm: ell1-future-interference`, with an increasing enumeration
that also certifies infinitude of the selected set. -/
theorem lemma_3_9
    (T : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i j, i < j →
      ‖T (lp.single 1 (f j) (1 : 𝕜)) (f i)‖ < ε :=
  ellOne_future_interference T (fun _ => ε) (fun _ => hε)

/-- Source `lmm: small-norm-ell1`: the sum of absolute entries in every
column is < ε, hence the operator norm is ≤ ε. -/
theorem lemma_3_10
    (T : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    {ε : ℝ} (hε : 0 < ε)
    (hT : ∀ n, (∑' m, ‖T (lp.single 1 n (1 : 𝕜)) m‖) < ε) : ‖T‖ ≤ ε := by
  apply ellOne_norm_le_of_columns T hε.le
  intro n
  rw [ellOne_norm_eq_tsum]
  exact (hT n).le

/-- Theorem 3.11: for each ε>0, every operator on the actual ℓ₁ space admits
one of the two identity factorisations with product of norms at most 2+ε. -/
theorem theorem_3_11 : Theorem_3_11 𝕜 := ellOne_hasCPlusPFP_two

theorem ellOne_hasUPFP : HasUPFP 𝕜 (ScalarEllOne 𝕜) :=
  HasCPlusPFP.hasUPFP (by norm_num : (1 : ℝ) ≤ 2) theorem_3_11
end PFP
