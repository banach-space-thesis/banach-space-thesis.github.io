import ThesisCommon.LpCut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Disjoint measurable cuts yield actual contractions from real or complex
L1 to scalar ℓ¹. No finiteness assumption on the measure is needed. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem norm_lOneCut_eq_integral_rclike (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) : ‖lpCut A hA f‖ = ∫ x in A, ‖f x‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖lpCut A hA f x‖ ∂μ) = ∫ x, A.indicator (fun y => ‖f y‖) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [lpCut_coe A hA f] with x hx
      rw [hx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    _ = _ := integral_indicator hA

theorem sum_norm_lOneCut_le_rclike (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (f : Lp 𝕜 1 μ) (F : Finset ℕ) :
    ∑ n ∈ F, ‖lpCut (A n) (hA n) f‖ ≤ ‖f‖ := by
  simp_rw [norm_lOneCut_eq_integral_rclike]
  rw [← integral_biUnion_finset F (fun n _ => hA n)
    (fun i _ j _ hij => hd hij) (fun _ _ => (L1.integrable_coeFn f).norm.integrableOn)]
  rw [L1.norm_eq_integral_norm]
  exact setIntegral_le_integral (L1.integrable_coeFn f).norm
    (Eventually.of_forall fun x => norm_nonneg (f x))

def scalarDisjointCutToEllOne (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (φ : ℕ → (Lp 𝕜 1 μ →L[𝕜] 𝕜))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) : Lp 𝕜 1 μ →L[𝕜] lp (fun _ : ℕ => 𝕜) 1 := by
  have hsum : ∀ f : Lp 𝕜 1 μ, ∀ F : Finset ℕ,
      ∑ n ∈ F, ‖φ n (lpCut (A n) (hA n) f)‖ ≤ ‖f‖ := by
    intro f F
    apply le_trans (Finset.sum_le_sum fun n _ => (φ n).le_opNorm _ |>.trans ?_)
      (sum_norm_lOneCut_le_rclike A hA hd f F)
    exact mul_le_of_le_one_left (norm_nonneg _) (hφ n)
  let L : Lp 𝕜 1 μ →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) 1 :=
    { toFun := fun f => ⟨fun n => φ n (lpCut (A n) (hA n) f),
        memℓp_gen' (by simpa only [ENNReal.toReal_one, Real.rpow_one] using hsum f)⟩
      map_add' := by intro f g; apply lp.ext; funext n; simp [lpCut_add]
      map_smul' := by intro c f; apply lp.ext; funext n; simp [lpCut_smul] }
  exact L.mkContinuous 1 (fun f => by
    simpa only [one_mul] using lp.norm_le_of_forall_sum_le
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (norm_nonneg f)
      (f := L f) (by simpa only [ENNReal.toReal_one, Real.rpow_one] using hsum f))

theorem scalarDisjointCutToEllOne_apply (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (φ : ℕ → (Lp 𝕜 1 μ →L[𝕜] 𝕜))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (f : Lp 𝕜 1 μ) (n : ℕ) :
    scalarDisjointCutToEllOne A hA hd φ hφ f n = φ n (lpCut (A n) (hA n) f) := rfl

theorem norm_scalarDisjointCutToEllOne_le (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (φ : ℕ → (Lp 𝕜 1 μ →L[𝕜] 𝕜))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) : ‖scalarDisjointCutToEllOne A hA hd φ hφ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (1 : ENNReal).toReal) (norm_nonneg f)
  intro F
  simp only [ENNReal.toReal_one, Real.rpow_one, scalarDisjointCutToEllOne_apply]
  apply (Finset.sum_le_sum fun n _ => ((φ n).le_opNorm _).trans ?_).trans
    (sum_norm_lOneCut_le_rclike A hA hd f F)
  exact mul_le_of_le_one_left (norm_nonneg _) (hφ n)

theorem lpCut_eq_zero_of_disjoint_cut_eq_self
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B) {f : Lp 𝕜 1 μ} (hf : lpCut B hB f = f) :
    lpCut A hA f = 0 := by
  apply Lp.ext
  have hself : f =ᵐ[μ] B.indicator f := by simpa only [hf] using lpCut_coe B hB f
  filter_upwards [lpCut_coe A hA f, hself, Lp.coeFn_zero 𝕜 1 μ] with x hcut hx hz
  rw [hcut, hz]
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := fun hxB => Set.disjoint_left.mp hd hxA hxB
    simp only [Set.indicator_of_notMem hxB] at hx
    simp [hxA, hx]
  · simp [hxA]

end ThesisCommon
