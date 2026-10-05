import ThesisCommon.Analysis.RCLikeL1DisjointCut
import ThesisCommon.Analysis.LpOneFamilyOperators
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Operator.Mul

/-! Normalized functions carried by pairwise disjoint measurable sets span
an actual isometric, contractively complemented copy of scalar ℓ¹ in L1.
Both maps are constructed from the functions, cuts, and norming functionals. -/
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem exists_lOne_disjoint_isometric_retraction
    (f : ℕ → Lp 𝕜 1 μ) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (hf : ∀ n, lpCut (A n) (hA n) (f n) = f n)
    (hnorm : ∀ n, ‖f n‖ = 1) :
    ∃ V : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] Lp 𝕜 1 μ,
      ∃ U : Lp 𝕜 1 μ →L[𝕜] lp (fun _ : ℕ => 𝕜) 1,
        (∀ n, V (lp.single 1 n 1) = f n) ∧
        U.comp V.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ ∧
        ‖U‖ ≤ 1 ∧ ‖V.toContinuousLinearMap‖ = 1 := by
  choose φ hφ hφf using fun n => exists_dual_vector'' 𝕜 (f n)
  let U := scalarDisjointCutToEllOne A hA hd φ hφ
  have hU : ‖U‖ ≤ 1 := norm_scalarDisjointCutToEllOne_le A hA hd φ hφ
  have hUf (m : ℕ) : U (f m) = lp.single 1 m 1 := by
    apply lp.ext
    funext n
    change φ n (lpCut (A n) (hA n) (f m)) = lp.single (E := fun _ : ℕ => 𝕜) 1 m 1 n
    by_cases hnm : n = m
    · subst n
      rw [hf, hφf, hnorm]
      simp
    · rw [lpCut_eq_zero_of_disjoint_cut_eq_self (hA n) (hA m) (hd hnm) (hf m),
        map_zero, lp.single_apply_ne 1 m 1 hnm]
  let B : ℕ → 𝕜 →L[𝕜] Lp 𝕜 1 μ := fun n => ContinuousLinearMap.toSpanSingleton 𝕜 (f n)
  have hB : ∀ n, ‖B n‖ ≤ 1 := fun n => by
    rw [ContinuousLinearMap.norm_toSpanSingleton, hnorm]
  let V₀ := lpOneFamilyOperator B 1 zero_le_one hB
  have hV₀ : ‖V₀‖ ≤ 1 := norm_lpOneFamilyOperator_le B 1 zero_le_one hB
  have hVs (n : ℕ) (a : 𝕜) : V₀ (lp.single 1 n a) = a • f n :=
    by
      have h := lpOneFamilyOperator_single B 1 zero_le_one hB n a
      convert h using 1
      congr 1
      apply lp.ext
      funext j
      by_cases hj : j = n <;> simp [lp.single_apply, hj]
  have hUV : U.comp V₀ = ContinuousLinearMap.id 𝕜 _ := by
    apply lp.ext_continuousLinearMap (by simp)
    intro n
    apply ContinuousLinearMap.ext
    intro a
    change U (V₀ (lp.single 1 n a)) = lp.single 1 n a
    rw [hVs, map_smul, hUf, ← lp.single_smul]
    simp
  have hnormV (x : lp (fun _ : ℕ => 𝕜) 1) : ‖V₀ x‖ = ‖x‖ := by
    apply le_antisymm
    · exact (V₀.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hV₀ (norm_nonneg x))
    · have hx : U (V₀ x) = x := DFunLike.congr_fun hUV x
      calc
        ‖x‖ = ‖U (V₀ x)‖ := congrArg norm hx.symm
        _ ≤ ‖U‖ * ‖V₀ x‖ := U.le_opNorm _
        _ ≤ ‖V₀ x‖ := mul_le_of_le_one_left (norm_nonneg _) hU
  let V : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] Lp 𝕜 1 μ :=
    { V₀.toLinearMap with norm_map' := hnormV }
  refine ⟨V, U, ?_, hUV, hU, ?_⟩
  · intro n
    change V₀ (lp.single 1 n 1) = f n
    rw [hVs, one_smul]
  · apply le_antisymm hV₀
    have h := V₀.le_opNorm (lp.single 1 0 (1 : 𝕜))
    simpa only [hVs, one_smul, hnorm, lp.norm_single (by simp : (0 : ENNReal) < 1),
      norm_one, mul_one] using h

end ThesisCommon
