import JLMS.L1Restriction

/-! Absolutely convergent synthesis on arbitrary scalar ℓ¹ index sets.
This is the analytic interface for the probability rows in Dale E. Alspach,
“Operators on C(ω^α) which do not preserve C(ω^α)”, Fund. Math. 153
(1997), 81–98, arXiv:math/9610215. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 I E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem alspach_summable_synthesis (v : I → E) (C : ℝ)
    (hv : ∀ i, ‖v i‖ ≤ C) (a : lp (fun _ : I => 𝕜) 1) :
    Summable (fun i => a i • v i) :=
  ((JLMS.ellOneOn_summable_norm a).mul_right C).of_norm_bounded fun i => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)

theorem alspach_norm_synthesis_le (v : I → E) (C : ℝ)
    (hv : ∀ i, ‖v i‖ ≤ C) (a : lp (fun _ : I => 𝕜) 1) :
    ‖∑' i, a i • v i‖ ≤ C * ‖a‖ := by
  have hb (i : I) : ‖a i • v i‖ ≤ ‖a i‖ * C := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
  have hn := ((JLMS.ellOneOn_summable_norm a).mul_right C).of_nonneg_of_le
    (fun _ => norm_nonneg _) hb
  calc
    _ ≤ ∑' i, ‖a i • v i‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, ‖a i‖ * C :=
      hn.tsum_le_tsum hb ((JLMS.ellOneOn_summable_norm a).mul_right C)
    _ = C * ‖a‖ := by rw [tsum_mul_right, JLMS.ellOneOn_norm_eq_tsum, mul_comm]

def alspachSynthesis (v : I → E) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    lp (fun _ : I => 𝕜) 1 →L[𝕜] E :=
  ({ toFun a := ∑' i, a i • v i
     map_add' a b := by
       change (∑' i, (a i + b i) • v i) = _
       simp_rw [add_smul]
       exact (alspach_summable_synthesis v C hv a).tsum_add
         (alspach_summable_synthesis v C hv b)
     map_smul' c a := by
       change (∑' i, (c * a i) • v i) = c • _
       simp_rw [mul_smul]
       exact (alspach_summable_synthesis v C hv a).tsum_const_smul c } :
      lp (fun _ : I => 𝕜) 1 →ₗ[𝕜] E).mkContinuous C
        (alspach_norm_synthesis_le v C hv)

@[simp] theorem alspachSynthesis_single (v : I → E) (C : ℝ)
    (hv : ∀ i, ‖v i‖ ≤ C) (i : I) (c : 𝕜) :
    alspachSynthesis v C hv (lp.single 1 i c) = c • v i := by
  classical
  change (∑' j, (lp.single 1 i c : lp (fun _ : I => 𝕜) 1) j • v j) = _
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, hj]

theorem alspachSynthesis_norm_le (v : I → E) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ C) : ‖alspachSynthesis (𝕜 := 𝕜) v C hv‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (alspach_norm_synthesis_le v C hv)

theorem alspach_lp_ext {S T : lp (fun _ : I => 𝕜) 1 →L[𝕜] E}
    (h : ∀ i, S (lp.single 1 i (1 : 𝕜)) = T (lp.single 1 i (1 : 𝕜))) : S = T := by
  apply lp.ext_continuousLinearMap (E := fun _ : I => 𝕜)
    (by norm_num : (1 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro c
  have he : lp.single (E := fun _ : I => 𝕜) 1 i c =
      c • lp.single (E := fun _ : I => 𝕜) 1 i (1 : 𝕜) := by
    rw [← lp.single_smul]
    simp
  change S (lp.single 1 i c) = T (lp.single 1 i c)
  rw [he, map_smul, map_smul, h]

end Posets
