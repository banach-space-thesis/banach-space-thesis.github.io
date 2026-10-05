import ThesisCommon.Analysis.EllOneColumns
import Mathlib.Tactic.Linarith

/-! Bounded scalar tests and finite approximations for actual scalar ell-one,
over either real or complex scalars and with an arbitrary index set. -/
noncomputable section
open scoped BigOperators
open Filter
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜]
attribute [local instance] Classical.decEq Classical.propDecidable

theorem scalar_ellOne_test_summable (b : I → 𝕜) (hb : ∀ i, ‖b i‖ ≤ 1)
    (x : lp (fun _ : I => 𝕜) 1) : Summable (fun i => b i * x i) :=
  (ellOne_hasSum_norm x).summable.of_norm_bounded (fun i => by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans_eq (one_mul _))

theorem scalar_ellOne_test_bound (b : I → 𝕜) (hb : ∀ i, ‖b i‖ ≤ 1)
    (x : lp (fun _ : I => 𝕜) 1) : ‖∑' i, b i * x i‖ ≤ ‖x‖ :=
  (scalar_ellOne_test_summable b hb x).hasSum.norm_le_of_bounded (ellOne_hasSum_norm x)
    (fun i => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans_eq (one_mul _))

/-- Pairing a scalar ell-one vector with any scalar family bounded by one. -/
def scalarEllOneTest (b : I → 𝕜) (hb : ∀ i, ‖b i‖ ≤ 1) :
    lp (fun _ : I => 𝕜) 1 →L[𝕜] 𝕜 :=
  ({ toFun x := ∑' i, b i * x i
     map_add' x y := by
       simp only [lp.coeFn_add, Pi.add_apply, mul_add]
       exact (scalar_ellOne_test_summable b hb x).tsum_add
         (scalar_ellOne_test_summable b hb y)
     map_smul' c x := by
       simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
       simp_rw [← mul_assoc, mul_comm (b _) c, mul_assoc]
       exact tsum_mul_left } : lp (fun _ : I => 𝕜) 1 →ₗ[𝕜] 𝕜).mkContinuous 1
      (fun x => by simpa only [one_mul] using scalar_ellOne_test_bound b hb x)

theorem scalarEllOneTest_bound (b : I → 𝕜) (hb : ∀ i, ‖b i‖ ≤ 1)
    (x : lp (fun _ : I => 𝕜) 1) : ‖scalarEllOneTest b hb x‖ ≤ ‖x‖ :=
  scalar_ellOne_test_bound b hb x

@[simp] theorem scalarEllOneTest_single (b : I → 𝕜) (hb : ∀ i, ‖b i‖ ≤ 1)
    (i : I) (a : 𝕜) : scalarEllOneTest b hb (lp.single 1 i a) = b i * a := by
  change (∑' j, b j * lp.single (E := fun _ : I => 𝕜) 1 i a j) = _
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, hj]

theorem scalar_ellOne_exists_finite_approx (x : lp (fun _ : I => 𝕜) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset I, ‖x - ∑ i ∈ F, lp.single 1 i (x i)‖ < ε := by
  have h := lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) x
  obtain ⟨F, hF⟩ := (Metric.tendsto_atTop.mp h) ε hε
  refine ⟨F, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hF F le_rfl

end ThesisCommon
