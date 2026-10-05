import ThesisCommon.Analysis.LpOneRestriction
import Mathlib.Tactic.Linarith

/-! Bounded scalar tests and finite approximations in real ell-one, on an
arbitrary index set. These are used in the gliding-hump proof of Schur's theorem. -/
noncomputable section
open scoped BigOperators
open Filter
namespace ThesisCommon
variable {I : Type*}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem ellOne_test_summable (b : I → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (x : lp (fun _ : I => ℝ) 1) : Summable (fun i => b i * x i) :=
  (lp_one_hasSum_norm x).summable.of_norm_bounded (fun i => by
    rw [norm_mul, Real.norm_eq_abs (b i)]
    exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans_eq (one_mul _))

theorem ellOne_test_bound (b : I → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (x : lp (fun _ : I => ℝ) 1) : ‖∑' i, b i * x i‖ ≤ ‖x‖ :=
  (ellOne_test_summable b hb x).hasSum.norm_le_of_bounded (lp_one_hasSum_norm x)
    (fun i => by
      rw [norm_mul, Real.norm_eq_abs (b i)]
      exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans_eq (one_mul _))

/-- Pairing a real ell-one vector with any scalar family bounded by one. -/
def ellOneTest (b : I → ℝ) (hb : ∀ i, |b i| ≤ 1) :
    lp (fun _ : I => ℝ) 1 →L[ℝ] ℝ :=
  ({ toFun x := ∑' i, b i * x i
     map_add' x y := by
       simp only [lp.coeFn_add, Pi.add_apply, mul_add]
       exact (ellOne_test_summable b hb x).tsum_add (ellOne_test_summable b hb y)
     map_smul' c x := by
       simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
       simp_rw [← mul_assoc, mul_comm (b _) c, mul_assoc]
       exact tsum_mul_left } : lp (fun _ : I => ℝ) 1 →ₗ[ℝ] ℝ).mkContinuous 1
      (fun x => by simpa only [one_mul] using ellOne_test_bound b hb x)

theorem ellOneTest_bound (b : I → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (x : lp (fun _ : I => ℝ) 1) : |ellOneTest b hb x| ≤ ‖x‖ :=
  ellOne_test_bound b hb x

@[simp] theorem ellOneTest_single (b : I → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (i : I) (a : ℝ) : ellOneTest b hb (lp.single 1 i a) = b i * a := by
  classical
  change (∑' j, b j * lp.single (E := fun _ : I => ℝ) 1 i a j) = _
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, hj]

/-- The finite-coordinate truncation is close in norm. -/
theorem ellOne_exists_finite_approx (x : lp (fun _ : I => ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset I, ‖x - ∑ i ∈ F, lp.single 1 i (x i)‖ < ε := by
  have h := (lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) x)
  obtain ⟨F, hF⟩ := (Metric.tendsto_atTop.mp h) ε hε
  refine ⟨F, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hF F le_rfl

end ThesisCommon
