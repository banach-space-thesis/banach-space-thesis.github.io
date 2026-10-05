import ThesisCommon.Analysis.LpOperators

/-! Uniformly bounded coordinate maps and isomorphisms on genuine dependent
lp families, for every p at least one, including infinity. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 ι : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

theorem lp_family_sum_rpow_bound (hp : 0 < p.toReal) (x : lp E p) (f : ∀ i, F i)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C * ‖x i‖) (s : Finset ι) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ (C * ‖x‖) ^ p.toReal := by
  calc
    _ ≤ ∑ i ∈ s, (C * ‖x i‖) ^ p.toReal :=
      Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (hf i) hp.le
    _ = C ^ p.toReal * ∑ i ∈ s, ‖x i‖ ^ p.toReal := by
      simp_rw [Real.mul_rpow hC (norm_nonneg _), Finset.mul_sum]
    _ ≤ C ^ p.toReal * ‖x‖ ^ p.toReal :=
      mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp x s) (Real.rpow_nonneg hC _)
    _ = (C * ‖x‖) ^ p.toReal := (Real.mul_rpow hC (norm_nonneg _)).symm

theorem mem_lp_family_of_norm_le_mul (x : lp E p) (f : ∀ i, F i)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C * ‖x i‖) : Memℓp f p := by
  by_cases hp : p = ∞
  · subst p
    apply memℓp_infty
    refine ⟨C * ‖x‖, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (hf i).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) hC)
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    exact memℓp_gen' (lp_family_sum_rpow_bound hp' x f hC hf)

theorem lp_family_norm_le_mul_of_pointwise (x : lp E p) (y : lp F p)
    {C : ℝ} (hC : 0 ≤ C) (hy : ∀ i, ‖y i‖ ≤ C * ‖x i‖) : ‖y‖ ≤ C * ‖x‖ := by
  by_cases hp : p = ∞
  · subst p
    exact lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _)) fun i =>
      (hy i).trans (mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) hC)
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    exact lp.norm_le_of_forall_sum_le hp' (mul_nonneg hC (norm_nonneg _))
      (lp_family_sum_rpow_bound hp' x y hC hy)

def lpFamilyDiagonal (A : ∀ i, E i →L[𝕜] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) : lp E p →L[𝕜] lp F p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => A i (x i), mem_lp_family_of_norm_le_mul x _ hC
        (fun i => ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)))⟩
      map_add' := by intros; ext i; exact map_add _ _ _
      map_smul' := by intros; ext i; exact map_smul _ _ _ }
    C (fun x => lp_family_norm_le_mul_of_pointwise x _ hC (fun i =>
      ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))))

@[simp] theorem lpFamilyDiagonal_apply (A : ∀ i, E i →L[𝕜] F i) (C : ℝ) (hC hA)
    (x : lp E p) (i : ι) : lpFamilyDiagonal A C hC hA x i = A i (x i) := rfl

theorem lpFamilyDiagonal_norm_le (A : ∀ i, E i →L[𝕜] F i) (C : ℝ) (hC hA) :
    ‖lpFamilyDiagonal (p := p) A C hC hA‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

def lpFamilyMapEquiv (e : ∀ i, E i ≃L[𝕜] F i) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D) : lp E p ≃L[𝕜] lp F p :=
  { (lpFamilyDiagonal (fun i => (e i).toContinuousLinearMap) C hC he).toLinearMap with
    invFun := lpFamilyDiagonal (fun i => (e i).symm.toContinuousLinearMap) D hD hei
    left_inv := by intro x; ext i; exact (e i).symm_apply_apply (x i)
    right_inv := by intro x; ext i; exact (e i).apply_symm_apply (x i)
    continuous_toFun := (lpFamilyDiagonal (p := p) (fun i => (e i).toContinuousLinearMap) C hC he).continuous
    continuous_invFun := (lpFamilyDiagonal (p := p) (fun i => (e i).symm.toContinuousLinearMap) D hD hei).continuous }

@[simp] theorem lpFamilyMapEquiv_apply (e : ∀ i, E i ≃L[𝕜] F i) (C D : ℝ) (hC hD he hei)
    (x : lp E p) (i : ι) : lpFamilyMapEquiv e C D hC hD he hei x i = e i (x i) := rfl

theorem lpFamilyMapEquiv_norm_le (e : ∀ i, E i ≃L[𝕜] F i) (C D : ℝ) (hC hD he hei) :
    ‖(lpFamilyMapEquiv (p := p) e C D hC hD he hei).toContinuousLinearMap‖ ≤ C :=
  lpFamilyDiagonal_norm_le (fun i => (e i).toContinuousLinearMap) C hC he

theorem lpFamilyMapEquiv_symm_norm_le (e : ∀ i, E i ≃L[𝕜] F i) (C D : ℝ) (hC hD he hei) :
    ‖(lpFamilyMapEquiv (p := p) e C D hC hD he hei).symm.toContinuousLinearMap‖ ≤ D :=
  lpFamilyDiagonal_norm_le (fun i => (e i).symm.toContinuousLinearMap) D hD hei

end ThesisCommon
