import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Tactic.GCongr

/-! Coordinate operators on actual vector-valued ℓp spaces, 1 ≤ p ≤ ∞.
Index sets may be arbitrary, including empty and uncountable sets.
The finite-p proofs use the defining sums of pth powers; infinity uses
pointwise bounds. This is shared infrastructure for both primariness papers.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

private theorem sum_rpow_bound (hp : 0 < p.toReal)
    (x : lp (fun _ : ι => X) p) (f : ι → Y) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C * ‖x i‖) (s : Finset ι) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ (C * ‖x‖) ^ p.toReal := by
  calc
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ∑ i ∈ s, (C * ‖x i‖) ^ p.toReal := by
      exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (hf i) hp.le
    _ = C ^ p.toReal * ∑ i ∈ s, ‖x i‖ ^ p.toReal := by
      simp_rw [Real.mul_rpow hC (norm_nonneg _), Finset.mul_sum]
    _ ≤ C ^ p.toReal * ‖x‖ ^ p.toReal :=
      mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp x s) (Real.rpow_nonneg hC _)
    _ = (C * ‖x‖) ^ p.toReal := (Real.mul_rpow hC (norm_nonneg _)).symm

/-- A pointwise bound by C times an ℓp sequence gives genuine ℓp membership. -/
theorem mem_lp_of_norm_le_mul (x : lp (fun _ : ι => X) p) (f : ι → Y)
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
    exact memℓp_gen' (sum_rpow_bound hp' x f hC hf)

/-- The same domination gives the exact operator bound, without finite support. -/
theorem lp_norm_le_mul_of_pointwise (x : lp (fun _ : ι => X) p)
    (y : lp (fun _ : ι => Y) p) {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ i, ‖y i‖ ≤ C * ‖x i‖) : ‖y‖ ≤ C * ‖x‖ := by
  by_cases hp : p = ∞
  · subst p
    exact lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _)) fun i =>
      (hy i).trans (mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) hC)
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    exact lp.norm_le_of_forall_sum_le hp' (mul_nonneg hC (norm_nonneg _))
      (sum_rpow_bound hp' x y hC hy)

/-- Uniformly bounded coordinate maps act diagonally on ℓp for every p≥1. -/
def lpDiagonal (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : ι → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    lp (fun _ : ι => X) p →L[𝕜] lp (fun _ : ι => Y) p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => F i (x i), mem_lp_of_norm_le_mul x _ hC
        (fun i => ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _)))⟩
      map_add' := by intros; ext i; exact map_add _ _ _
      map_smul' := by intros; ext i; exact map_smul _ _ _ }
    C (fun x => lp_norm_le_mul_of_pointwise x _ hC (fun i =>
      ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _))))

@[simp] theorem lpDiagonal_apply (F : ι → X →L[𝕜] Y) (C : ℝ) (hC hF)
    (x : lp (fun _ : ι => X) p) (i : ι) : lpDiagonal p F C hC hF x i = F i (x i) := rfl

theorem norm_lpDiagonal_le (F : ι → X →L[𝕜] Y) (C : ℝ) (hC hF) :
    ‖lpDiagonal p F C hC hF‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

private theorem lp_restrict_mem (e : ι ↪ κ) (x : lp (fun _ : κ => X) p) :
    Memℓp (fun i => x (e i)) p := by
  by_cases hp : p = ∞
  · subst p
    exact memℓp_infty ⟨‖x‖, by
      rintro _ ⟨i, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (e i)⟩
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    exact memℓp_gen (((lp.memℓp x).summable hp').comp_injective e.injective)

private theorem lp_restrict_norm_le (e : ι ↪ κ) (x : lp (fun _ : κ => X) p) :
    ‖(⟨fun i => x (e i), lp_restrict_mem e x⟩ : lp (fun _ : ι => X) p)‖ ≤ ‖x‖ := by
  by_cases hp : p = ∞
  · subst p
    exact lp.norm_le_of_forall_le (norm_nonneg _) fun i =>
      lp.norm_apply_le_norm ENNReal.top_ne_zero x (e i)
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    apply lp.norm_le_of_tsum_le hp' (norm_nonneg _)
    rw [lp.norm_rpow_eq_tsum hp']
    exact Summable.tsum_le_tsum_of_inj e e.injective
      (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun i => le_rfl) (((lp.memℓp x).summable hp').comp_injective e.injective)
      ((lp.memℓp x).summable hp')

/-- The canonical contraction reading the coordinates in the image of e. -/
def lpRestrict (p : ℝ≥0∞) [Fact (1 ≤ p)] (e : ι ↪ κ) :
    lp (fun _ : κ => X) p →L[𝕜] lp (fun _ : ι => X) p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => x (e i), lp_restrict_mem e x⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa using lp_restrict_norm_le e x)

@[simp] theorem lpRestrict_apply (e : ι ↪ κ) (x : lp (fun _ : κ => X) p) (i : ι) :
    lpRestrict (𝕜 := 𝕜) p e x i = x (e i) := rfl

theorem norm_lpRestrict_le (e : ι ↪ κ) :
    ‖lpRestrict (𝕜 := 𝕜) (X := X) p e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

private theorem extend_rpow (e : ι ↪ κ) (f : ι → X) {q : ℝ} (hq : q ≠ 0) :
    (fun k => ‖Function.extend e f 0 k‖ ^ q) =
      Function.extend e (fun i => ‖f i‖ ^ q) 0 := by
  classical
  funext k
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    simp only [e.injective.extend_apply]
  · simp only [Function.extend_apply' _ _ _ h, Pi.zero_apply, norm_zero, Real.zero_rpow hq]

private theorem lp_extend_mem (e : ι ↪ κ) (x : lp (fun _ : ι => X) p) :
    Memℓp (Function.extend e x 0) p := by
  classical
  by_cases hp : p = ∞
  · subst p
    apply memℓp_infty
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    change ‖Function.extend e x 0 k‖ ≤ ‖x‖
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [e.injective.extend_apply]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i
    · simp only [Function.extend_apply' _ _ _ hk, Pi.zero_apply, norm_zero]
      exact norm_nonneg _
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    apply memℓp_gen
    rw [extend_rpow e x hp'.ne']
    exact (summable_extend_zero e.injective).mpr ((lp.memℓp x).summable hp')

private theorem lp_extend_norm_le (e : ι ↪ κ) (x : lp (fun _ : ι => X) p) :
    ‖(⟨Function.extend e x 0, lp_extend_mem e x⟩ : lp (fun _ : κ => X) p)‖ ≤ ‖x‖ := by
  classical
  by_cases hp : p = ∞
  · subst p
    apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro k
    change ‖Function.extend e x 0 k‖ ≤ ‖x‖
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [e.injective.extend_apply]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i
    · simp only [Function.extend_apply' _ _ _ hk, Pi.zero_apply, norm_zero]
      exact norm_nonneg _
  · have hp' : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    apply lp.norm_le_of_tsum_le hp' (norm_nonneg _)
    change (∑' k, ‖Function.extend e x 0 k‖ ^ p.toReal) ≤ ‖x‖ ^ p.toReal
    rw [extend_rpow e x hp'.ne', tsum_extend_zero e.injective, lp.norm_rpow_eq_tsum hp']

/-- Isometric insertion on an arbitrary set of coordinates, zero elsewhere. -/
def lpExtend (p : ℝ≥0∞) [Fact (1 ≤ p)] (e : ι ↪ κ) :
    lp (fun _ : ι => X) p →L[𝕜] lp (fun _ : κ => X) p := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun x => ⟨Function.extend e x 0, lp_extend_mem e x⟩
      map_add' := ?_
      map_smul' := ?_ } 1 (fun x => by simpa using lp_extend_norm_le e x)
  · intro x y
    ext k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  · intro a x
    ext k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

@[simp] theorem lpExtend_apply_image (e : ι ↪ κ) (x : lp (fun _ : ι => X) p) (i : ι) :
    lpExtend (𝕜 := 𝕜) p e x (e i) = x i := by
  simp [lpExtend, e.injective.extend_apply]

theorem norm_lpExtend_le (e : ι ↪ κ) :
    ‖lpExtend (𝕜 := 𝕜) (X := X) p e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem lpRestrict_comp_extend (e : ι ↪ κ) :
    (lpRestrict (𝕜 := 𝕜) (X := X) p e).comp (lpExtend p e) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : ι => X) p) := by
  ext x i
  simp

end ThesisCommon
