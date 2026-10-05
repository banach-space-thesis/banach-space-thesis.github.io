import ThesisCommon.Analysis.GowersMaureyBlockSums

/-! If a block subspace had no normalized m-piece average, recursive
grouping would force an exponential upper estimate on every long block sum.
The averages are actual finite vectors in the given subspace. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def HasBlockAverage (D : ConstructionData 𝕜) (Y : Submodule ℝ (C00 𝕜))
    (m : ℕ) (C : ℝ) : Prop :=
  ∃ x : Fin m → C00 𝕜, (∀ i, x i ∈ Y) ∧ Successive x ∧
    implicitNorm D (∑ i, x i) = 1 ∧ ∀ i, implicitNorm D (x i) ≤ C / m

theorem no_block_average_sum_bound (D : ConstructionData 𝕜) (Y : Submodule ℝ (C00 𝕜))
    {m : ℕ} (hm : 0 < m) {C : ℝ} (hC : 0 < C) (hno : ¬ HasBlockAverage D Y m C)
    {b : ℝ} (hb : 0 ≤ b) {x : Fin m → C00 𝕜} (hx : Successive x)
    (hy : ∀ i, x i ∈ Y) (hbound : ∀ i, implicitNorm D (x i) ≤ b) :
    implicitNorm D (∑ i, x i) ≤ (m : ℝ) * b / C := by
  classical
  by_contra! hlarge
  let p := implicitNorm D
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < p (∑ i, x i) :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg hmR.le hb) hC.le) hlarge
  let r := (p (∑ i, x i))⁻¹
  have hr : 0 < r := inv_pos.mpr hpos
  have hscale (y : C00 𝕜) : p (r • y) = r * p y := by
    have hh := map_smul_eq_mul (p.restrictScalars ℝ) r y
    simpa only [Real.norm_eq_abs, abs_of_pos hr] using hh
  apply hno
  refine ⟨fun i => r • x i, fun i => Y.smul_mem r (hy i), successive_real_smul hx r, ?_, ?_⟩
  · rw [← Finset.smul_sum]
    change p (r • ∑ i, x i) = 1
    rw [hscale]
    exact inv_mul_cancel₀ hpos.ne'
  · intro i
    change p (r • x i) ≤ C / m
    rw [hscale]
    calc
      r * p (x i) ≤ r * b := mul_le_mul_of_nonneg_left (hbound i) hr.le
      _ = b / p (∑ j, x j) := by dsimp [r]; ring
      _ ≤ C / m := (div_le_div_iff₀ hpos hmR).mpr (by
        have hh := (div_lt_iff₀ hC).mp hlarge
        nlinarith)

theorem no_block_average_power_bound (D : ConstructionData 𝕜) (Y : Submodule ℝ (C00 𝕜))
    {m : ℕ} (hm : 0 < m) {C : ℝ} (hC : 0 < C) (hno : ¬ HasBlockAverage D Y m C)
    (k : ℕ) (x : Fin (m ^ k) → C00 𝕜) (hx : Successive x)
    (hy : ∀ i, x i ∈ Y) (hbound : ∀ i, implicitNorm D (x i) ≤ 1) :
    implicitNorm D (∑ i, x i) ≤ ((m : ℝ) / C) ^ k := by
  classical
  induction k with
  | zero => simpa using hbound (0 : Fin 1)
  | succ k ih =>
    let e : Fin m × Fin (m ^ k) ≃ Fin (m ^ (k + 1)) :=
      finProdFinEquiv.trans (finCongr (pow_succ' m k).symm)
    let z (i : Fin m) (j : Fin (m ^ k)) := x (e (i, j))
    have hz (i : Fin m) : Successive (z i) := by
      intro a b hab
      apply hx
      change a.val + m ^ k * i.val < b.val + m ^ k * i.val
      exact Nat.add_lt_add_right hab _
    have hzg : Successive (fun i => ∑ j, z i j) := by
      apply successive_grouped_sums
      intro i j hij a b
      apply hx
      exact finProdFinEquiv_lt_of_first_lt hij a b
    have hsum : (∑ i, ∑ j, z i j) = ∑ l, x l := by
      simpa only [Fintype.sum_prod_type] using e.sum_comp x
    have hgroup (i : Fin m) : implicitNorm D (∑ j, z i j) ≤ ((m : ℝ) / C) ^ k :=
      ih (z i) (hz i) (fun j => hy (e (i, j))) (fun j => hbound (e (i, j)))
    have hstep := no_block_average_sum_bound D Y hm hC hno
      (pow_nonneg (div_nonneg (Nat.cast_nonneg m) hC.le) k) hzg
      (fun i => Y.sum_mem (fun j _ => hy (e (i, j)))) hgroup
    rw [hsum] at hstep
    calc
      implicitNorm D (∑ i, x i) ≤ (m : ℝ) * ((m : ℝ) / C) ^ k / C := hstep
      _ = ((m : ℝ) / C) ^ (k + 1) := by rw [pow_succ]; ring

end ThesisCommon.GowersMaurey
