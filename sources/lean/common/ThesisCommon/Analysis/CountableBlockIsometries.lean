import ThesisCommon.Analysis.LpSelfSimilarity
import ThesisCommon.Analysis.CZeroSelfSimilarity
import Mathlib.Logic.Denumerable

/-! Exact coordinate flattening for nonempty countable blocks. The coordinate
bijection is chosen on Δ × ℕ, so finite nonempty Δ is included. All maps act
on the actual lp and C₀ spaces and preserve their norms exactly. -/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
universe u v
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Δ : Type u}

/-- A nonempty countable family of infinite countable blocks is countably infinite. -/
def countableBlockIndexEquiv (Δ : Type u) [Nonempty Δ] [Countable Δ] : Δ × ℕ ≃ ℕ := by
  letI : Infinite (Δ × ℕ) := Infinite.of_injective
    (fun n : ℕ => (Classical.choice ‹Nonempty Δ›, n))
    (fun _ _ h => congrArg Prod.snd h)
  exact Classical.choice (nonempty_equiv_of_countable : Nonempty (Δ × ℕ ≃ ℕ))

def countableBlockEmbedding (φ : Δ × ℕ ≃ ℕ) (i : Δ) : ℕ ↪ ℕ where
  toFun n := φ (i, n)
  inj' := fun _ _ h => congrArg Prod.snd (φ.injective h)

section Lp
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (φ : Δ × ℕ ≃ ℕ)

include hp in
theorem lp_block_pair_summable
    (x : lp (fun _ : Δ => lp (fun _ : ℕ => X) p) p) :
    Summable (fun ij : Δ × ℕ => ‖x ij.1 ij.2‖ ^ p.toReal) := by
  apply (summable_prod_of_nonneg (fun ij => Real.rpow_nonneg (norm_nonneg _) _)).mpr
  refine ⟨fun i => (lp.memℓp (x i)).summable hp, ?_⟩
  exact ((lp.memℓp x).summable hp).congr (fun i => lp.norm_rpow_eq_tsum hp (x i))

def lpBlockFlattenValue
    (x : lp (fun _ : Δ => lp (fun _ : ℕ => X) p) p) : lp (fun _ : ℕ => X) p :=
  ⟨fun n => x (φ.symm n).1 (φ.symm n).2,
    memℓp_gen ((φ.symm.summable_iff
      (f := fun ij : Δ × ℕ => ‖x ij.1 ij.2‖ ^ p.toReal)).mpr
        (lp_block_pair_summable p hp x))⟩

theorem norm_lpBlockFlattenValue
    (x : lp (fun _ : Δ => lp (fun _ : ℕ => X) p) p) :
    ‖lpBlockFlattenValue p hp φ x‖ = ‖x‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  calc
    _ = ∑' n, ‖x (φ.symm n).1 (φ.symm n).2‖ ^ p.toReal :=
      lp.norm_rpow_eq_tsum hp _
    _ = ∑' ij : Δ × ℕ, ‖x ij.1 ij.2‖ ^ p.toReal :=
      φ.symm.tsum_eq (fun ij : Δ × ℕ => ‖x ij.1 ij.2‖ ^ p.toReal)
    _ = ∑' i, ∑' j, ‖x i j‖ ^ p.toReal := (lp_block_pair_summable p hp x).tsum_prod
    _ = ∑' i, ‖x i‖ ^ p.toReal :=
      tsum_congr (fun i => (lp.norm_rpow_eq_tsum hp (x i)).symm)
    _ = ‖x‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hp x).symm

def lpBlockUnflattenValue (x : lp (fun _ : ℕ => X) p) :
    lp (fun _ : Δ => lp (fun _ : ℕ => X) p) p :=
  ⟨fun i => lpRestrict (𝕜 := 𝕜) p (countableBlockEmbedding φ i) x, by
    apply memℓp_gen
    have hpair : Summable (fun ij : Δ × ℕ => ‖x (φ ij)‖ ^ p.toReal) :=
      (φ.summable_iff (f := fun n => ‖x n‖ ^ p.toReal)).mpr
        ((lp.memℓp x).summable hp)
    have hs := ((summable_prod_of_nonneg (fun ij : Δ × ℕ =>
      Real.rpow_nonneg (norm_nonneg (x (φ ij))) _)).mp hpair).2
    exact hs.congr (fun i => (lp.norm_rpow_eq_tsum hp
      (lpRestrict (𝕜 := 𝕜) p (countableBlockEmbedding φ i) x)).symm)⟩

/-- Flattening along the supplied bijection is a surjective linear isometry. -/
def lpBlockFlattenIsometry :
    lp (fun _ : Δ => lp (fun _ : ℕ => X) p) p ≃ₗᵢ[𝕜] lp (fun _ : ℕ => X) p where
  toFun := lpBlockFlattenValue p hp φ
  invFun := lpBlockUnflattenValue (𝕜 := 𝕜) p hp φ
  map_add' := by intros; ext n; rfl
  map_smul' := by intros; ext n; rfl
  left_inv := by
    intro x
    ext i n
    change x (φ.symm (φ (i, n))).1 (φ.symm (φ (i, n))).2 = x i n
    rw [φ.symm_apply_apply]
  right_inv := by
    intro x
    ext n
    change x (φ ((φ.symm n).1, (φ.symm n).2)) = x n
    simp only [Prod.mk.eta, φ.apply_symm_apply]
  norm_map' := norm_lpBlockFlattenValue p hp φ

@[simp] theorem lpBlockFlattenIsometry_apply
    (x : lp (fun _ : Δ => lp (fun _ : ℕ => X) p) p) (n : ℕ) :
    lpBlockFlattenIsometry (𝕜 := 𝕜) (X := X) p hp φ x n =
      x (φ.symm n).1 (φ.symm n).2 := rfl

end Lp

section CZero
variable [TopologicalSpace Δ] [DiscreteTopology Δ] (φ : Δ × ℕ ≃ ℕ)

theorem cZero_block_finite_norm_exception (x : C₀(Δ, X)) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖x i‖ < ε}.Finite := by
  have h := Metric.tendsto_nhds.mp x.zero_at_infty' ε hε
  rw [cocompact_eq_cofinite] at h
  simpa only [dist_zero_right] using mem_cofinite.mp h

def cZeroBlockFlattenValue (x : C₀(Δ, CZeroSum X)) : CZeroSum X where
  toFun n := x (φ.symm n).1 (φ.symm n).2
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [cocompact_eq_cofinite]
    let A := {i | ¬ ‖x i‖ < ε}
    let B := fun i => {j | ¬ ‖x i j‖ < ε}
    have hA : A.Finite := cZero_block_finite_norm_exception x hε
    have hB (i : Δ) : (B i).Finite := cZero_finite_norm_exception (x i) hε
    have hbad : (⋃ i ∈ A, (fun j => φ (i, j)) '' B i).Finite :=
      hA.biUnion (fun i _ => (hB i).image (fun j => φ (i, j)))
    filter_upwards [hbad.compl_mem_cofinite] with n hn
    rw [dist_zero_right]
    by_contra hnlarge
    have hi : (φ.symm n).1 ∈ A := by
      intro hsmall
      exact hnlarge ((BoundedContinuousFunction.norm_coe_le_norm
        (x (φ.symm n).1).toBCF (φ.symm n).2).trans_lt hsmall)
    have hj : (φ.symm n).2 ∈ B (φ.symm n).1 := hnlarge
    exact hn (Set.mem_iUnion.mpr ⟨(φ.symm n).1,
      Set.mem_iUnion.mpr ⟨hi, ⟨(φ.symm n).2, hj, φ.apply_symm_apply n⟩⟩⟩)

theorem norm_cZeroBlockFlattenValue_le (x : C₀(Δ, CZeroSum X)) :
    ‖cZeroBlockFlattenValue φ x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro n
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (x (φ.symm n).1).toBCF (φ.symm n).2).trans
      (BoundedContinuousFunction.norm_coe_le_norm x.toBCF (φ.symm n).1)

def cZeroBlockUnflattenValue (x : CZeroSum X) : C₀(Δ, CZeroSum X) where
  toFun i := cZeroRead (countableBlockEmbedding φ i) x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [cocompact_eq_cofinite]
    let B := {n | ¬ ‖x n‖ < ε / 2}
    have hB : B.Finite := cZero_finite_norm_exception x (half_pos hε)
    filter_upwards [(hB.image (fun n => (φ.symm n).1)).compl_mem_cofinite] with i hi
    have hpoint (j : ℕ) : ‖x (φ (i, j))‖ < ε / 2 := by
      by_contra hlarge
      exact hi ⟨φ (i, j), hlarge, by simp⟩
    have hnorm : ‖cZeroRead (countableBlockEmbedding φ i) x‖ ≤ ε / 2 := by
      apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
      intro j
      exact (hpoint j).le
    simpa only [dist_zero_right] using hnorm.trans_lt (half_lt_self hε)

theorem norm_cZeroBlockUnflattenValue_le (x : CZeroSum X) :
    ‖cZeroBlockUnflattenValue φ x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro i
  exact norm_cZeroRead_le (countableBlockEmbedding φ i) x

theorem cZeroBlockUnflatten_flatten (x : C₀(Δ, CZeroSum X)) :
    cZeroBlockUnflattenValue φ (cZeroBlockFlattenValue φ x) = x := by
  ext i j
  change x (φ.symm (φ (i, j))).1 (φ.symm (φ (i, j))).2 = x i j
  rw [φ.symm_apply_apply]

/-- The inverse restriction also contracts, so flattening preserves the exact sup norm. -/
theorem norm_cZeroBlockFlattenValue (x : C₀(Δ, CZeroSum X)) :
    ‖cZeroBlockFlattenValue φ x‖ = ‖x‖ := by
  apply le_antisymm (norm_cZeroBlockFlattenValue_le φ x)
  have h := norm_cZeroBlockUnflattenValue_le φ (cZeroBlockFlattenValue φ x)
  rwa [cZeroBlockUnflatten_flatten] at h

/-- Flattening of the actual vanishing-at-infinity spaces along a block bijection. -/
def cZeroBlockFlattenIsometry : C₀(Δ, CZeroSum X) ≃ₗᵢ[𝕜] CZeroSum X where
  toFun := cZeroBlockFlattenValue φ
  invFun := cZeroBlockUnflattenValue φ
  map_add' := by intros; ext n; rfl
  map_smul' := by intros; ext n; rfl
  left_inv := cZeroBlockUnflatten_flatten φ
  right_inv := by
    intro x
    ext n
    change x (φ ((φ.symm n).1, (φ.symm n).2)) = x n
    simp only [Prod.mk.eta, φ.apply_symm_apply]
  norm_map' := norm_cZeroBlockFlattenValue φ

@[simp] theorem cZeroBlockFlattenIsometry_apply (x : C₀(Δ, CZeroSum X)) (n : ℕ) :
    cZeroBlockFlattenIsometry (𝕜 := 𝕜) (X := X) φ x n =
      x (φ.symm n).1 (φ.symm n).2 := rfl

end CZero
end ThesisCommon
