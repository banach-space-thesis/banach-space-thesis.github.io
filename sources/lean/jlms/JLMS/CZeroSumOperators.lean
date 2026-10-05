import JLMS.CZeroSum
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Uniformly bounded coordinate maps on Banach c₀ sums

Kislyakov Lemma 1.1 follows by applying uniformly bounded coordinate
isomorphisms and their inverses. The operator construction is also useful
for the block maps appearing in the ordinal decomposition.
-/

noncomputable section
open Filter Topology
namespace JLMS.CZeroSum
universe u v v' w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u}
  {E : I → Type v} {F : I → Type v'}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

local instance cZeroSumOperatorsSourceGroup : NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance cZeroSumOperatorsSourceSpace : NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance
local instance cZeroSumOperatorsTargetGroup : NormedAddCommGroup (CZeroSum 𝕜 F) := inferInstance
local instance cZeroSumOperatorsTargetSpace : NormedSpace 𝕜 (CZeroSum 𝕜 F) := inferInstance

def mapBounded (f : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) (x : CZeroSum 𝕜 E) : CZeroSum 𝕜 F :=
  CZeroSum.mk (fun i => f i (x i))
    (squeeze_zero (fun i => norm_nonneg _) (fun i =>
      ((f i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right (hf i) (norm_nonneg _)))
      (by simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul x.tendsto_norm))

@[simp] theorem mapBounded_apply (f : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) (x : CZeroSum 𝕜 E) (i : I) :
    mapBounded f hC hf x i = f i (x i) := rfl

theorem norm_mapBounded_le (f : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) (x : CZeroSum 𝕜 E) : ‖mapBounded f hC hf x‖ ≤ C * ‖x‖ := by
  apply norm_le (mul_nonneg hC (norm_nonneg x))
  intro i
  exact ((f i).le_opNorm (x i)).trans
    (mul_le_mul (hf i) (x.norm_apply_le_norm i) (norm_nonneg _) hC)

def mapCLM (f : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 F :=
  ({ toFun := mapBounded f hC hf
     map_add' x y := by ext i; exact (f i).map_add _ _
     map_smul' c x := by ext i; exact (f i).map_smul c _ } :
      CZeroSum 𝕜 E →ₗ[𝕜] CZeroSum 𝕜 F).mkContinuous C (norm_mapBounded_le f hC hf)

@[simp] theorem mapCLM_apply (f : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) (x : CZeroSum 𝕜 E) (i : I) :
    mapCLM f hC hf x i = f i (x i) := rfl

theorem norm_mapCLM_le (f : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) : ‖mapCLM f hC hf‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_mapBounded_le f hC hf)

/-- Uniformly bounded coordinate isomorphisms induce a Banach-space
isomorphism of the c₀ sums (Kislyakov Lemma 1.1). -/
def congrRight (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (heinv : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D) :
    CZeroSum 𝕜 E ≃L[𝕜] CZeroSum 𝕜 F := by
  apply ContinuousLinearEquiv.equivOfInverse
    (mapCLM (fun i => (e i).toContinuousLinearMap) hC he)
    (mapCLM (fun i => (e i).symm.toContinuousLinearMap) hD heinv)
  · intro x
    ext i
    exact (e i).symm_apply_apply (x i)
  · intro x
    ext i
    exact (e i).apply_symm_apply (x i)

@[simp] theorem congrRight_apply (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (heinv : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D) (x : CZeroSum 𝕜 E) (i : I) :
    congrRight e hC hD he heinv x i = e i (x i) := rfl

/-- The isometric case has no auxiliary bounds. -/
def congrRightIsometry (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) :
    CZeroSum 𝕜 E ≃ₗᵢ[𝕜] CZeroSum 𝕜 F where
  toFun x := CZeroSum.mk (fun i => e i (x i)) (by simpa only [LinearIsometryEquiv.norm_map] using x.tendsto_norm)
  invFun x := CZeroSum.mk (fun i => (e i).symm (x i)) (by simpa only [LinearIsometryEquiv.norm_map] using x.tendsto_norm)
  left_inv x := by ext i; exact (e i).symm_apply_apply (x i)
  right_inv x := by ext i; exact (e i).apply_symm_apply (x i)
  map_add' x y := by ext i; exact (e i).map_add _ _
  map_smul' c x := by ext i; exact (e i).map_smul c _
  norm_map' x := by
    apply le_antisymm
    · apply norm_le (norm_nonneg x)
      intro i
      change ‖e i (x i)‖ ≤ ‖x‖
      rw [(e i).norm_map]
      exact x.norm_apply_le_norm i
    · apply norm_le (norm_nonneg _)
      intro i
      have h := (CZeroSum.mk (𝕜 := 𝕜) (fun i => e i (x i))
        (by simpa only [LinearIsometryEquiv.norm_map] using x.tendsto_norm)).norm_apply_le_norm i
      change ‖e i (x i)‖ ≤ _ at h
      rw [(e i).norm_map] at h
      exact h

/-- Normalize an isomorphism without changing its distortion bound. The
zero-dimensional case is included, so this applies to arbitrary families. -/
theorem exists_normalized_equiv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (e : X ≃L[𝕜] Y) {K : ℝ} (hK : 0 ≤ K)
    (he : ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    ∃ d : X ≃L[𝕜] Y, ‖d.toContinuousLinearMap‖ ≤ 1 ∧
      ‖d.symm.toContinuousLinearMap‖ ≤ K := by
  by_cases hzero : ‖e.toContinuousLinearMap‖ = 0
  · have hezero : e.toContinuousLinearMap = 0 := norm_eq_zero.mp hzero
    have hX (x : X) : x = 0 := e.injective (by
      change e.toContinuousLinearMap x = e.toContinuousLinearMap 0
      rw [hezero]
      rfl)
    have hinvzero : e.symm.toContinuousLinearMap = 0 := by ext y; exact hX _
    refine ⟨e, by simpa only [hzero] using (zero_le_one : (0 : ℝ) ≤ 1), ?_⟩
    simpa only [hinvzero, norm_zero] using hK
  · have hpos : 0 < ‖e.toContinuousLinearMap‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    let c : 𝕜 := (‖e.toContinuousLinearMap‖ : ℝ)
    have hc : c ≠ 0 := (RCLike.ofReal_ne_zero (K := 𝕜)).mpr hzero
    have hcnorm : ‖c‖ = ‖e.toContinuousLinearMap‖ := by
      simp only [c, RCLike.norm_ofReal, abs_of_pos hpos]
    let f : X →L[𝕜] Y := c⁻¹ • e.toContinuousLinearMap
    let g : Y →L[𝕜] X := c • e.symm.toContinuousLinearMap
    have hgf (x : X) : g (f x) = x := by
      change c • e.symm (c⁻¹ • e x) = x
      rw [map_smul, e.symm_apply_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hfg (y : Y) : f (g y) = y := by
      change c⁻¹ • e (c • e.symm y) = y
      rw [map_smul, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
    let d := ContinuousLinearEquiv.equivOfInverse f g hgf hfg
    refine ⟨d, ?_, ?_⟩
    · change ‖f‖ ≤ 1
      simp only [f, norm_smul, norm_inv, hcnorm, inv_mul_cancel₀ hzero, le_refl]
    · change ‖g‖ ≤ K
      simpa only [g, norm_smul, hcnorm] using he

/-- Kislyakov Lemma 1.1 with its original uniform distortion-product bound. -/
theorem exists_congrRight_of_distortion {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ i, ∃ e : E i ≃L[𝕜] F i,
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    ∃ e : CZeroSum 𝕜 E ≃L[𝕜] CZeroSum 𝕜 F,
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K := by
  choose e he using he
  choose d hd hdinv using fun i => exists_normalized_equiv (e i) hK (he i)
  let D := congrRight d zero_le_one hK hd hdinv
  have hD : ‖D.toContinuousLinearMap‖ ≤ 1 :=
    norm_mapCLM_le (fun i => (d i).toContinuousLinearMap) zero_le_one hd
  have hDinv : ‖D.symm.toContinuousLinearMap‖ ≤ K :=
    norm_mapCLM_le (fun i => (d i).symm.toContinuousLinearMap) hK hdinv
  refine ⟨D, ?_⟩
  simpa only [one_mul] using mul_le_mul hD hDinv (norm_nonneg _) zero_le_one

end JLMS.CZeroSum
