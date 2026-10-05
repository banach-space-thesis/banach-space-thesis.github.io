import Posets.CZeroContinuousAmplificationSynthesis

/-! Scalar matrix columns act on continuous-function-valued c₀ coordinates.
The supremum norm estimate is obtained by evaluating at each point of K. -/

noncomputable section
open Filter Topology
namespace Posets
universe u v
variable {𝕜 : Type} [RCLike 𝕜] {I : Type u}
  {K : Type v} [TopologicalSpace K] [CompactSpace K]

local instance amplificationSumGroup {J : Type*} (X : J → Type*)
    [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace 𝕜 (X j)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 X) := inferInstance
local instance amplificationSumSpace {J : Type*} (X : J → Type*)
    [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace 𝕜 (X j)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 X) := inferInstance

def cZeroContinuousPointEval (t : K) :
    JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) :=
  JLMS.CZeroSum.mapCLM (fun _ => ContinuousMap.evalCLM 𝕜 t) zero_le_one
    (fun _ => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
      simpa only [one_mul] using f.norm_coe_le_norm t))

@[simp] theorem cZeroContinuousPointEval_apply (t : K)
    (x : JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜))) (i : I) :
    cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t x i = x i t := rfl

@[simp] theorem cZeroContinuousPointEval_single (t : K) (i : I) (f : C(K, 𝕜)) :
    cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t (JLMS.CZeroSum.single i f) =
      JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => 𝕜) i (f t) := by
  classical
  apply JLMS.CZeroSum.ext
  intro j
  by_cases h : j = i
  · subst j; simp
  · simp only [cZeroContinuousPointEval_apply, JLMS.CZeroSum.single_apply_ne _ _ h,
      ContinuousMap.zero_apply]

def cZeroContinuousColumnValue (a : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) (f : C(K, 𝕜)) :
    JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)) :=
  JLMS.CZeroSum.mk (fun i => a i • f) (by
    simpa only [norm_smul, zero_mul] using a.tendsto_norm.mul_const ‖f‖)

def cZeroContinuousColumn (a : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    C(K, 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)) :=
  ({ toFun := cZeroContinuousColumnValue a
     map_add' f g := by apply JLMS.CZeroSum.ext; intro i; exact smul_add _ _ _
     map_smul' c f := by apply JLMS.CZeroSum.ext; intro i; exact smul_comm _ _ _ } :
      C(K, 𝕜) →ₗ[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜))).mkContinuous ‖a‖ (fun f => by
    apply JLMS.CZeroSum.norm_le (mul_nonneg (norm_nonneg a) (norm_nonneg f))
    intro i
    change ‖a i • f‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (a.norm_apply_le_norm i) (norm_nonneg f))

@[simp] theorem cZeroContinuousColumn_apply (a : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (f : C(K, 𝕜)) (i : I) : cZeroContinuousColumn a f i = a i • f := rfl

theorem cZeroContinuousColumn_pointEval (a : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (f : C(K, 𝕜)) (t : K) :
    cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t (cZeroContinuousColumn a f) = f t • a := by
  apply JLMS.CZeroSum.ext
  intro i
  change a i * f t = f t * a i
  exact mul_comm _ _

theorem cZeroScalarSingle_smul (i : I) (c : 𝕜) :
    JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => 𝕜) i c =
      c • JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => 𝕜) i (1 : 𝕜) := by
  classical
  apply JLMS.CZeroSum.ext
  intro j
  by_cases h : j = i
  · subst j; simp
  · simp only [JLMS.CZeroSum.smul_apply, JLMS.CZeroSum.single_apply_ne _ _ h, smul_zero]

theorem cZeroContinuous_columns_bound
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    CZeroSumFiniteColumnBound (fun j => cZeroContinuousColumn (K := K)
      (A (JLMS.CZeroSum.single j 1))) ‖A‖ := by
  classical
  intro f s M hM hf
  apply JLMS.CZeroSum.norm_le (mul_nonneg (norm_nonneg A) hM)
  intro i
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) hM)).mpr
  intro t
  let v : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) := ∑ j ∈ s, JLMS.CZeroSum.single j (f j t)
  have hv : ‖v‖ ≤ M := by
    apply JLMS.CZeroSum.norm_le hM
    intro j
    simp only [v, JLMS.CZeroSum.sum_apply]
    by_cases hj : j ∈ s
    · rw [Finset.sum_eq_single j]
      · simpa only [JLMS.CZeroSum.single_apply_self] using (f j).norm_coe_le_norm t |>.trans (hf j hj)
      · intro k hk hkj
        exact JLMS.CZeroSum.single_apply_ne k _ hkj.symm
      · exact fun h => (h hj).elim
    · rw [Finset.sum_eq_zero (fun k hk => JLMS.CZeroSum.single_apply_ne
        (𝕜 := 𝕜) (E := fun _ : I => 𝕜) k (f k t)
        (fun he : j = k => hj (he.symm ▸ hk))), norm_zero]
      exact hM
  have he : (∑ j ∈ s, cZeroContinuousColumn (K := K) (A (JLMS.CZeroSum.single j 1)) (f j)) i t = A v i := by
    simp only [JLMS.CZeroSum.sum_apply, ContinuousMap.sum_apply, cZeroContinuousColumn_apply,
      ContinuousMap.smul_apply, smul_eq_mul, v, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hs : A (JLMS.CZeroSum.single j (f j t)) =
        f j t • A (JLMS.CZeroSum.single j 1) := by
      rw [cZeroScalarSingle_smul j (f j t), map_smul]
    rw [hs, JLMS.CZeroSum.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [he]
  exact (A v).norm_apply_le_norm i |>.trans ((A.le_opNorm v).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg A)))

end Posets
