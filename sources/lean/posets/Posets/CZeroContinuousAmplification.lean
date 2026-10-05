import Posets.CZeroContinuousAmplificationColumns

/-! Every bounded scalar c₀ operator amplifies to continuous-function-valued
c₀ coordinates. Amplification respects composition, identity and subtraction,
and its operator norm does not increase. -/

noncomputable section
open Filter Topology
namespace Posets
universe u v
variable {𝕜 : Type} [RCLike 𝕜] {I : Type u}
  {K : Type v} [TopologicalSpace K] [CompactSpace K]
set_option synthInstance.maxSize 4096

local instance amplificationMainSumGroup {J : Type*} (X : J → Type*)
    [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace 𝕜 (X j)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 X) := inferInstance
local instance amplificationMainSumSpace {J : Type*} (X : J → Type*)
    [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace 𝕜 (X j)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 X) := inferInstance

def cZeroContinuousAmplification
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)) :=
  cZeroSumColumns (fun j => cZeroContinuousColumn (K := K) (A (JLMS.CZeroSum.single j 1)))
    ‖A‖ (norm_nonneg A) (cZeroContinuous_columns_bound A)

theorem norm_cZeroContinuousAmplification_le
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    ‖cZeroContinuousAmplification (K := K) A‖ ≤ ‖A‖ := norm_cZeroSumColumns_le ..

@[simp] theorem cZeroContinuousAmplification_single
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (j : I) (f : C(K, 𝕜)) (i : I) :
    cZeroContinuousAmplification A (JLMS.CZeroSum.single j f) i =
      A (JLMS.CZeroSum.single j 1) i • f := by
  unfold cZeroContinuousAmplification
  rw [cZeroSumColumns_single]
  rfl

theorem cZeroContinuousAmplification_pointEval
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (x : JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜))) (t : K) :
    cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t (cZeroContinuousAmplification A x) =
      A (cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t x) := by
  have hleft := (cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t).hasSum
    (hasSum_cZeroSumColumns (fun j => cZeroContinuousColumn (K := K)
      (A (JLMS.CZeroSum.single j 1))) ‖A‖ (norm_nonneg A) (cZeroContinuous_columns_bound A) x)
  have hright := A.hasSum (JLMS.CZeroSum.hasSum_single
    (cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t x))
  simp only [cZeroContinuousColumn_pointEval] at hleft
  simp only [cZeroContinuousPointEval_apply] at hright
  have hs (j : I) : A (JLMS.CZeroSum.single j (x j t)) =
      x j t • A (JLMS.CZeroSum.single j 1) := by
    rw [cZeroScalarSingle_smul j (x j t), map_smul]
  simp_rw [hs] at hright
  exact hleft.unique hright

theorem cZeroContinuousAmplification_apply
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (x : JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜))) (i : I) (t : K) :
    cZeroContinuousAmplification A x i t =
      A (cZeroContinuousPointEval (𝕜 := 𝕜) (I := I) t x) i :=
  congrArg (fun z : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) => z i)
    (cZeroContinuousAmplification_pointEval A x t)

@[simp] theorem cZeroContinuousAmplification_id :
    cZeroContinuousAmplification (K := K)
      (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))) =
        ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜))) := by
  apply ContinuousLinearMap.ext
  intro x
  apply JLMS.CZeroSum.ext
  intro i
  apply ContinuousMap.ext
  intro t
  exact cZeroContinuousAmplification_apply _ x i t

theorem cZeroContinuousAmplification_comp
    (A B : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    cZeroContinuousAmplification (K := K) (A.comp B) =
      (cZeroContinuousAmplification (K := K) A).comp (cZeroContinuousAmplification (K := K) B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply JLMS.CZeroSum.ext
  intro i
  apply ContinuousMap.ext
  intro t
  change cZeroContinuousAmplification (A.comp B) x i t =
    cZeroContinuousAmplification A (cZeroContinuousAmplification B x) i t
  rw [cZeroContinuousAmplification_apply, cZeroContinuousAmplification_apply,
    cZeroContinuousAmplification_pointEval]
  rfl

theorem cZeroContinuousAmplification_sub
    (A B : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    cZeroContinuousAmplification (K := K) (A - B) =
      cZeroContinuousAmplification (K := K) A - cZeroContinuousAmplification (K := K) B := by
  apply ContinuousLinearMap.ext
  intro x
  apply JLMS.CZeroSum.ext
  intro i
  apply ContinuousMap.ext
  intro t
  change cZeroContinuousAmplification (A - B) x i t =
    cZeroContinuousAmplification A x i t - cZeroContinuousAmplification B x i t
  simp only [cZeroContinuousAmplification_apply, ContinuousLinearMap.sub_apply, JLMS.CZeroSum.sub_apply]

theorem cZeroSum_clm_ext_columns {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A B : JLMS.CZeroSum 𝕜 E →L[𝕜] F)
    (h : ∀ i x, A (JLMS.CZeroSum.single i x) = B (JLMS.CZeroSum.single i x)) : A = B := by
  apply ContinuousLinearMap.ext
  intro x
  have ha := A.hasSum (JLMS.CZeroSum.hasSum_single x)
  have hb := B.hasSum (JLMS.CZeroSum.hasSum_single x)
  simp_rw [h] at ha
  exact ha.unique hb

theorem eq_cZeroContinuousAmplification_of_columns
    (A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (D : JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜)))
    (h : ∀ i j f, D (JLMS.CZeroSum.single j f) i = A (JLMS.CZeroSum.single j 1) i • f) :
    D = cZeroContinuousAmplification A := by
  apply cZeroSum_clm_ext_columns
  intro j f
  apply JLMS.CZeroSum.ext
  intro i
  rw [h, cZeroContinuousAmplification_single]

end Posets
