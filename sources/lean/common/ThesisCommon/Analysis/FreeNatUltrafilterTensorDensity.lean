import ThesisCommon.Analysis.FreeNatUltrafilterApproximation
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Piecewise

/-! Actual clopen masks and tensor tests determine bounded operators on
vector-valued C(ω*). Uniform locally constant approximation supplies the
all-vector conclusion; no finite-dimensionality of the coefficient is used. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 K X Y : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def continuousFunctionMask (A : Set K) (hA : IsClopen A) : C(K, X) →L[𝕜] C(K, X) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨A.piecewise f 0, continuous_piecewise (by
        intro U hU
        rw [hA.isOpen.frontier_eq, hA.isClosed.closure_eq, Set.diff_self] at hU
        exact False.elim hU) f.continuous.continuousOn continuous_const.continuousOn⟩
      map_add' := fun f g => by ext U; by_cases hU : U ∈ A <;> simp [hU]
      map_smul' := fun c f => by ext U; by_cases hU : U ∈ A <;> simp [hU] }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro U
      change ‖A.piecewise (fun V => f V) (fun _ => 0) U‖ ≤ ‖f‖
      by_cases hU : U ∈ A
      · simpa only [Set.piecewise_eq_of_mem _ _ _ hU] using f.norm_coe_le_norm U
      · simp only [Set.piecewise_eq_of_notMem _ _ _ hU, norm_zero]
        exact norm_nonneg f)

@[simp] theorem continuousFunctionMask_apply (A : Set K) (hA : IsClopen A)
    (f : C(K, X)) (U : K) : continuousFunctionMask (𝕜 := 𝕜) A hA f U =
      if U ∈ A then f U else 0 := rfl

theorem norm_continuousFunctionMask_le (A : Set K) (hA : IsClopen A) :
    ‖continuousFunctionMask (𝕜 := 𝕜) (X := X) A hA‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def continuousFunctionTensor (x : X) : C(K, 𝕜) →L[𝕜] C(K, X) :=
  ContinuousLinearMap.compLeftContinuous 𝕜 K ((ContinuousLinearMap.id 𝕜 𝕜).smulRight x)

omit [CompactSpace K] in
@[simp] theorem continuousFunctionTensor_apply (x : X) (f : C(K, 𝕜)) (U : K) :
    continuousFunctionTensor x f U = f U • x := rfl

theorem norm_continuousFunctionTensor_le (x : X) :
    ‖continuousFunctionTensor (𝕜 := 𝕜) (K := K) x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg x) (norm_nonneg f))).mpr
  intro U
  change ‖f U • x‖ ≤ ‖x‖ * ‖f‖
  rw [norm_smul, mul_comm ‖x‖]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm U) (norm_nonneg x)

theorem freeNatUltrafilter_operator_zero_of_tensors
    (T : C(FreeNatUltrafilter, X) →L[𝕜] Y)
    (hT : ∀ (x : X) (f : C(FreeNatUltrafilter, 𝕜)),
      T (continuousFunctionTensor x f) = 0) : T = 0 := by
  classical
  have hsimple (g : C(FreeNatUltrafilter, X)) (hg : IsLocallyConstant g) : T g = 0 := by
    let S := hg.range_finite.toFinset
    let h (x : X) : C(FreeNatUltrafilter, 𝕜) :=
      continuousFunctionMask (𝕜 := 𝕜) {U | g U = x} (hg.isClopen_fiber x)
        (ContinuousMap.const _ 1)
    have he : g = ∑ x ∈ S, continuousFunctionTensor x (h x) := by
      ext U
      simp only [ContinuousMap.sum_apply, continuousFunctionTensor_apply,
        h, continuousFunctionMask_apply, ContinuousMap.const_apply]
      rw [Finset.sum_eq_single (g U)]
      · simp
      · intro x hx hne
        simp [Ne.symm hne]
      · intro hn
        exact False.elim (hn (by simpa only [S, Set.Finite.mem_toFinset] using
          (Set.mem_range_self U : g U ∈ Set.range g)))
    rw [he, map_sum]
    exact Finset.sum_eq_zero (fun x _ => hT x (h x))
  apply ContinuousLinearMap.ext
  intro f
  have hclosed : IsClosed {g : C(FreeNatUltrafilter, X) | T g = 0} :=
    isClosed_eq T.continuous continuous_const
  change f ∈ {g : C(FreeNatUltrafilter, X) | T g = 0}
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := freeNatUltrafilter_exists_locallyConstant_approximation f
    (by positivity : 0 < ε / 2)
  exact ⟨g, hsimple g hg, by rw [dist_eq_norm]; linarith⟩

theorem freeNatUltrafilter_operator_ext_of_tensors
    (S T : C(FreeNatUltrafilter, X) →L[𝕜] Y)
    (h : ∀ (x : X) (f : C(FreeNatUltrafilter, 𝕜)),
      S (continuousFunctionTensor x f) = T (continuousFunctionTensor x f)) : S = T := by
  apply sub_eq_zero.mp
  apply freeNatUltrafilter_operator_zero_of_tensors
  intro x f
  change S (continuousFunctionTensor x f) - T (continuousFunctionTensor x f) = 0
  exact sub_eq_zero.mpr (h x f)

end ThesisCommon
