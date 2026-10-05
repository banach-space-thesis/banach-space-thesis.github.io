import ThesisCommon.Analysis.SequenceSumEquivs
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! Continuous functions on the convergent-sequence compactum are the sum
of their limit and an actual null sequence. The resulting bounded linear
isomorphism is proved for arbitrary normed real or complex vector values. -/

noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def onePointNullPart (f : C(OnePoint ℕ, X)) : CZeroSum X where
  toFun n := f (n : OnePoint ℕ) - f OnePoint.infty
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    have h := (OnePoint.continuous_iff_from_discrete f).mp f.continuous
    simpa only [sub_self, cocompact_eq_cofinite] using
      h.sub (tendsto_const_nhds (x := f OnePoint.infty))

@[simp] theorem onePointNullPart_apply (f : C(OnePoint ℕ, X)) (n : ℕ) :
    onePointNullPart f n = f (n : OnePoint ℕ) - f OnePoint.infty := rfl

theorem norm_onePointNullPart_le (f : C(OnePoint ℕ, X)) :
    ‖onePointNullPart f‖ ≤ 2 * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ 2 * ‖f‖)).mpr
  intro n
  change ‖f (n : OnePoint ℕ) - f OnePoint.infty‖ ≤ 2 * ‖f‖
  calc
    _ ≤ ‖f (n : OnePoint ℕ)‖ + ‖f OnePoint.infty‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
    _ = 2 * ‖f‖ := (two_mul _).symm

def onePointNullPartCLM : C(OnePoint ℕ, X) →L[𝕜] CZeroSum X :=
  LinearMap.mkContinuous
    { toFun := onePointNullPart
      map_add' := by
        intro f g
        ext n
        change (f (n : OnePoint ℕ) + g (n : OnePoint ℕ)) -
          (f OnePoint.infty + g OnePoint.infty) =
          (f (n : OnePoint ℕ) - f OnePoint.infty) +
            (g (n : OnePoint ℕ) - g OnePoint.infty)
        abel
      map_smul' := by
        intro a f
        ext n
        change a • f (n : OnePoint ℕ) - a • f OnePoint.infty =
          a • (f (n : OnePoint ℕ) - f OnePoint.infty)
        exact (smul_sub _ _ _).symm }
    2 norm_onePointNullPart_le

def onePointAssembleValue (z : X × CZeroSum X) : C(OnePoint ℕ, X) :=
  OnePoint.continuousMapMkDiscrete (fun n => z.1 + z.2 n) z.1 (by
    simpa only [add_zero, cocompact_eq_cofinite] using
      tendsto_const_nhds.add z.2.zero_at_infty')

@[simp] theorem onePointAssembleValue_infty (z : X × CZeroSum X) :
    onePointAssembleValue z OnePoint.infty = z.1 := rfl

@[simp] theorem onePointAssembleValue_some (z : X × CZeroSum X) (n : ℕ) :
    onePointAssembleValue z (n : OnePoint ℕ) = z.1 + z.2 n := rfl

theorem norm_onePointAssembleValue_le (z : X × CZeroSum X) :
    ‖onePointAssembleValue z‖ ≤ 2 * ‖z‖ := by
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 2 * ‖z‖)).mpr
  intro x
  refine OnePoint.rec ?_ (fun n => ?_) x
  · change ‖z.1‖ ≤ 2 * ‖z‖
    exact (norm_fst_le z).trans (by nlinarith [norm_nonneg z])
  · change ‖z.1 + z.2 n‖ ≤ 2 * ‖z‖
    have hsecond := BoundedContinuousFunction.norm_coe_le_norm z.2.toBCF n
    calc
      _ ≤ ‖z.1‖ + ‖z.2 n‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ‖z‖ := add_le_add (norm_fst_le z) (hsecond.trans (norm_snd_le z))
      _ = 2 * ‖z‖ := (two_mul _).symm

def onePointAssemble : X × CZeroSum X →L[𝕜] C(OnePoint ℕ, X) :=
  LinearMap.mkContinuous
    { toFun := onePointAssembleValue
      map_add' := by
        intro z w
        ext x
        refine OnePoint.rec ?_ (fun n => ?_) x
        · rfl
        · change (z.1 + w.1) + (z.2 n + w.2 n) =
            (z.1 + z.2 n) + (w.1 + w.2 n)
          abel
      map_smul' := by
        intro a z
        ext x
        refine OnePoint.rec ?_ (fun n => ?_) x
        · rfl
        · change a • z.1 + a • z.2 n = a • (z.1 + z.2 n)
          exact (smul_add _ _ _).symm }
    2 norm_onePointAssembleValue_le

def onePointContinuousProductEquiv : C(OnePoint ℕ, X) ≃L[𝕜] X × CZeroSum X :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousMap.evalCLM 𝕜 OnePoint.infty).prod onePointNullPartCLM)
    onePointAssemble
    (by
      intro f
      ext x
      refine OnePoint.rec ?_ (fun n => ?_) x
      · rfl
      · change f OnePoint.infty + (f (n : OnePoint ℕ) - f OnePoint.infty) = _
        abel)
    (by
      intro z
      apply Prod.ext
      · rfl
      · ext n
        change (z.1 + z.2 n) - z.1 = z.2 n
        abel)

def onePointContinuousCZeroEquiv : C(OnePoint ℕ, X) ≃L[𝕜] CZeroSum X :=
  onePointContinuousProductEquiv.trans cZeroHeadTailEquiv.symm

end ThesisCommon
