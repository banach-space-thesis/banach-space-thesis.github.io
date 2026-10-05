import JLMS.CZeroSumFinite
import JLMS.CZeroSumSynthesis
import JLMS.CZeroSumOperators
import Mathlib.Topology.ContinuousMap.Compact

/-! Bounded synthesis on the actual dependent c₀ sum. This version retains
an arbitrary operator bound, needed for scalar-operator amplification. -/

noncomputable section
open Filter Topology
namespace Posets
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {E : I → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

def CZeroSumFiniteColumnBound (T : ∀ i, E i →L[𝕜] F) (C : ℝ) : Prop :=
  ∀ (x : ∀ i, E i) (s : Finset I) (M : ℝ), 0 ≤ M →
    (∀ i ∈ s, ‖x i‖ ≤ M) → ‖∑ i ∈ s, T i (x i)‖ ≤ C * M

theorem cZeroSum_columns_summable (T : ∀ i, E i →L[𝕜] F) {C : ℝ}
    (hC : 0 ≤ C) (hT : CZeroSumFiniteColumnBound T C) (x : JLMS.CZeroSum 𝕜 E) :
    Summable (fun i => T i (x i)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  let η := ε / (C + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsmall : C * η < ε := by
    dsimp [η]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  let s : Finset I := (x.finite_norm_ge hη).toFinset
  refine ⟨s, fun t ht => (hT x t η hη.le ?_).trans_lt hsmall⟩
  intro i hi
  apply le_of_not_ge
  intro hge
  have his : i ∈ s := by simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hge
  exact Finset.disjoint_left.mp ht hi his

theorem norm_cZeroSum_columns_tsum_le (T : ∀ i, E i →L[𝕜] F) {C : ℝ}
    (hC : 0 ≤ C) (hT : CZeroSumFiniteColumnBound T C) (x : JLMS.CZeroSum 𝕜 E) :
    ‖∑' i, T i (x i)‖ ≤ C * ‖x‖ := by
  apply le_of_tendsto (cZeroSum_columns_summable T hC hT x).hasSum.norm
  exact Eventually.of_forall (fun s => hT x s ‖x‖ (norm_nonneg x)
    (fun i _ => x.norm_apply_le_norm i))

def cZeroSumColumns (T : ∀ i, E i →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (hT : CZeroSumFiniteColumnBound T C) : JLMS.CZeroSum 𝕜 E →L[𝕜] F :=
  ({ toFun x := ∑' i, T i (x i)
     map_add' x y := by
       simp only [JLMS.CZeroSum.add_apply, map_add]
       exact (cZeroSum_columns_summable T hC hT x).tsum_add
         (cZeroSum_columns_summable T hC hT y)
     map_smul' c x := by
       simp only [JLMS.CZeroSum.smul_apply, map_smul]
       exact (cZeroSum_columns_summable T hC hT x).tsum_const_smul c } :
      JLMS.CZeroSum 𝕜 E →ₗ[𝕜] F).mkContinuous C (norm_cZeroSum_columns_tsum_le T hC hT)

theorem norm_cZeroSumColumns_le (T : ∀ i, E i →L[𝕜] F) (C : ℝ) (hC hT) :
    ‖cZeroSumColumns T C hC hT‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

theorem hasSum_cZeroSumColumns (T : ∀ i, E i →L[𝕜] F) (C : ℝ) (hC hT)
    (x : JLMS.CZeroSum 𝕜 E) :
    HasSum (fun i => T i (x i)) (cZeroSumColumns T C hC hT x) :=
  (cZeroSum_columns_summable T hC hT x).hasSum

theorem cZeroSumColumns_single (T : ∀ i, E i →L[𝕜] F) (C : ℝ) (hC hT)
    (j : I) (x : E j) :
    cZeroSumColumns T C hC hT (JLMS.CZeroSum.single j x) = T j x := by
  classical
  change (∑' i, T i (JLMS.CZeroSum.single j x i)) = _
  rw [tsum_eq_single j]
  · simp
  · intro i hij
    simp only [JLMS.CZeroSum.single_apply_ne _ _ hij, map_zero]

end Posets
