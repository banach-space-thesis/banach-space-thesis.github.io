import ThesisCommon.Analysis.LpOperators
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Synthesis on an actual dependent lp family from a uniform finite-sum
estimate. The target is complete; no completeness of the fibres is needed. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 ι X : Type*} [RCLike 𝕜] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem summable_lp_family_of_finite_bound (hp : p ≠ ∞)
    (A : ∀ i, E i →L[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ (F : Finset ι) (x : ∀ i, E i),
      ‖∑ i ∈ F, A i (x i)‖ ≤ C * ‖∑ i ∈ F, lp.single p i (x i)‖)
    (x : lp E p) : Summable (fun i => A i (x i)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hpos : 0 < C + 1 := by linarith
  obtain ⟨F, hF⟩ := cauchySeq_finset_iff_vanishing_norm.mp
    (lp.hasSum_single hp x).cauchySeq (ε / (C + 1)) (div_pos hε hpos)
  refine ⟨F, ?_⟩
  intro G hG
  have hsmall := hF G hG
  have hmul : (C + 1) * ‖∑ i ∈ G, lp.single p i (x i)‖ < ε := by
    have h := (lt_div_iff₀ hpos).mp hsmall
    simpa only [mul_comm] using h
  have hbound := hA G x
  nlinarith [norm_nonneg (∑ i ∈ G, lp.single p i (x i))]

theorem norm_tsum_lp_family_le (hp : p ≠ ∞)
    (A : ∀ i, E i →L[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ (F : Finset ι) (x : ∀ i, E i),
      ‖∑ i ∈ F, A i (x i)‖ ≤ C * ‖∑ i ∈ F, lp.single p i (x i)‖)
    (x : lp E p) : ‖∑' i, A i (x i)‖ ≤ C * ‖x‖ := by
  exact le_of_tendsto_of_tendsto
    (summable_lp_family_of_finite_bound hp A hC hA x).hasSum.norm
    (tendsto_const_nhds.mul (lp.hasSum_single hp x).norm)
    (Eventually.of_forall (fun F => hA F x))

def lpFamilySynthesis (hp : p ≠ ∞)
    (A : ∀ i, E i →L[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ (F : Finset ι) (x : ∀ i, E i),
      ‖∑ i ∈ F, A i (x i)‖ ≤ C * ‖∑ i ∈ F, lp.single p i (x i)‖) :
    lp E p →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, A i (x i)
      map_add' := by
        intro x y
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_lp_family_of_finite_bound hp A hC hA x).tsum_add
          (summable_lp_family_of_finite_bound hp A hC hA y)
      map_smul' := by
        intro a x
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact Summable.tsum_const_smul a (summable_lp_family_of_finite_bound hp A hC hA x) }
    C (norm_tsum_lp_family_le hp A hC hA)

theorem norm_lpFamilySynthesis_le (hp : p ≠ ∞)
    (A : ∀ i, E i →L[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ (F : Finset ι) (x : ∀ i, E i),
      ‖∑ i ∈ F, A i (x i)‖ ≤ C * ‖∑ i ∈ F, lp.single p i (x i)‖) :
    ‖lpFamilySynthesis hp A hC hA‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

@[simp] theorem lpFamilySynthesis_single (hp : p ≠ ∞)
    (A : ∀ i, E i →L[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ (F : Finset ι) (x : ∀ i, E i),
      ‖∑ i ∈ F, A i (x i)‖ ≤ C * ‖∑ i ∈ F, lp.single p i (x i)‖)
    (i : ι) (y : E i) : lpFamilySynthesis hp A hC hA (lp.single p i y) = A i y := by
  classical
  change (∑' j, A j ((lp.single p i y : lp E p) j)) = A i y
  rw [tsum_eq_single i]
  · simp
  · intro j hji
    simp [lp.single_apply, hji]

theorem exists_lpFamilySynthesis (hp : p ≠ ∞)
    (A : ∀ i, E i →L[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ (F : Finset ι) (x : ∀ i, E i),
      ‖∑ i ∈ F, A i (x i)‖ ≤ C * ‖∑ i ∈ F, lp.single p i (x i)‖) :
    ∃ T : lp E p →L[𝕜] X, ‖T‖ ≤ C ∧ ∀ i (y : E i), T (lp.single p i y) = A i y :=
  ⟨lpFamilySynthesis hp A hC hA, norm_lpFamilySynthesis_le hp A hC hA,
    lpFamilySynthesis_single hp A hC hA⟩

end ThesisCommon
