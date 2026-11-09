import ThesisCommon.Analysis.CZeroSingles
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Build a bounded operator on c0 from a uniform finite-block supremum
estimate. The defining series is unconditionally convergent; absolute
summability of the input coordinates is neither required nor asserted. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

def CZeroFiniteColumnBound (F : ℕ → X →L[𝕜] Y) (C : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → X) (b : ℝ), 0 ≤ b →
    (∀ i ∈ s, ‖x i‖ ≤ b) → ‖∑ i ∈ s, F i (x i)‖ ≤ C*b

theorem cZero_columns_summable (F : ℕ → X →L[𝕜] Y) {C : ℝ}
    (hC : 0 ≤ C) (hF : CZeroFiniteColumnBound F C) (x : CZeroSum X) :
    Summable (fun i => F i (x i)) := by
  classical
  apply summable_iff_vanishing_norm.2
  intro ε hε
  let η := ε/(C+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsmall : C*η < ε := by
    dsimp [η]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C+1)]
    nlinarith
  have hx : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero] using x.zero_at_infty'.norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hx).2 η hη)
  refine ⟨Finset.range N, ?_⟩
  intro s hs
  apply (hF s x η hη.le ?_).trans_lt hsmall
  intro i hi
  apply (hN i ?_).le
  by_contra h
  exact Finset.disjoint_left.1 hs hi (Finset.mem_range.mpr (by omega))

theorem norm_cZero_columns_tsum_le (F : ℕ → X →L[𝕜] Y) {C : ℝ}
    (hC : 0 ≤ C) (hF : CZeroFiniteColumnBound F C) (x : CZeroSum X) :
    ‖∑' i, F i (x i)‖ ≤ C*‖x‖ := by
  apply le_of_tendsto (cZero_columns_summable F hC hF x).hasSum.norm
  exact Eventually.of_forall (fun s => hF s x ‖x‖ (norm_nonneg x)
    (fun i _ => BoundedContinuousFunction.norm_coe_le_norm x.toBCF i))

def cZeroColumns (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C)
    (hF : CZeroFiniteColumnBound F C) : CZeroSum X →L[𝕜] Y :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, F i (x i)
      map_add' := by
        intro x y
        change (∑' i, F i (x i+y i)) = _
        simp only [map_add]
        exact (cZero_columns_summable F hC hF x).tsum_add (cZero_columns_summable F hC hF y)
      map_smul' := by
        intro a x
        change (∑' i, F i (a • x i)) = _
        simp only [map_smul]
        exact (cZero_columns_summable F hC hF x).tsum_const_smul a }
    C (norm_cZero_columns_tsum_le F hC hF)

theorem norm_cZeroColumns_le (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC hF) :
    ‖cZeroColumns F C hC hF‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

theorem cZeroColumns_single (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC hF) (j : ℕ) (x : X) :
    cZeroColumns F C hC hF (cZeroSingle j x) = F j x := by
  change (∑' i, F i (cZeroSingle j x i)) = _
  rw [tsum_eq_single j]
  · simp
  · intro i hij
    simp [hij]

end ThesisCommon
