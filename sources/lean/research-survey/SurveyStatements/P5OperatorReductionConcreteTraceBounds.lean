import SurveyStatements.P5OperatorReductionConcreteBirthBounds

/-! Global point and edge estimates follow from the finite birth and
balance conditions, including the first node of every off-diagonal stripe. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ENNReal
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : BanachExponent}
  {T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val}
  {a b : NormalizedBlockTrace 𝕜} {δo δi : ℕ → ℕ → ℝ}
  {ν : ℕ → ℕ → ℕ → ℕ → ℝ} {Fo Fi : LpHaarSequentialSplits}

private theorem traceQuarter_sub_bound {x y : 𝕜} {B : ℝ} (hB : 0 ≤ B)
    (hx : ‖x‖ ≤ B / 4) (hy : ‖y‖ ≤ B / 4) : ‖x - y‖ ≤ B := by
  apply (norm_sub_le x y).trans
  have h := add_le_add hx hy
  linarith only [h, hB]

private theorem traceBudget_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    0 ≤ lpHaarTraceErrorBudget δ j := mul_nonneg hδ (pow_nonneg (by norm_num) _)

private theorem traceBudget_quarter_le {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    lpHaarTraceErrorBudget δ j / 4 ≤ δ := by
  have h := (lpHaarTraceErrorBudget_le hδ j).trans
    (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hδ)
  have hn := traceBudget_nonneg hδ j
  linarith only [h, hn, hδ]

theorem concrete_outer_trace_bounds (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    (ha : NormalizedTraceExtensional a) {J L : ℕ} (hJL : J ≠ L)
    (hδ : 0 ≤ δo J L) :
    (∀ i, ‖concreteMixedEntry p T (Fo.node i) (Fi.node J) (Fo.node i) (Fi.node L) -
      a (Fi.node J, Fi.node L) (Fo.node i).parent‖ ≤
        lpHaarTraceErrorBudget (δo J L) i) ∧
    (∀ i, i ≠ 0 →
      ‖a (Fi.node J, Fi.node L) (Fo.node i).parent -
        a (Fi.node J, Fi.node L) (Fo.node ((i - 1) / 2)).parent‖ ≤
          lpHaarTraceErrorBudget (δo J L) ((i - 1) / 2)) ∧
    ‖a (Fi.node J, Fi.node L) (Fo.node 0).parent‖ ≤ δo J L := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < max J L
    · obtain ⟨hg, ht, _⟩ := concrete_outer_stripe_birth_bounds h hJL hi
      exact traceQuarter_sub_bound (traceBudget_nonneg hδ i) hg ht
    · let j : Fin (i + 1) := ⟨J, by omega⟩
      let l : Fin (i + 1) := ⟨L, by omega⟩
      exact (h.outer i).point j l (fun he => hJL (congrArg Fin.val he))
  · intro i hi
    rw [normalizedTrace_parent a ha (Fi.node J, Fi.node L) Fo i hi]
    by_cases hk : (i - 1) / 2 < max J L
    · obtain ⟨_, ht, hc⟩ := concrete_outer_stripe_birth_bounds h hJL hk
      exact traceQuarter_sub_bound (traceBudget_nonneg hδ _) (hc _) ht
    · let k := (i - 1) / 2
      let j : Fin (k + 1) := ⟨J, by dsimp [k]; omega⟩
      let l : Fin (k + 1) := ⟨L, by dsimp [k]; omega⟩
      exact (h.outer k).balance j l (fun he => hJL (congrArg Fin.val he)) _
  · have hzero : 0 < max J L := by omega
    exact (concrete_outer_stripe_birth_bounds h hJL hzero).2.1.trans
      (traceBudget_quarter_le hδ 0)

theorem concrete_inner_trace_bounds (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    (hb : NormalizedTraceExtensional b) {I K : ℕ} (hIK : I ≠ K)
    (hδ : 0 ≤ δi I K) :
    (∀ j, ‖concreteMixedEntry p T (Fo.node I) (Fi.node j) (Fo.node K) (Fi.node j) -
      b (Fo.node I, Fo.node K) (Fi.node j).parent‖ ≤
        lpHaarTraceErrorBudget (δi I K) j) ∧
    (∀ j, j ≠ 0 →
      ‖b (Fo.node I, Fo.node K) (Fi.node j).parent -
        b (Fo.node I, Fo.node K) (Fi.node ((j - 1) / 2)).parent‖ ≤
          lpHaarTraceErrorBudget (δi I K) ((j - 1) / 2)) ∧
    ‖b (Fo.node I, Fo.node K) (Fi.node 0).parent‖ ≤ δi I K := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ≤ max I K
    · obtain ⟨hg, ht, _⟩ := concrete_inner_stripe_birth_bounds h hIK hj
      exact traceQuarter_sub_bound (traceBudget_nonneg hδ j) hg ht
    · let i : Fin j := ⟨I, by omega⟩
      let k : Fin j := ⟨K, by omega⟩
      exact (h.inner j).point i k (fun he => hIK (congrArg Fin.val he))
  · intro j hj
    rw [normalizedTrace_parent b hb (Fo.node I, Fo.node K) Fi j hj]
    by_cases hk : (j - 1) / 2 ≤ max I K
    · obtain ⟨_, ht, hc⟩ := concrete_inner_stripe_birth_bounds h hIK hk
      exact traceQuarter_sub_bound (traceBudget_nonneg hδ _) (hc _) ht
    · let n := (j - 1) / 2
      let i : Fin n := ⟨I, by dsimp [n]; omega⟩
      let k : Fin n := ⟨K, by dsimp [n]; omega⟩
      exact (h.inner n).balance i k (fun he => hIK (congrArg Fin.val he)) _
  · exact (concrete_inner_stripe_birth_bounds h hIK (Nat.zero_le _)).2.1.trans
      (traceBudget_quarter_le hδ 0)

theorem exists_concrete_outer_stripe_multiplier (hp : p.val ≠ ∞)
    (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    (ha : NormalizedTraceExtensional a) {J L : ℕ} (hJL : J ≠ L)
    (hδ : 0 ≤ δo J L) :
    ∃ Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ‖Q‖ ≤ 14 * δo J L ∧
      (∀ n (k : Fin (2 ^ n)), Q (lpHaarDyadic 𝕜 p n k) =
        concreteMixedEntry p T (Fo.node (lpHaarHeapIndex n k)) (Fi.node J)
          (Fo.node (lpHaarHeapIndex n k)) (Fi.node L) • lpHaarDyadic 𝕜 p n k) ∧
      Q (MeasureTheory.Lp.const p.val (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
        (1 : 𝕜)) = 0 := by
  obtain ⟨hg, ht, hr⟩ := concrete_outer_trace_bounds h ha hJL hδ
  exact exists_small_geometric_trace_multiplier p hp _ _ hδ hg ht hr

theorem exists_concrete_inner_stripe_multiplier
    (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    (hb : NormalizedTraceExtensional b) {I K : ℕ} (hIK : I ≠ K)
    (hδ : 0 ≤ δi I K) :
    ∃ Q : IntervalLp 𝕜 concreteInnerExponent →L[𝕜] IntervalLp 𝕜 concreteInnerExponent,
      ‖Q‖ ≤ 14 * δi I K ∧
      (∀ n (k : Fin (2 ^ n)), Q (lpHaarDyadic 𝕜 concreteInnerExponent n k) =
        concreteMixedEntry p T (Fo.node I) (Fi.node (lpHaarHeapIndex n k))
          (Fo.node K) (Fi.node (lpHaarHeapIndex n k)) •
            lpHaarDyadic 𝕜 concreteInnerExponent n k) ∧
      Q (MeasureTheory.Lp.const 1 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
        (1 : 𝕜)) = 0 := by
  obtain ⟨hg, ht, hr⟩ := concrete_inner_trace_bounds h hb hIK hδ
  exact exists_small_geometric_trace_multiplier concreteInnerExponent (by simp) _ _
    hδ hg ht hr

end SurveyStatements.P5OperatorReduction
