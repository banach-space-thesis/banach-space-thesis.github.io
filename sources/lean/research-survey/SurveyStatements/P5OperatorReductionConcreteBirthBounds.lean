import SurveyStatements.P5OperatorReductionConcreteTrees

/-! Bounds imposed exactly when a distinct block pair first exists. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : BanachExponent}
  {T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val}
  {a b : NormalizedBlockTrace 𝕜} {δo δi : ℕ → ℕ → ℝ}
  {ν : ℕ → ℕ → ℕ → ℕ → ℝ} {Fo Fi : LpHaarSequentialSplits}

theorem concrete_outer_stripe_birth_bounds
    (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    {J L i : ℕ} (hJL : J ≠ L) (hi : i < max J L) :
    ‖concreteMixedEntry p T (Fo.node i) (Fi.node J) (Fo.node i) (Fi.node L)‖ ≤
        lpHaarTraceErrorBudget (δo J L) i / 4 ∧
    ‖a (Fi.node J, Fi.node L) (Fo.node i).parent‖ ≤
        lpHaarTraceErrorBudget (δo J L) i / 4 ∧
    ∀ s : Bool, ‖a (Fi.node J, Fi.node L) ((Fo.node i).child s)‖ ≤
        lpHaarTraceErrorBudget (δo J L) i / 4 := by
  let n := max J L
  let j : Fin (n + 1) := ⟨J, by dsimp [n]; omega⟩
  let l : Fin (n + 1) := ⟨L, by dsimp [n]; omega⟩
  let i' : Fin n := ⟨i, hi⟩
  have hjl : j ≠ l := fun he => hJL (congrArg Fin.val he)
  have hfresh : j.val = n ∨ l.val = n := by dsimp [j, l, n]; omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [currentSplitHistory_sequence] using
      (h.inner n).birth_entries j l hjl hfresh i'
  · simpa only [currentSplitHistory_sequence] using
      (h.inner n).birth_parents j l hjl hfresh i'
  · intro s
    simpa only [currentSplitHistory_sequence] using
      (h.inner n).birth_children j l hjl hfresh i' s

theorem concrete_inner_stripe_birth_bounds
    (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    {I K j : ℕ} (hIK : I ≠ K) (hj : j ≤ max I K) :
    ‖concreteMixedEntry p T (Fo.node I) (Fi.node j) (Fo.node K) (Fi.node j)‖ ≤
        lpHaarTraceErrorBudget (δi I K) j / 4 ∧
    ‖b (Fo.node I, Fo.node K) (Fi.node j).parent‖ ≤
        lpHaarTraceErrorBudget (δi I K) j / 4 ∧
    ∀ s : Bool, ‖b (Fo.node I, Fo.node K) ((Fi.node j).child s)‖ ≤
        lpHaarTraceErrorBudget (δi I K) j / 4 := by
  let n := max I K
  let i : Fin (n + 1) := ⟨I, by dsimp [n]; omega⟩
  let k : Fin (n + 1) := ⟨K, by dsimp [n]; omega⟩
  let j' : Fin (n + 1) := ⟨j, by dsimp [n]; omega⟩
  have hik : i ≠ k := fun he => hIK (congrArg Fin.val he)
  have hfresh : i.val = n ∨ k.val = n := by dsimp [i, k, n]; omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [currentSplitHistory_sequence] using
      (h.outer n).birth_entries i k hik hfresh j'
  · simpa only [currentSplitHistory_sequence] using
      (h.outer n).birth_parents i k hik hfresh j'
  · intro s
    simpa only [currentSplitHistory_sequence] using
      (h.outer n).birth_children i k hik hfresh j' s

theorem concrete_mixed_entry_bound
    (h : ConcreteTreeSteps p T a b δo δi ν Fo Fi)
    {I J K L : ℕ} (hIK : I ≠ K) (hJL : J ≠ L) :
    ‖concreteMixedEntry p T (Fo.node I) (Fi.node J) (Fo.node K) (Fi.node L)‖ ≤
      ν I J K L := by
  by_cases horder : max I K < max J L
  · let n := max J L
    let i : Fin n := ⟨I, by dsimp [n]; omega⟩
    let k : Fin n := ⟨K, by dsimp [n]; omega⟩
    let j : Fin (n + 1) := ⟨J, by dsimp [n]; omega⟩
    let l : Fin (n + 1) := ⟨L, by dsimp [n]; omega⟩
    have hik : i ≠ k := fun he => hIK (congrArg Fin.val he)
    have hjl : j ≠ l := fun he => hJL (congrArg Fin.val he)
    have hfresh : j.val = n ∨ l.val = n := by dsimp [j, l, n]; omega
    simpa only [currentSplitHistory_sequence] using (h.inner n).mixed i k hik j l hjl hfresh
  · let n := max I K
    let i : Fin (n + 1) := ⟨I, by dsimp [n]; omega⟩
    let k : Fin (n + 1) := ⟨K, by dsimp [n]; omega⟩
    let j : Fin (n + 1) := ⟨J, by dsimp [n]; omega⟩
    let l : Fin (n + 1) := ⟨L, by dsimp [n]; omega⟩
    have hik : i ≠ k := fun he => hIK (congrArg Fin.val he)
    have hjl : j ≠ l := fun he => hJL (congrArg Fin.val he)
    have hfresh : i.val = n ∨ k.val = n := by dsimp [i, k, n]; omega
    simpa only [currentSplitHistory_sequence] using (h.outer n).mixed i k hik hfresh j l hjl

end SurveyStatements.P5OperatorReduction
