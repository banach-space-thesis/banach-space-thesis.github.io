import SurveyStatements.P5OperatorReductionConcreteErrorLists

/-! The actual outer half-step finite error list, using the inner history
that already contains the newly selected inner split. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev OuterBirthIndex (n : ℕ) := BornDistinctPair n × Fin (n + 1)
abbrev OuterFiniteErrorIndex (n : ℕ) :=
  PastDistinctPair (n + 1) ⊕ ((PastDistinctPair (n + 1) × Bool) ⊕
    (OuterBirthIndex n ⊕ (OuterBirthIndex n ⊕
      ((OuterBirthIndex n × Bool) ⊕ (BornDistinctPair n × PastDistinctPair (n + 1))))))

def concreteOuterError (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) {n : ℕ}
    (ho : Fin n → LpHaarFiniteSplit) (hi : Fin (n + 1) → LpHaarFiniteSplit) :
    OuterFiniteErrorIndex n → LpHaarFiniteSplit → 𝕜 :=
  Sum.elim
    (fun v S => concreteMixedEntry p T S (hi v.val.1) S (hi v.val.2) -
      a (hi v.val.1, hi v.val.2) S.parent)
    (Sum.elim
      (fun v S => a (hi v.1.val.1, hi v.1.val.2) (S.child v.2) -
        a (hi v.1.val.1, hi v.1.val.2) S.parent)
      (Sum.elim
        (fun v S => concreteMixedEntry p T (currentSplitHistory ho S v.1.val.1)
          (hi v.2) (currentSplitHistory ho S v.1.val.2) (hi v.2))
        (Sum.elim
          (fun v S => b (currentSplitHistory ho S v.1.val.1,
            currentSplitHistory ho S v.1.val.2) (hi v.2).parent)
          (Sum.elim
            (fun v S => b (currentSplitHistory ho S v.1.1.val.1,
              currentSplitHistory ho S v.1.1.val.2) ((hi v.1.2).child v.2))
            (fun v S => concreteMixedEntry p T (currentSplitHistory ho S v.1.val.1)
              (hi v.2.val.1) (currentSplitHistory ho S v.1.val.2)
              (hi v.2.val.2))))))

def concreteOuterTolerance (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ) (n : ℕ) : OuterFiniteErrorIndex n → ℝ :=
  Sum.elim
    (fun v => lpHaarTraceErrorBudget (δo v.val.1.val v.val.2.val) n)
    (Sum.elim
      (fun v => lpHaarTraceErrorBudget (δo v.1.val.1.val v.1.val.2.val) n)
      (Sum.elim
        (fun v => lpHaarTraceErrorBudget (δi v.1.val.1.val v.1.val.2.val) v.2.val / 4)
        (Sum.elim
          (fun v => lpHaarTraceErrorBudget (δi v.1.val.1.val v.1.val.2.val) v.2.val / 4)
          (Sum.elim
            (fun v => lpHaarTraceErrorBudget
              (δi v.1.1.val.1.val v.1.1.val.2.val) v.1.2.val / 4)
            (fun v => ν v.1.val.1.val v.2.val.1.val v.1.val.2.val v.2.val.2.val)))))

theorem concreteOuterTolerance_pos (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (ho : ∀ i j, 0 < δo i j) (hi : ∀ i j, 0 < δi i j)
    (hv : ∀ i j k l, 0 < ν i j k l) (n : ℕ) :
    ∀ v, 0 < concreteOuterTolerance δo δi ν n v := by
  intro v
  rcases v with v | v
  · exact concreteTraceErrorBudget_pos (ho _ _) _
  rcases v with v | v
  · exact concreteTraceErrorBudget_pos (ho _ _) _
  rcases v with v | v
  · exact div_pos (concreteTraceErrorBudget_pos (hi _ _) _) (by norm_num)
  rcases v with v | v
  · exact div_pos (concreteTraceErrorBudget_pos (hi _ _) _) (by norm_num)
  rcases v with v | v
  · exact div_pos (concreteTraceErrorBudget_pos (hi _ _) _) (by norm_num)
  · exact hv _ _ _ _

theorem concreteOuterStep_of_finite_errors (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ) {n : ℕ}
    (ho : Fin n → LpHaarFiniteSplit) (hi : Fin (n + 1) → LpHaarFiniteSplit)
    (S : LpHaarFiniteSplit)
    (h : ∀ v, ‖concreteOuterError p T a b ho hi v S‖ ≤
      concreteOuterTolerance δo δi ν n v) :
    ConcreteOuterStep p T a b δo δi ν n ho hi S := by
  constructor
  · intro J L hJL
    exact h (Sum.inl ⟨(J, L), hJL⟩)
  · intro J L hJL s
    exact h (Sum.inr (Sum.inl (⟨(J, L), hJL⟩, s)))
  · intro I K hIK hborn j
    exact h (Sum.inr (Sum.inr (Sum.inl (⟨(I, K), hIK, hborn⟩, j))))
  · intro I K hIK hborn j
    exact h (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨(I, K), hIK, hborn⟩, j)))))
  · intro I K hIK hborn j s
    exact h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      ((⟨(I, K), hIK, hborn⟩, j), s))))))
  · intro I K hIK hborn J L hJL
    exact h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (⟨(I, K), hIK, hborn⟩, ⟨(J, L), hJL⟩))))))

theorem exists_concrete_outer_step_of_actual_moments (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hδo : ∀ i j, 0 < δo i j) (hδi : ∀ i j, 0 < δi i j)
    (hν : ∀ i j k l, 0 < ν i j k l) (n : ℕ)
    (ho : Fin n → LpHaarFiniteSplit) (hi : Fin (n + 1) → LpHaarFiniteSplit)
    (P : LpHaarFiniteParent) (r : ℕ → ℕ) (hr : StrictMono r) (N : ℕ)
    (hlim : ∀ v, Tendsto (fun k => mean (fun θ =>
      ‖concreteOuterError p T a b ho hi v (candidateRefinedSplit P (r k) θ)‖ ^ 2))
      atTop (𝓝 0)) :
    ∃ S : LpHaarFiniteSplit, ∃ k : ℕ, S.level = r k ∧ N ≤ S.level ∧
      S.parent.set = P.set ∧ ConcreteOuterStep p T a b δo δi ν n ho hi S := by
  obtain ⟨S, k, hk, hN, hparent, herrors⟩ :=
    exists_candidate_split_of_actual_error_moment_limits P r hr
      (concreteOuterError p T a b ho hi) (concreteOuterTolerance δo δi ν n)
      (concreteOuterTolerance_pos δo δi ν hδo hδi hν n) N hlim
  exact ⟨S, k, hk, hN, hparent,
    concreteOuterStep_of_finite_errors p T a b δo δi ν ho hi S (fun v => (herrors v).le)⟩

end SurveyStatements.P5OperatorReduction
