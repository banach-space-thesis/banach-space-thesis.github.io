import SurveyStatements.P5OperatorReductionConcreteSteps
import SurveyStatements.P5OperatorReductionCandidateSplits

/-! The six concrete finite requirements form one finite scalar error
list. Selection is applied to the actual operator entries and trace values;
the analytic moment limits are discharged in the subsequent modules. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev PastDistinctPair (n : ℕ) := {v : Fin n × Fin n // v.1 ≠ v.2}
abbrev BornDistinctPair (n : ℕ) :=
  {v : Fin (n + 1) × Fin (n + 1) // v.1 ≠ v.2 ∧ (v.1.val = n ∨ v.2.val = n)}
abbrev InnerBirthIndex (n : ℕ) := BornDistinctPair n × Fin n
abbrev InnerFiniteErrorIndex (n : ℕ) :=
  PastDistinctPair n ⊕ ((PastDistinctPair n × Bool) ⊕
    (InnerBirthIndex n ⊕ (InnerBirthIndex n ⊕
      ((InnerBirthIndex n × Bool) ⊕ (PastDistinctPair n × BornDistinctPair n)))))

def concreteInnerError (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) {n : ℕ}
    (ho hi : Fin n → LpHaarFiniteSplit) :
    InnerFiniteErrorIndex n → LpHaarFiniteSplit → 𝕜 :=
  Sum.elim
    (fun v S => concreteMixedEntry p T (ho v.val.1) S (ho v.val.2) S -
      b (ho v.val.1, ho v.val.2) S.parent)
    (Sum.elim
      (fun v S => b (ho v.1.val.1, ho v.1.val.2) (S.child v.2) -
        b (ho v.1.val.1, ho v.1.val.2) S.parent)
      (Sum.elim
        (fun v S => concreteMixedEntry p T (ho v.2)
          (currentSplitHistory hi S v.1.val.1) (ho v.2)
          (currentSplitHistory hi S v.1.val.2))
        (Sum.elim
          (fun v S => a (currentSplitHistory hi S v.1.val.1,
            currentSplitHistory hi S v.1.val.2) (ho v.2).parent)
          (Sum.elim
            (fun v S => a (currentSplitHistory hi S v.1.1.val.1,
              currentSplitHistory hi S v.1.1.val.2) ((ho v.1.2).child v.2))
            (fun v S => concreteMixedEntry p T (ho v.1.val.1)
              (currentSplitHistory hi S v.2.val.1) (ho v.1.val.2)
              (currentSplitHistory hi S v.2.val.2))))))

def concreteInnerTolerance (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ) (n : ℕ) : InnerFiniteErrorIndex n → ℝ :=
  Sum.elim
    (fun v => lpHaarTraceErrorBudget (δi v.val.1.val v.val.2.val) n)
    (Sum.elim
      (fun v => lpHaarTraceErrorBudget (δi v.1.val.1.val v.1.val.2.val) n)
      (Sum.elim
        (fun v => lpHaarTraceErrorBudget (δo v.1.val.1.val v.1.val.2.val) v.2.val / 4)
        (Sum.elim
          (fun v => lpHaarTraceErrorBudget (δo v.1.val.1.val v.1.val.2.val) v.2.val / 4)
          (Sum.elim
            (fun v => lpHaarTraceErrorBudget
              (δo v.1.1.val.1.val v.1.1.val.2.val) v.1.2.val / 4)
            (fun v => ν v.1.val.1.val v.2.val.1.val v.1.val.2.val v.2.val.2.val)))))

theorem concreteTraceErrorBudget_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    0 < lpHaarTraceErrorBudget δ n := by
  unfold lpHaarTraceErrorBudget
  exact mul_pos hδ (pow_pos (by norm_num) _)

theorem concreteInnerTolerance_pos (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (ho : ∀ i j, 0 < δo i j) (hi : ∀ i j, 0 < δi i j)
    (hv : ∀ i j k l, 0 < ν i j k l) (n : ℕ) :
    ∀ v, 0 < concreteInnerTolerance δo δi ν n v := by
  intro v
  rcases v with v | v
  · exact concreteTraceErrorBudget_pos (hi _ _) _
  rcases v with v | v
  · exact concreteTraceErrorBudget_pos (hi _ _) _
  rcases v with v | v
  · exact div_pos (concreteTraceErrorBudget_pos (ho _ _) _) (by norm_num)
  rcases v with v | v
  · exact div_pos (concreteTraceErrorBudget_pos (ho _ _) _) (by norm_num)
  rcases v with v | v
  · exact div_pos (concreteTraceErrorBudget_pos (ho _ _) _) (by norm_num)
  · exact hv _ _ _ _

theorem concreteInnerStep_of_finite_errors (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ) {n : ℕ}
    (ho hi : Fin n → LpHaarFiniteSplit) (S : LpHaarFiniteSplit)
    (h : ∀ v, ‖concreteInnerError p T a b ho hi v S‖ ≤
      concreteInnerTolerance δo δi ν n v) :
    ConcreteInnerStep p T a b δo δi ν n ho hi S := by
  constructor
  · intro I K hIK
    exact h (Sum.inl ⟨(I, K), hIK⟩)
  · intro I K hIK s
    exact h (Sum.inr (Sum.inl (⟨(I, K), hIK⟩, s)))
  · intro J L hJL hborn i
    exact h (Sum.inr (Sum.inr (Sum.inl (⟨(J, L), hJL, hborn⟩, i))))
  · intro J L hJL hborn i
    exact h (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨(J, L), hJL, hborn⟩, i)))))
  · intro J L hJL hborn i s
    exact h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      ((⟨(J, L), hJL, hborn⟩, i), s))))))
  · intro I K hIK J L hJL hborn
    exact h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (⟨(I, K), hIK⟩, ⟨(J, L), hJL, hborn⟩))))))

theorem exists_concrete_inner_step_of_actual_moments (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hδo : ∀ i j, 0 < δo i j) (hδi : ∀ i j, 0 < δi i j)
    (hν : ∀ i j k l, 0 < ν i j k l) (n : ℕ)
    (ho hi : Fin n → LpHaarFiniteSplit) (P : LpHaarFiniteParent)
    (r : ℕ → ℕ) (hr : StrictMono r) (N : ℕ)
    (hlim : ∀ v, Tendsto (fun k => mean (fun θ =>
      ‖concreteInnerError p T a b ho hi v (candidateRefinedSplit P (r k) θ)‖ ^ 2))
      atTop (𝓝 0)) :
    ∃ S : LpHaarFiniteSplit, ∃ k : ℕ, S.level = r k ∧ N ≤ S.level ∧
      S.parent.set = P.set ∧ ConcreteInnerStep p T a b δo δi ν n ho hi S := by
  obtain ⟨S, k, hk, hN, hparent, herrors⟩ :=
    exists_candidate_split_of_actual_error_moment_limits P r hr
      (concreteInnerError p T a b ho hi) (concreteInnerTolerance δo δi ν n)
      (concreteInnerTolerance_pos δo δi ν hδo hδi hν n) N hlim
  exact ⟨S, k, hk, hN, hparent,
    concreteInnerStep_of_finite_errors p T a b δo δi ν ho hi S (fun v => (herrors v).le)⟩

end SurveyStatements.P5OperatorReduction
