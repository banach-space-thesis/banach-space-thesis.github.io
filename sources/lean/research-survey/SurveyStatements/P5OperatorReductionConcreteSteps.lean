import SurveyStatements.P5HaarNorm
import SurveyStatements.P5OperatorReductionAlternatingHistories
import SurveyStatements.P5OperatorReductionTraceBalancedMultipliers

/-! Concrete finite analytic conditions for the alternating construction.
Every entry is an actual mixed-operator pairing. The two trace functions
are normalized by their parent measures by the trace construction.
Birth conditions include every old parent and both of its child sets. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev concreteInnerExponent : BanachExponent := ⟨1, le_rfl⟩
abbrev NormalizedBlockTrace (𝕜 : Type*) :=
  (LpHaarFiniteSplit × LpHaarFiniteSplit) → LpHaarFiniteParent → 𝕜

def concreteMixedEntry (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os Is : LpHaarFiniteSplit) : 𝕜 :=
  Ot.reader 𝕜 p
    (((It.reader 𝕜 concreteInnerExponent).compLpL p.val unitIntervalMeasure)
      (T (tensorWith (p := p.val) (Is.vector 𝕜 concreteInnerExponent)
        (Os.vector 𝕜 p))))

def currentSplitHistory {n : ℕ} (h : Fin n → LpHaarFiniteSplit)
    (S : LpHaarFiniteSplit) : Fin (n + 1) → LpHaarFiniteSplit :=
  Fin.lastCases S h

structure ConcreteInnerStep (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (n : ℕ) (ho hi : Fin n → LpHaarFiniteSplit) (S : LpHaarFiniteSplit) : Prop where
  point : ∀ I K : Fin n, I ≠ K →
    ‖concreteMixedEntry p T (ho I) S (ho K) S - b (ho I, ho K) S.parent‖ ≤
      lpHaarTraceErrorBudget (δi I.val K.val) n
  balance : ∀ I K : Fin n, I ≠ K → ∀ s : Bool,
    ‖b (ho I, ho K) (S.child s) - b (ho I, ho K) S.parent‖ ≤
      lpHaarTraceErrorBudget (δi I.val K.val) n
  birth_entries : ∀ J L : Fin (n + 1), J ≠ L → J.val = n ∨ L.val = n →
    ∀ i : Fin n,
      ‖concreteMixedEntry p T (ho i) (currentSplitHistory hi S J)
        (ho i) (currentSplitHistory hi S L)‖ ≤
          lpHaarTraceErrorBudget (δo J.val L.val) i.val / 4
  birth_parents : ∀ J L : Fin (n + 1), J ≠ L → J.val = n ∨ L.val = n →
    ∀ i : Fin n,
      ‖a (currentSplitHistory hi S J, currentSplitHistory hi S L) (ho i).parent‖ ≤
        lpHaarTraceErrorBudget (δo J.val L.val) i.val / 4
  birth_children : ∀ J L : Fin (n + 1), J ≠ L → J.val = n ∨ L.val = n →
    ∀ i : Fin n, ∀ s : Bool,
      ‖a (currentSplitHistory hi S J, currentSplitHistory hi S L) ((ho i).child s)‖ ≤
        lpHaarTraceErrorBudget (δo J.val L.val) i.val / 4
  mixed : ∀ I K : Fin n, I ≠ K → ∀ J L : Fin (n + 1), J ≠ L →
    J.val = n ∨ L.val = n →
      ‖concreteMixedEntry p T (ho I) (currentSplitHistory hi S J)
        (ho K) (currentSplitHistory hi S L)‖ ≤ ν I.val J.val K.val L.val

structure ConcreteOuterStep (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (n : ℕ) (ho : Fin n → LpHaarFiniteSplit)
    (hi : Fin (n + 1) → LpHaarFiniteSplit) (S : LpHaarFiniteSplit) : Prop where
  point : ∀ J L : Fin (n + 1), J ≠ L →
    ‖concreteMixedEntry p T S (hi J) S (hi L) - a (hi J, hi L) S.parent‖ ≤
      lpHaarTraceErrorBudget (δo J.val L.val) n
  balance : ∀ J L : Fin (n + 1), J ≠ L → ∀ s : Bool,
    ‖a (hi J, hi L) (S.child s) - a (hi J, hi L) S.parent‖ ≤
      lpHaarTraceErrorBudget (δo J.val L.val) n
  birth_entries : ∀ I K : Fin (n + 1), I ≠ K → I.val = n ∨ K.val = n →
    ∀ j : Fin (n + 1),
      ‖concreteMixedEntry p T (currentSplitHistory ho S I) (hi j)
        (currentSplitHistory ho S K) (hi j)‖ ≤
          lpHaarTraceErrorBudget (δi I.val K.val) j.val / 4
  birth_parents : ∀ I K : Fin (n + 1), I ≠ K → I.val = n ∨ K.val = n →
    ∀ j : Fin (n + 1),
      ‖b (currentSplitHistory ho S I, currentSplitHistory ho S K) (hi j).parent‖ ≤
        lpHaarTraceErrorBudget (δi I.val K.val) j.val / 4
  birth_children : ∀ I K : Fin (n + 1), I ≠ K → I.val = n ∨ K.val = n →
    ∀ j : Fin (n + 1), ∀ s : Bool,
      ‖b (currentSplitHistory ho S I, currentSplitHistory ho S K) ((hi j).child s)‖ ≤
        lpHaarTraceErrorBudget (δi I.val K.val) j.val / 4
  mixed : ∀ I K : Fin (n + 1), I ≠ K → I.val = n ∨ K.val = n →
    ∀ J L : Fin (n + 1), J ≠ L →
      ‖concreteMixedEntry p T (currentSplitHistory ho S I) (hi J)
        (currentSplitHistory ho S K) (hi L)‖ ≤ ν I.val J.val K.val L.val

end SurveyStatements.P5OperatorReduction
