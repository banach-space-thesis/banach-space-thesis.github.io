import SurveyStatements.P5OperatorReductionConcreteSteps

/-! Coherent trees carrying the actual finite-step analytic inequalities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem currentSplitHistory_sequence (f : ℕ → LpHaarFiniteSplit) (n : ℕ)
    (i : Fin (n + 1)) :
    currentSplitHistory (fun j : Fin n => f j.val) (f n) i = f i.val := by
  induction i using Fin.lastCases with
  | last => simp [currentSplitHistory]
  | cast i => simp [currentSplitHistory]

def NormalizedTraceExtensional (a : NormalizedBlockTrace 𝕜) : Prop :=
  ∀ pair P Q, P.set = Q.set → a pair P = a pair Q

theorem normalizedTrace_parent (a : NormalizedBlockTrace 𝕜)
    (ha : NormalizedTraceExtensional a) (pair : LpHaarFiniteSplit × LpHaarFiniteSplit)
    (F : LpHaarSequentialSplits) (j : ℕ) (hj : j ≠ 0) :
    a pair (F.node j).parent =
      a pair ((F.node ((j - 1) / 2)).child (decide (j % 2 = 1))) := by
  apply ha
  simpa only [lpHaarHistoryParent, dif_neg hj] using F.parent j

structure ConcreteTreeSteps (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ) (Fo Fi : LpHaarSequentialSplits) : Prop where
  inner : ∀ n, ConcreteInnerStep p T a b δo δi ν n
    (fun i : Fin n => Fo.node i.val) (fun i : Fin n => Fi.node i.val) (Fi.node n)
  outer : ∀ n, ConcreteOuterStep p T a b δo δi ν n
    (fun i : Fin n => Fo.node i.val) (fun i : Fin (n + 1) => Fi.node i.val) (Fo.node n)

theorem exists_concrete_trees (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (δo δi : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hinner : ∀ n (ho hi : Fin n → LpHaarFiniteSplit)
      (P : LpHaarFiniteParent) (N : ℕ),
      ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
        ConcreteInnerStep p T a b δo δi ν n ho hi S)
    (houter : ∀ n (ho : Fin n → LpHaarFiniteSplit)
      (hi : Fin (n + 1) → LpHaarFiniteSplit) (P : LpHaarFiniteParent) (N : ℕ),
      ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
        ConcreteOuterStep p T a b δo δi ν n ho hi S) :
    ∃ Fo Fi : LpHaarSequentialSplits,
      (∀ i j, i < j → (Fo.node i).level < (Fo.node j).level) ∧
      (∀ i j, i < j → (Fi.node i).level < (Fi.node j).level) ∧
      ConcreteTreeSteps p T a b δo δi ν Fo Fi := by
  obtain ⟨Fo, Fi, hFo, hFi, hI, hO⟩ := exists_alternating_split_histories
    (ConcreteInnerStep p T a b δo δi ν)
    (ConcreteOuterStep p T a b δo δi ν) (by
      intro n h _
      let ho := alternatingOuterHistory h
      let hi := alternatingInnerHistory h
      let Ni := n + (∑ i : Fin n, (hi i).level) + 1
      obtain ⟨Si, hSi, hPi, hIi⟩ := hinner n ho hi (lpHaarHistoryParent n hi) Ni
      let No := n + (∑ i : Fin n, (ho i).level) + 1
      obtain ⟨So, hSo, hPo, hOo⟩ := houter n ho (Fin.lastCases Si hi)
        (lpHaarHistoryParent n ho) No
      refine ⟨(So, Si), ⟨?_, ?_, hPo, hPi, ?_, ?_, hIi, hOo⟩⟩
      · dsimp [No] at hSo
        change n ≤ So.level
        omega
      · dsimp [Ni] at hSi
        change n ≤ Si.level
        omega
      · intro i
        have hle : (ho i).level ≤ ∑ j : Fin n, (ho j).level :=
          Finset.single_le_sum (fun j _ => show 0 ≤ (ho j).level from Nat.zero_le _)
            (Finset.mem_univ i)
        dsimp [No] at hSo
        change (ho i).level < So.level
        omega
      · intro i
        have hle : (hi i).level ≤ ∑ j : Fin n, (hi j).level :=
          Finset.single_le_sum (fun j _ => show 0 ≤ (hi j).level from Nat.zero_le _)
            (Finset.mem_univ i)
        dsimp [Ni] at hSi
        change (hi i).level < Si.level
        omega)
  refine ⟨Fo, Fi, hFo, hFi, ⟨hI, ?_⟩⟩
  intro n
  have heq : Fin.lastCases (Fi.node n) (fun i : Fin n => Fi.node i.val) =
      (fun i : Fin (n + 1) => Fi.node i.val) := by
    funext i
    exact currentSplitHistory_sequence Fi.node n i
  simpa only [heq] using hO n

end SurveyStatements.P5OperatorReduction
