import SurveyStatements.P1MatchingColors

/-! The two-front recursion for the one-set matching lemma. Every stage
predicts the color of either next point on all infinite residual tails. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

def IsLocallyConstantFiniteAssignment (F : Set ℕ → Finset ℕ) : Prop :=
  ∀ A : Set ℕ, A.Infinite → ∃ r : ℕ,
    ∀ B : Set ℕ, B.Infinite →
      (∀ i : ℕ, i < r → (i ∈ A ↔ i ∈ B)) → F B = F A

structure TwoFrontMatchState (F : Set ℕ → Finset ℕ) (N : Set ℕ) where
  frontA : Finset ℕ
  frontB : Finset ℕ
  subsetA : (frontA : Set ℕ) ⊆ N
  subsetB : (frontB : Set ℕ) ⊆ N
  tail : Set ℕ
  tailSubset : tail ⊆ N
  tailInfinite : tail.Infinite
  separated : ∀ a ∈ frontA ∪ frontB, ∀ b ∈ tail, a < b
  colorA : MatchingColor
  colorB : MatchingColor
  predictsA : ∀ Q : Set ℕ, Q ⊆ tail → Q.Infinite →
    finiteSetMatchingColor F ((frontA : Set ℕ) ∪ Q) (sInf Q) = colorA
  predictsB : ∀ Q : Set ℕ, Q ⊆ tail → Q.Infinite →
    finiteSetMatchingColor F ((frontB : Set ℕ) ∪ Q) (sInf Q) = colorB

def matchingFrontStep (a b : MatchingColor) (A B : Finset ℕ) (x y : ℕ) :
    Finset ℕ × Finset ℕ :=
  match a, b with
  | .inside, .inside => (insert x A, insert x B)
  | .inside, .before => (A, insert x B)
  | .before, .inside => (insert x A, B)
  | _, _ => (insert x A, insert y B)

def twoFrontMatchX {F : Set ℕ → Finset ℕ} {N : Set ℕ}
    (q : TwoFrontMatchState F N) : ℕ := sInf q.tail

theorem twoFrontMatchX_mem {F : Set ℕ → Finset ℕ} {N : Set ℕ}
    (q : TwoFrontMatchState F N) : twoFrontMatchX q ∈ q.tail :=
  Nat.sInf_mem q.tailInfinite.nonempty

def twoFrontMatchY {F : Set ℕ → Finset ℕ} {N : Set ℕ}
    (q : TwoFrontMatchState F N) : ℕ :=
  (q.tailInfinite.exists_gt (twoFrontMatchX q)).choose

theorem twoFrontMatchY_spec {F : Set ℕ → Finset ℕ} {N : Set ℕ}
    (q : TwoFrontMatchState F N) :
    twoFrontMatchY q ∈ q.tail ∧ twoFrontMatchX q < twoFrontMatchY q :=
  (q.tailInfinite.exists_gt (twoFrontMatchX q)).choose_spec

def twoFrontMatchInitial (F : Set ℕ → Finset ℕ)
    (hF : IsLocallyConstantFiniteAssignment F) (N : Set ℕ) (hN : N.Infinite) :
    TwoFrontMatchState F N := by
  let hex := exists_twoFront_matching_prediction F hF ∅ ∅ N hN
  let Y := hex.choose
  have hY := hex.choose_spec
  let a := hY.2.2.2.choose
  let b := hY.2.2.2.choose_spec.choose
  have hp := hY.2.2.2.choose_spec.choose_spec
  exact
    { frontA := ∅
      frontB := ∅
      subsetA := by simp
      subsetB := by simp
      tail := Y
      tailSubset := hY.1
      tailInfinite := hY.2.1
      separated := hY.2.2.1
      colorA := a
      colorB := b
      predictsA := hp.1
      predictsB := hp.2 }

def twoFrontMatchNext (F : Set ℕ → Finset ℕ)
    (hF : IsLocallyConstantFiniteAssignment F) {N : Set ℕ}
    (q : TwoFrontMatchState F N) : TwoFrontMatchState F N := by
  let x := twoFrontMatchX q
  let y := twoFrontMatchY q
  let AB := matchingFrontStep q.colorA q.colorB q.frontA q.frontB x y
  have hxN : x ∈ N := q.tailSubset (twoFrontMatchX_mem q)
  have hyN : y ∈ N := q.tailSubset (twoFrontMatchY_spec q).1
  have hAN : (AB.1 : Set ℕ) ⊆ N := by
    cases ha : q.colorA <;> cases hb : q.colorB <;>
      simp only [AB, matchingFrontStep, ha, hb, Finset.coe_insert]
    all_goals first | exact q.subsetA | exact Set.insert_subset hxN q.subsetA
  have hBN : (AB.2 : Set ℕ) ⊆ N := by
    cases ha : q.colorA <;> cases hb : q.colorB <;>
      simp only [AB, matchingFrontStep, ha, hb, Finset.coe_insert]
    all_goals first | exact q.subsetB | exact Set.insert_subset hxN q.subsetB |
      exact Set.insert_subset hyN q.subsetB
  let T := q.tail ∩ Ioi y
  have hT : T.Infinite := infiniteSet_inter_Ioi q.tail q.tailInfinite y
  let hex := exists_twoFront_matching_prediction F hF AB.1 AB.2 T hT
  let Y := hex.choose
  have hY := hex.choose_spec
  let a := hY.2.2.2.choose
  let b := hY.2.2.2.choose_spec.choose
  have hp := hY.2.2.2.choose_spec.choose_spec
  exact
    { frontA := AB.1
      frontB := AB.2
      subsetA := hAN
      subsetB := hBN
      tail := Y
      tailSubset := fun i hi => q.tailSubset (hY.1 hi).1
      tailInfinite := hY.2.1
      separated := hY.2.2.1
      colorA := a
      colorB := b
      predictsA := hp.1
      predictsB := hp.2 }

theorem twoFrontMatchNext_fronts (F : Set ℕ → Finset ℕ)
    (hF : IsLocallyConstantFiniteAssignment F) {N : Set ℕ}
    (q : TwoFrontMatchState F N) :
    ((twoFrontMatchNext F hF q).frontA, (twoFrontMatchNext F hF q).frontB) =
      matchingFrontStep q.colorA q.colorB q.frontA q.frontB
        (twoFrontMatchX q) (twoFrontMatchY q) := rfl

theorem twoFrontMatchNext_tail (F : Set ℕ → Finset ℕ)
    (hF : IsLocallyConstantFiniteAssignment F) {N : Set ℕ}
    (q : TwoFrontMatchState F N) :
    (twoFrontMatchNext F hF q).tail ⊆ q.tail ∩ Ioi (twoFrontMatchY q) := by
  exact (exists_twoFront_matching_prediction F hF
    (matchingFrontStep q.colorA q.colorB q.frontA q.frontB
      (twoFrontMatchX q) (twoFrontMatchY q)).1
    (matchingFrontStep q.colorA q.colorB q.frontA q.frontB
      (twoFrontMatchX q) (twoFrontMatchY q)).2
    (q.tail ∩ Ioi (twoFrontMatchY q))
    (infiniteSet_inter_Ioi q.tail q.tailInfinite (twoFrontMatchY q))).choose_spec.1

def twoFrontMatchRun (F : Set ℕ → Finset ℕ)
    (hF : IsLocallyConstantFiniteAssignment F) (N : Set ℕ) (hN : N.Infinite) :
    ℕ → TwoFrontMatchState F N
  | 0 => twoFrontMatchInitial F hF N hN
  | n + 1 => twoFrontMatchNext F hF (twoFrontMatchRun F hF N hN n)

theorem matchingFrontStep_monoA (a b : MatchingColor)
    (A B : Finset ℕ) (x y : ℕ) :
    A ⊆ (matchingFrontStep a b A B x y).1 := by
  cases a <;> cases b <;> simp [matchingFrontStep]

theorem matchingFrontStep_monoB (a b : MatchingColor)
    (A B : Finset ℕ) (x y : ℕ) :
    B ⊆ (matchingFrontStep a b A B x y).2 := by
  cases a <;> cases b <;> simp [matchingFrontStep]

theorem matchingFrontStep_mem_union (a b : MatchingColor)
    (A B : Finset ℕ) (x y : ℕ) :
    x ∈ (matchingFrontStep a b A B x y).1 ∪
      (matchingFrontStep a b A B x y).2 := by
  cases a <;> cases b <;> simp [matchingFrontStep]

end SurveyStatements.P1
