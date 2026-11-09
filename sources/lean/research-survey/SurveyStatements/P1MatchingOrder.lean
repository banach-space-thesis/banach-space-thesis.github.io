import SurveyStatements.P1MatchingResiduals
import SurveyStatements.P1FiniteInitialSegments
import Aesop

/-! The finite witnesses produced by matching are comparable as initial
segments. Every unmatched witness point lies after the other entire witness. -/

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem matchingFrontStep_newA (a b : MatchingColor) (A B : Finset ℕ)
    (x y z : ℕ) (hz : z ∈ (matchingFrontStep a b A B x y).1) (hold : z ∉ A) :
    z = x ∧ ¬ (a = .inside ∧ b = .before) := by
  cases a <;> cases b <;> simp only [matchingFrontStep, Finset.mem_insert] at hz <;> aesop

theorem matchingFrontStep_newB (a b : MatchingColor) (A B : Finset ℕ)
    (x y z : ℕ) (hz : z ∈ (matchingFrontStep a b A B x y).2) (hold : z ∉ B) :
    (a = .inside ∧ b = .inside ∧ z = x) ∨
    (a = .inside ∧ b = .before ∧ z = x) ∨
    (z = y ∧ ¬ (a = .inside ∧ b = .inside) ∧
      ¬ (a = .inside ∧ b = .before) ∧ ¬ (a = .before ∧ b = .inside)) := by
  cases a <;> cases b <;> simp only [matchingFrontStep, Finset.mem_insert] at hz <;> aesop

theorem matchingFrontStep_generalB (a b : MatchingColor) (A B : Finset ℕ) (x y : ℕ)
    (hii : ¬ (a = .inside ∧ b = .inside))
    (hib : ¬ (a = .inside ∧ b = .before))
    (hbi : ¬ (a = .before ∧ b = .inside)) :
    (matchingFrontStep a b A B x y).2 = insert y B := by
  cases a <;> cases b <;> simp_all [matchingFrontStep]

section Run

variable (F : Set ℕ → Finset ℕ) (hF : IsLocallyConstantFiniteAssignment F)
  (N : Set ℕ) (hN : N.Infinite)
  (hsupp : ∀ A : Set ℕ, A.Infinite → (F A : Set ℕ) ⊆ A)

include hsupp

local notation "q" => twoFrontMatchRun F hF N hN
local notation "L" => finiteFrontLimit (fun n => (q n).frontA)
local notation "M" => finiteFrontLimit (fun n => (q n).frontB)

theorem twoFrontMatchRun_frontA_exclusive (n : ℕ) :
    ∀ z ∈ (q n).frontA, z ∈ F L → z ∉ F M → ∀ w ∈ F M, w < z := by
  induction n with
  | zero =>
    intro z hz
    change z ∈ (∅ : Finset ℕ) at hz
    exact False.elim (Finset.notMem_empty _ hz)
  | succ n ih =>
    intro z hz hzF hznot w hw
    by_cases hold : z ∈ (q n).frontA
    · exact ih z hold hzF hznot w hw
    have heqA := congrArg Prod.fst (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heqA
    have heqB := congrArg Prod.snd (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heqB
    change z ∈ (twoFrontMatchNext F hF (q n)).frontA at hz
    rw [heqA] at hz
    obtain ⟨rfl, hnotheld⟩ := matchingFrontStep_newA _ _ _ _ _ _ _ hz hold
    have hxAdded : twoFrontMatchX (q n) ∈ (q (n + 1)).frontA := by
      change _ ∈ (twoFrontMatchNext F hF (q n)).frontA
      rwa [heqA]
    have hpA := twoFrontMatchRun_predictA_at_X F hF N hN
      (twoFrontMatchRun_limitA_infinite F hF N hN) n hxAdded
    have hcA : (q n).colorA = .inside := hpA.symm.trans
      ((finiteSetMatchingColor_inside F L _).mpr hzF)
    cases hcB : (q n).colorB with
    | inside =>
      have hxB : twoFrontMatchX (q n) ∈ (q (n + 1)).frontB := by
        change _ ∈ (twoFrontMatchNext F hF (q n)).frontB
        rw [heqB]
        simp [hcA, hcB, matchingFrontStep]
      have hpB := twoFrontMatchRun_predictB_at_X F hF N hN
        (twoFrontMatchRun_limitB_infinite F hF N hN) n hxB
      exact False.elim (hznot ((finiteSetMatchingColor_inside F M _).mp (hpB.trans hcB)))
    | before => exact False.elim (hnotheld ⟨hcA, hcB⟩)
    | after =>
      have hshapeB : (q (n + 1)).frontB = insert (twoFrontMatchY (q n)) (q n).frontB := by
        change (twoFrontMatchNext F hF (q n)).frontB = _
        rw [heqB]
        simp [hcA, hcB, matchingFrontStep]
      have hpB := twoFrontMatchRun_predictB_at_Y F hF N hN n hshapeB
      have hFM := twoFrontMatchRun_witnessB_subset_front_after F hF N hN hsupp n hshapeB
        (hpB.trans hcB)
      exact (q n).separated w (Finset.mem_union_right _ (hFM hw)) _ (twoFrontMatchX_mem (q n))

theorem twoFrontMatchRun_frontB_exclusive (n : ℕ) :
    ∀ z ∈ (q n).frontB, z ∈ F M → z ∉ F L → ∀ w ∈ F L, w < z := by
  induction n with
  | zero =>
    intro z hz
    change z ∈ (∅ : Finset ℕ) at hz
    exact False.elim (Finset.notMem_empty _ hz)
  | succ n ih =>
    intro z hz hzF hznot w hw
    by_cases hold : z ∈ (q n).frontB
    · exact ih z hold hzF hznot w hw
    have heqA := congrArg Prod.fst (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heqA
    have heqB := congrArg Prod.snd (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heqB
    change z ∈ (twoFrontMatchNext F hF (q n)).frontB at hz
    rw [heqB] at hz
    rcases matchingFrontStep_newB _ _ _ _ _ _ _ hz hold with
      ⟨hcA, hcB, rfl⟩ | ⟨hcA, hcB, rfl⟩ | ⟨rfl, hii, hib, hbi⟩
    · have hxA : twoFrontMatchX (q n) ∈ (q (n + 1)).frontA := by
        change _ ∈ (twoFrontMatchNext F hF (q n)).frontA
        rw [heqA]
        simp [hcA, hcB, matchingFrontStep]
      have hpA := twoFrontMatchRun_predictA_at_X F hF N hN
        (twoFrontMatchRun_limitA_infinite F hF N hN) n hxA
      exact False.elim (hznot ((finiteSetMatchingColor_inside F L _).mp (hpA.trans hcA)))
    · have hxB : twoFrontMatchX (q n) ∈ (q (n + 1)).frontB := by
        change _ ∈ (twoFrontMatchNext F hF (q n)).frontB
        rw [heqB]
        simp [hcA, hcB, matchingFrontStep]
      have hpB := twoFrontMatchRun_predictB_at_X F hF N hN
        (twoFrontMatchRun_limitB_infinite F hF N hN) n hxB
      have hinside := (finiteSetMatchingColor_inside F M _).mpr hzF
      rw [hpB, hcB] at hinside
      cases hinside
    · have hshapeB : (q (n + 1)).frontB = insert (twoFrontMatchY (q n)) (q n).frontB := by
        change (twoFrontMatchNext F hF (q n)).frontB = _
        rw [heqB]
        exact matchingFrontStep_generalB _ _ _ _ _ _ hii hib hbi
      have hpB := twoFrontMatchRun_predictB_at_Y F hF N hN n hshapeB
      have hcB : (q n).colorB = .inside := hpB.symm.trans
        ((finiteSetMatchingColor_inside F M _).mpr hzF)
      have hcA : (q n).colorA = .after := by
        cases ha : (q n).colorA with
        | inside => exact False.elim (hii ⟨ha, hcB⟩)
        | before => exact False.elim (hbi ⟨ha, hcB⟩)
        | after => rfl
      have hxA : twoFrontMatchX (q n) ∈ (q (n + 1)).frontA := by
        change _ ∈ (twoFrontMatchNext F hF (q n)).frontA
        rw [heqA]
        simp [hcA, hcB, matchingFrontStep]
      have hpA := twoFrontMatchRun_predictA_at_X F hF N hN
        (twoFrontMatchRun_limitA_infinite F hF N hN) n hxA
      have hFL := twoFrontMatchRun_witnessA_subset_front_after F hF N hN hsupp n (hpA.trans hcA)
      exact ((q n).separated w (Finset.mem_union_left _ (hFL hw)) _
        (twoFrontMatchX_mem (q n))).trans (twoFrontMatchY_spec (q n)).2

theorem twoFrontMatchRun_witnesses_initialSegments :
    FinsetIsInitialSegment (F L) (F M) ∨ FinsetIsInitialSegment (F M) (F L) := by
  have hA : ∀ z ∈ F L, z ∉ F M → ∀ w ∈ F M, w < z := by
    intro z hz hznot
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp (hsupp L (twoFrontMatchRun_limitA_infinite F hF N hN) hz)
    exact twoFrontMatchRun_frontA_exclusive F hF N hN hsupp n z hzn hz hznot
  have hB : ∀ z ∈ F M, z ∉ F L → ∀ w ∈ F L, w < z := by
    intro z hz hznot
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp (hsupp M (twoFrontMatchRun_limitB_infinite F hF N hN) hz)
    exact twoFrontMatchRun_frontB_exclusive F hF N hN hsupp n z hzn hz hznot
  by_cases hLM : F L ⊆ F M
  · exact Or.inl ⟨hLM, fun a ha b hb hbnot => hB b hb hbnot a ha⟩
  · have hML : F M ⊆ F L := by
      intro y hy
      by_contra hynot
      obtain ⟨x, hx, hxnot⟩ := Finset.not_subset.mp hLM
      exact (not_lt_of_gt (hA x hx hxnot y hy)) (hB y hy hynot x hx)
    exact Or.inr ⟨hML, fun a ha b hb hbnot => hA b hb hbnot a ha⟩

end Run

theorem finiteSet_matching_lemma (F : Set ℕ → Finset ℕ)
    (hF : IsLocallyConstantFiniteAssignment F)
    (hsupp : ∀ A : Set ℕ, A.Infinite → (F A : Set ℕ) ⊆ A)
    (N : Set ℕ) (hN : N.Infinite) :
    ∃ L M : Set ℕ, L ⊆ N ∧ M ⊆ N ∧ (L).Infinite ∧ (M).Infinite ∧
      (FinsetIsInitialSegment (F L) (F M) ∨ FinsetIsInitialSegment (F M) (F L)) ∧
      L ∩ M = (F L : Set ℕ) ∩ (F M : Set ℕ) := by
  let q := twoFrontMatchRun F hF N hN
  let L := finiteFrontLimit (fun n => (q n).frontA)
  let M := finiteFrontLimit (fun n => (q n).frontB)
  refine ⟨L, M, ?_, ?_, twoFrontMatchRun_limitA_infinite F hF N hN,
    twoFrontMatchRun_limitB_infinite F hF N hN,
    twoFrontMatchRun_witnesses_initialSegments F hF N hN hsupp,
    twoFrontMatchRun_intersection_witnesses F hF N hN hsupp⟩
  · intro i hi
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hi
    exact (q n).subsetA hn
  · intro i hi
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hi
    exact (q n).subsetB hn

end SurveyStatements.P1
