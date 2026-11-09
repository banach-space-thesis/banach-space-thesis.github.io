import SurveyStatements.P1TwoFrontLimits

/-! Neither front can stop growing. If one did, the other would retain the
color 'before' at arbitrarily late points, contradicting finiteness of its
chosen witness set. -/

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem matchingFrontStep_holdA_of_no_new (a b : MatchingColor)
    (A B : Finset ℕ) (x y : ℕ) (hx : x ∉ A)
    (h : (matchingFrontStep a b A B x y).1 ⊆ A) :
    a = .inside ∧ b = .before := by
  cases a <;> cases b <;> simp_all [matchingFrontStep, Finset.insert_subset_iff]

theorem matchingFrontStep_holdB_of_no_new (a b : MatchingColor)
    (A B : Finset ℕ) (x y : ℕ) (hx : x ∉ B) (hy : y ∉ B)
    (h : (matchingFrontStep a b A B x y).2 ⊆ B) :
    a = .before ∧ b = .inside := by
  cases a <;> cases b <;> simp_all [matchingFrontStep, Finset.insert_subset_iff]

section Run

variable (F : Set ℕ → Finset ℕ) (hF : IsLocallyConstantFiniteAssignment F)
  (N : Set ℕ) (hN : N.Infinite)

local notation "q" => twoFrontMatchRun F hF N hN
local notation "L" => finiteFrontLimit (fun n => (q n).frontA)
local notation "M" => finiteFrontLimit (fun n => (q n).frontB)

theorem twoFrontMatchRun_X_not_frontA (n : ℕ) : twoFrontMatchX (q n) ∉ (q n).frontA := by
  intro hx
  exact (lt_irrefl _) ((q n).separated _ (Finset.mem_union_left _ hx)
    _ (twoFrontMatchX_mem (q n)))

theorem twoFrontMatchRun_X_not_frontB (n : ℕ) : twoFrontMatchX (q n) ∉ (q n).frontB := by
  intro hx
  exact (lt_irrefl _) ((q n).separated _ (Finset.mem_union_right _ hx)
    _ (twoFrontMatchX_mem (q n)))

theorem twoFrontMatchRun_Y_not_frontB (n : ℕ) : twoFrontMatchY (q n) ∉ (q n).frontB := by
  intro hy
  exact (lt_irrefl _) ((q n).separated _ (Finset.mem_union_right _ hy)
    _ (twoFrontMatchY_spec (q n)).1)

theorem twoFrontMatchRun_predictA_at_X (hL : (L).Infinite) (n : ℕ)
    (hx : twoFrontMatchX (q n) ∈ (q (n + 1)).frontA) :
    finiteSetMatchingColor F L (twoFrontMatchX (q n)) = (q n).colorA := by
  let Q := L \ (q n).frontA
  have hQ : Q.Infinite := hL.diff (q n).frontA.finite_toSet
  have hQtail : Q ⊆ (q n).tail := twoFrontMatchRun_limitA_tail F hF N hN n
  have hxQ : twoFrontMatchX (q n) ∈ Q :=
    ⟨finiteFront_subset_limit _ (n + 1) hx, twoFrontMatchRun_X_not_frontA F hF N hN n⟩
  have hmin : sInf Q = twoFrontMatchX (q n) := by
    apply le_antisymm (Nat.sInf_le hxQ)
    exact Nat.sInf_le (hQtail (Nat.sInf_mem hQ.nonempty))
  have hfront : ((q n).frontA : Set ℕ) ∪ Q = L := by
    ext i
    constructor
    · rintro (hi | hi)
      · exact finiteFront_subset_limit _ n hi
      · exact hi.1
    · intro hi
      by_cases hif : i ∈ (q n).frontA
      · exact Or.inl hif
      · exact Or.inr ⟨hi, hif⟩
  have hp := (q n).predictsA Q hQtail hQ
  rwa [hfront, hmin] at hp

theorem twoFrontMatchRun_predictB_at_X (hM : (M).Infinite) (n : ℕ)
    (hx : twoFrontMatchX (q n) ∈ (q (n + 1)).frontB) :
    finiteSetMatchingColor F M (twoFrontMatchX (q n)) = (q n).colorB := by
  let Q := M \ (q n).frontB
  have hQ : Q.Infinite := hM.diff (q n).frontB.finite_toSet
  have hQtail : Q ⊆ (q n).tail := twoFrontMatchRun_limitB_tail F hF N hN n
  have hxQ : twoFrontMatchX (q n) ∈ Q :=
    ⟨finiteFront_subset_limit _ (n + 1) hx, twoFrontMatchRun_X_not_frontB F hF N hN n⟩
  have hmin : sInf Q = twoFrontMatchX (q n) := by
    apply le_antisymm (Nat.sInf_le hxQ)
    exact Nat.sInf_le (hQtail (Nat.sInf_mem hQ.nonempty))
  have hfront : ((q n).frontB : Set ℕ) ∪ Q = M := by
    ext i
    constructor
    · rintro (hi | hi)
      · exact finiteFront_subset_limit _ n hi
      · exact hi.1
    · intro hi
      by_cases hif : i ∈ (q n).frontB
      · exact Or.inl hif
      · exact Or.inr ⟨hi, hif⟩
  have hp := (q n).predictsB Q hQtail hQ
  rwa [hfront, hmin] at hp

theorem twoFrontMatchRun_limitA_infinite : (L).Infinite := by
  by_contra hL
  have hLfin : (L).Finite := Set.not_infinite.mp hL
  have hM : (M).Infinite := (Set.infinite_union.mp
    (twoFrontMatchRun_limit_union_infinite F hF N hN)).resolve_left hL
  obtain ⟨k, hk⟩ := monotone_finiteFront_limit_finite _
    (twoFrontMatchRun_monoA F hF N hN) hLfin
  have hcolors (n : ℕ) (hkn : k ≤ n) :
      (q n).colorA = .inside ∧ (q n).colorB = .before := by
    apply matchingFrontStep_holdA_of_no_new _ _ _ _ _ _
      (twoFrontMatchRun_X_not_frontA F hF N hN n)
    have hstep := (hk (n + 1)).trans (twoFrontMatchRun_monoA F hF N hN hkn)
    have heq := congrArg Prod.fst (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heq
    simpa only [heq] using hstep
  obtain ⟨b, hb, hblarge⟩ := hM.exists_gt ((F M).sup id)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  let n := max k j
  have hbn : b ∈ (q n).frontB := twoFrontMatchRun_monoB F hF N hN (Nat.le_max_right _ _) hj
  have hxgt : b < twoFrontMatchX (q n) :=
    (q n).separated b (Finset.mem_union_right _ hbn) _ (twoFrontMatchX_mem (q n))
  have hc := hcolors n (Nat.le_max_left _ _)
  have hx : twoFrontMatchX (q n) ∈ (q (n + 1)).frontB := by
    have heq := congrArg Prod.snd (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heq
    change _ ∈ (twoFrontMatchNext F hF (q n)).frontB
    rw [heq]
    simp only [hc.1, hc.2, matchingFrontStep]
    exact Finset.mem_insert_self _ _
  have hp := twoFrontMatchRun_predictB_at_X F hF N hN hM n hx
  rw [hc.2] at hp
  obtain ⟨_, i, hi, hxi⟩ := (finiteSetMatchingColor_before F M _).mp hp
  exact (not_lt_of_ge (Finset.le_sup (f := id) hi))
    (hblarge.trans (hxgt.trans hxi))

theorem twoFrontMatchRun_limitB_infinite : (M).Infinite := by
  by_contra hM
  have hMfin : (M).Finite := Set.not_infinite.mp hM
  have hL := twoFrontMatchRun_limitA_infinite F hF N hN
  obtain ⟨k, hk⟩ := monotone_finiteFront_limit_finite _
    (twoFrontMatchRun_monoB F hF N hN) hMfin
  have hcolors (n : ℕ) (hkn : k ≤ n) :
      (q n).colorA = .before ∧ (q n).colorB = .inside := by
    apply matchingFrontStep_holdB_of_no_new _ _ _ _ _ _
      (twoFrontMatchRun_X_not_frontB F hF N hN n)
      (twoFrontMatchRun_Y_not_frontB F hF N hN n)
    have hstep := (hk (n + 1)).trans (twoFrontMatchRun_monoB F hF N hN hkn)
    have heq := congrArg Prod.snd (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heq
    simpa only [heq] using hstep
  obtain ⟨b, hb, hblarge⟩ := hL.exists_gt ((F L).sup id)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  let n := max k j
  have hbn : b ∈ (q n).frontA := twoFrontMatchRun_monoA F hF N hN (Nat.le_max_right _ _) hj
  have hxgt : b < twoFrontMatchX (q n) :=
    (q n).separated b (Finset.mem_union_left _ hbn) _ (twoFrontMatchX_mem (q n))
  have hc := hcolors n (Nat.le_max_left _ _)
  have hx : twoFrontMatchX (q n) ∈ (q (n + 1)).frontA := by
    have heq := congrArg Prod.fst (twoFrontMatchNext_fronts F hF (q n))
    dsimp only at heq
    change _ ∈ (twoFrontMatchNext F hF (q n)).frontA
    rw [heq]
    simp only [hc.1, hc.2, matchingFrontStep]
    exact Finset.mem_insert_self _ _
  have hp := twoFrontMatchRun_predictA_at_X F hF N hN hL n hx
  rw [hc.1] at hp
  obtain ⟨_, i, hi, hxi⟩ := (finiteSetMatchingColor_before F L _).mp hp
  exact (not_lt_of_ge (Finset.le_sup (f := id) hi))
    (hblarge.trans (hxgt.trans hxi))

end Run

end SurveyStatements.P1
