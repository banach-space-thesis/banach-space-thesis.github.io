import NonCalkinAlgebra.RootedBlockDiagram
import NonCalkinAlgebra.TraceStageGrowth
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.TraceWeightRefinement
open NonCalkinAlgebra.FiniteBlockRefinement

private def boolSigmaEquiv (P : Bool → Type) : (Σ b, P b) ≃ P false ⊕ P true where
  toFun
    | ⟨false, x⟩ => Sum.inl x
    | ⟨true, x⟩ => Sum.inr x
  invFun
    | Sum.inl x => ⟨false, x⟩
    | Sum.inr x => ⟨true, x⟩
  left_inv := by rintro ⟨(_ | _), _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

def TwoRows (m n : ℕ) : Bool → Type
  | false => Fin m
  | true => Fin n

def leftRefinement (m n : ℕ) : Refinement (TwoRows m n) (TwoRows m (m+n)) where
  Copies
    | false => PUnit
    | true => Bool
  color
    | false, _ => false
    | true, b => b
  rows
    | false => (identity (TwoRows m n)).rows false
    | true => (boolSigmaEquiv (TwoRows m n)).trans finSumFinEquiv

def rightRefinement (m n : ℕ) : Refinement (TwoRows m n) (TwoRows (m+n) n) where
  Copies
    | false => Bool
    | true => PUnit
  color
    | false, b => b
    | true, _ => true
  rows
    | false => (boolSigmaEquiv (TwoRows m n)).trans finSumFinEquiv
    | true => (identity (TwoRows m n)).rows true

private theorem left_covers (m n : ℕ) : Covers (leftRefinement m n) :=
  fun c => ⟨true, c, rfl⟩

private theorem right_covers (m n : ℕ) : Covers (rightRefinement m n) :=
  fun c => ⟨false, c, rfl⟩

private theorem left_right_mixes (m n : ℕ) :
    Mixes ((leftRefinement m n).trans (rightRefinement m (m+n))) := by
  intro c d
  cases d
  · exact ⟨⟨true, c⟩, rfl⟩
  · exact ⟨⟨PUnit.unit, c⟩, rfl⟩

private theorem right_left_mixes (m n : ℕ) :
    Mixes ((rightRefinement m n).trans (leftRefinement (m+n) n)) := by
  intro c d
  cases d
  · exact ⟨⟨PUnit.unit, c⟩, rfl⟩
  · exact ⟨⟨false, c⟩, rfl⟩

variable {R : Subring ℝ}
abbrev StateRows (s : State R) := TwoRows s.leftDim s.rightDim


structure ParameterEdge (s : State R) where
  target : State R
  refinement : Refinement (StateRows s) (StateRows target)

def parameterEdge (s : State R) : ParameterEdge s :=
  if h : s.rightWeight < s.leftWeight then
    ⟨s.subtractLeft h, leftRefinement s.leftDim s.rightDim⟩
  else
    ⟨s.subtractRight (lt_of_le_of_ne (le_of_not_gt h) s.weights_ne),
      rightRefinement s.leftDim s.rightDim⟩

theorem parameterEdge_target (s : State R) : (parameterEdge s).target = s.step := by
  by_cases h : s.rightWeight < s.leftWeight <;> simp [parameterEdge, State.step, h]

theorem parameterEdge_covers (s : State R) : Covers (parameterEdge s).refinement := by
  by_cases h : s.rightWeight < s.leftWeight
  · have he : parameterEdge s =
      ⟨s.subtractLeft h, leftRefinement s.leftDim s.rightDim⟩ := dif_pos h
    rw [he]
    exact left_covers _ _
  · have he : parameterEdge s =
      ⟨s.subtractRight (lt_of_le_of_ne (le_of_not_gt h) s.weights_ne),
        rightRefinement s.leftDim s.rightDim⟩ := dif_neg h
    rw [he]
    exact right_covers _ _

theorem parameterEdge_twice_mixes (s : State R)
    (hs : (s.rightWeight < s.leftWeight) ↔
      ¬ ((parameterEdge s).target.rightWeight < (parameterEdge s).target.leftWeight)) :
    Mixes ((parameterEdge s).refinement.trans
      (parameterEdge (parameterEdge s).target).refinement) := by
  by_cases h : s.rightWeight < s.leftWeight
  · have he : parameterEdge s =
      ⟨s.subtractLeft h, leftRefinement s.leftDim s.rightDim⟩ := dif_pos h
    have h' := hs.mp h
    rw [he] at h' ⊢
    have ht : parameterEdge (s.subtractLeft h) =
        ⟨(s.subtractLeft h).subtractRight
            (lt_of_le_of_ne (le_of_not_gt h') (s.subtractLeft h).weights_ne),
          rightRefinement (s.subtractLeft h).leftDim (s.subtractLeft h).rightDim⟩ := dif_neg h'
    rw [ht]
    exact left_right_mixes _ _
  · have hR := lt_of_le_of_ne (le_of_not_gt h) s.weights_ne
    have he : parameterEdge s =
      ⟨s.subtractRight hR, rightRefinement s.leftDim s.rightDim⟩ := dif_neg h
    have h' := Classical.not_not.mp (fun h₂ => h (hs.mpr h₂))
    rw [he] at h' ⊢
    have ht : parameterEdge (s.subtractRight hR) =
        ⟨(s.subtractRight hR).subtractLeft h',
          leftRefinement (s.subtractRight hR).leftDim (s.subtractRight hR).rightDim⟩ := dif_pos h'
    rw [ht]
    exact right_left_mixes _ _

def parameterStates (s : State R) : ℕ → State R
  | 0 => s
  | n + 1 => (parameterEdge (parameterStates s n)).target

theorem parameterStates_eq_stages (s : State R) (n : ℕ) :
    parameterStates s n = s.stages n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parameterStates, parameterEdge_target, ih, State.stages_succ]

def ParamColors : ℕ → Type
  | 0 => Unit
  | _ + 1 => Bool

def ParamRows (s : State R) : ∀ n, ParamColors n → Type
  | 0, _ => Unit
  | n + 1, c => StateRows (parameterStates s n) c

private def rootStep (s : State R) (hl : s.leftDim = 1) (hr : s.rightDim = 1) :
    Refinement (ParamRows s 0) (ParamRows s 1) where
  Copies _ := Unit
  color _ _ := ()
  rows c := by
    letI : Unique (Σ _ : Unit, Unit) := ⟨⟨(), ()⟩, fun ⟨⟨⟩, ⟨⟩⟩ => rfl⟩
    cases c
    · change (Σ _ : Unit, Unit) ≃ Fin s.leftDim
      rw [hl]
      exact Equiv.ofUnique _ _
    · change (Σ _ : Unit, Unit) ≃ Fin s.rightDim
      rw [hr]
      exact Equiv.ofUnique _ _

private def paramStep (s : State R) (hl : s.leftDim = 1) (hr : s.rightDim = 1) :
    ∀ n, Refinement (ParamRows s n) (ParamRows s (n + 1))
  | 0 => rootStep s hl hr
  | n + 1 => (parameterEdge (parameterStates s n)).refinement

def parameterDiagram (s : State R) (hl : s.leftDim = 1) (hr : s.rightDim = 1) :
    RootedBlockDiagram where
  Color := ParamColors
  Row := ParamRows s
  colorFinite n := by
    cases n
    · exact inferInstanceAs (Finite Unit)
    · exact inferInstanceAs (Finite Bool)
  rowFinite n c := by
    cases n with
    | zero => exact inferInstanceAs (Finite Unit)
    | succ n => cases c <;> exact inferInstanceAs (Finite (Fin _))
  colorNonempty n := by
    cases n
    · exact inferInstanceAs (Nonempty Unit)
    · exact inferInstanceAs (Nonempty Bool)
  rowNonempty n c := by
    cases n with
    | zero => exact inferInstanceAs (Nonempty Unit)
    | succ n =>
      cases c
      · exact ⟨⟨0, (parameterStates s n).leftDim_pos⟩⟩
      · exact ⟨⟨0, (parameterStates s n).rightDim_pos⟩⟩
  rootColorSubsingleton := inferInstanceAs (Subsingleton Unit)
  rootRowSubsingleton _ := inferInstanceAs (Subsingleton Unit)
  step := paramStep s hl hr
  step_covers n := by
    cases n with
    | zero => exact fun ⟨⟩ => ⟨false, (), rfl⟩
    | succ n => exact parameterEdge_covers (parameterStates s n)

private theorem exists_adjacent_switch (s : State R) (n : ℕ) :
    ∃ k ≥ n, ((s.stages k).rightWeight < (s.stages k).leftWeight) ↔
      ¬ ((s.stages (k+1)).rightWeight < (s.stages (k+1)).leftWeight) := by
  classical
  let left (k : ℕ) : Prop := (s.stages k).rightWeight < (s.stages k).leftWeight
  change ∃ k ≥ n, left k ↔ ¬ left (k + 1)
  by_contra! h
  have hs (k : ℕ) (hk : n ≤ k) : left k ↔ left (k + 1) := by
    have hno := h k hk
    tauto
  have hc (k : ℕ) (hk : n ≤ k) : left n ↔ left k := by
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact ih.trans (hs k hk)
  obtain ⟨kl, hkl, hleft⟩ := s.exists_later_left n
  obtain ⟨kr, hkr, hright⟩ := s.exists_later_right n
  exact (not_lt_of_gt hright) ((hc kr hkr).mp ((hc kl hkl).mpr hleft))

theorem parameterDiagram_mixes (s : State R) (hl : s.leftDim = 1) (hr : s.rightDim = 1) :
    (parameterDiagram s hl hr).EventuallyMixes := by
  let D := parameterDiagram s hl hr
  intro n
  cases n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    rw [D.path_self]
    exact fun ⟨⟩ ⟨⟩ => ⟨PUnit.unit, rfl⟩
  | succ n =>
    obtain ⟨k, hnk, hswitch⟩ := exists_adjacent_switch s n
    have hle : n + 1 ≤ k + 1 := Nat.succ_le_succ hnk
    refine ⟨k + 3, hle.step.step, ?_⟩
    rw [D.path_succ (n+1) (k+2) hle.step, D.path_succ (n+1) (k+1) hle]
    intro c e
    obtain ⟨d, k₀, hk₀⟩ := D.path_covers (n+1) (k+1) hle c
    have hswitch' : ((parameterStates s k).rightWeight < (parameterStates s k).leftWeight) ↔
        ¬ ((parameterStates s (k+1)).rightWeight < (parameterStates s (k+1)).leftWeight) := by
      simpa only [parameterStates_eq_stages] using hswitch
    obtain ⟨⟨k₂, k₁⟩, hk⟩ := parameterEdge_twice_mixes (parameterStates s k) hswitch' d e
    change (D.step (k+1)).color ((D.step (k+2)).color e k₂) k₁ = d at hk
    subst d
    exact ⟨⟨k₂, ⟨k₁, k₀⟩⟩, hk₀⟩

end NonCalkinAlgebra.TraceWeightRefinement
