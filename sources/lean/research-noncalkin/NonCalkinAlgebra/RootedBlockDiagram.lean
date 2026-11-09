import NonCalkinAlgebra.BlockRefinementEntries

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
universe u

/-- Finite block stages with a scalar root and unital block-diagonal transitions. -/
structure RootedBlockDiagram where
  Color : ℕ → Type u
  Row : ∀ n, Color n → Type u
  colorFinite : ∀ n, Finite (Color n)
  rowFinite : ∀ n c, Finite (Row n c)
  colorNonempty : ∀ n, Nonempty (Color n)
  rowNonempty : ∀ n c, Nonempty (Row n c)
  rootColorSubsingleton : Subsingleton (Color 0)
  rootRowSubsingleton : ∀ c, Subsingleton (Row 0 c)
  step : ∀ n, Refinement (Row n) (Row (n + 1))
  step_covers : ∀ n, Covers (step n)

attribute [instance] RootedBlockDiagram.colorFinite RootedBlockDiagram.rowFinite
  RootedBlockDiagram.colorNonempty RootedBlockDiagram.rowNonempty
  RootedBlockDiagram.rootColorSubsingleton RootedBlockDiagram.rootRowSubsingleton

namespace RootedBlockDiagram
variable (D : RootedBlockDiagram.{u})

def path (i j : ℕ) (h : i ≤ j) : Refinement (D.Row i) (D.Row j) :=
  Nat.leRecOn (C := fun k => Refinement (D.Row i) (D.Row k)) h
    (fun {k} f => f.trans (D.step k)) (identity (D.Row i))

@[simp] theorem path_self (i : ℕ) : D.path i i le_rfl = identity (D.Row i) :=
  Nat.leRecOn_self _

theorem path_succ (i j : ℕ) (h : i ≤ j) :
    D.path i (j + 1) h.step = (D.path i j h).trans (D.step j) :=
  Nat.leRecOn_succ h _

theorem path_read_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : Cell (D.Row k)) :
    (D.path i k (hij.trans hjk)).read x =
      ((D.path j k hjk).read x).bind (D.path i j hij).read := by
  induction k, hjk using Nat.le_induction with
  | base => simp [Option.bind_some]
  | succ k h ih =>
    rw [path_succ D i k (hij.trans h), path_succ D j k h,
      Refinement.read_trans, Refinement.read_trans]
    cases hx : (D.step k).read x with
    | none => rfl
    | some y => exact ih y

theorem path_covers (i j : ℕ) (h : i ≤ j) : Covers (D.path i j h) := by
  induction j, h using Nat.le_induction with
  | base => simpa only [path_self] using (identity_covers (P := D.Row i))
  | succ j h ih => rw [D.path_succ i j h]; exact covers_trans ih (D.step_covers j)

instance pathCopiesFinite (i j : ℕ) (h : i ≤ j) (c : D.Color j) :
    Finite ((D.path i j h).Copies c) :=
  finite_copies (D.path i j h) c

instance pathCopiesNonempty (i j : ℕ) (h : i ≤ j) (c : D.Color j) :
    Nonempty ((D.path i j h).Copies c) :=
  ⟨((D.path i j h).rows c).symm (Classical.choice inferInstance) |>.1⟩

theorem pathCopiesSubsingleton (c : D.Color 0) :
    Subsingleton ((D.path 0 0 le_rfl).Copies c) := by
  rw [path_self]
  exact inferInstanceAs (Subsingleton PUnit)

def EventuallyMixes : Prop :=
  ∀ i, ∃ j, ∃ h : i ≤ j, Mixes (D.path i j h)

end RootedBlockDiagram
end NonCalkinAlgebra.FiniteBlockRefinement
