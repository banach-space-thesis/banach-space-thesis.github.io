import NonCalkinAlgebra.TraceMatrixRefinement
import Mathlib.Order.DirectedInverseSystem

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TraceWeightRefinement
variable {R : Subring ℝ}

abbrev Stage (s : State R) := Blocks s.leftDim s.rightDim

/-- A single weighted refinement with its actual injective transition. -/
structure Edge (s : State R) where
  target : State R
  map : Stage s →⋆ₐ[ℂ] Stage target
  injective : Function.Injective map
  trace_map : ∀ x, weightedTrace target (map x) = weightedTrace s x

def edge (s : State R) : Edge s :=
  if h : s.rightWeight < s.leftWeight then
    ⟨s.subtractLeft h, leftEmbedding s.leftDim s.rightDim,
      leftEmbedding_injective _ _, weightedTrace_left s h⟩
  else
    let h' := lt_of_le_of_ne (le_of_not_gt h) s.weights_ne
    ⟨s.subtractRight h', rightEmbedding s.leftDim s.rightDim,
      rightEmbedding_injective _ _, weightedTrace_right s h'⟩

@[simp] theorem edge_target (s : State R) : (edge s).target = s.step := by
  by_cases h : s.rightWeight < s.leftWeight <;> simp [edge, State.step, h]

def matrixStates (s : State R) : ℕ → State R
  | 0 => s
  | n + 1 => (edge (matrixStates s n)).target

@[simp] theorem matrixStates_eq_stages (s : State R) (n : ℕ) :
    matrixStates s n = s.stages n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (edge (matrixStates s n)).target = (s.stages n).step
    rw [edge_target, ih]

abbrev MatrixStage (s : State R) (n : ℕ) := Stage (matrixStates s n)

def next (s : State R) (n : ℕ) : MatrixStage s n →⋆ₐ[ℂ] MatrixStage s (n + 1) :=
  (edge (matrixStates s n)).map

def connecting (s : State R) (i j : ℕ) (h : i ≤ j) :
    MatrixStage s i →⋆ₐ[ℂ] MatrixStage s j :=
  Nat.leRecOn (C := fun n => MatrixStage s i →⋆ₐ[ℂ] MatrixStage s n) h
    (fun {n} g => (next s n).comp g) (StarAlgHom.id ℂ (MatrixStage s i))

@[simp] theorem connecting_self (s : State R) (i : ℕ) :
    connecting s i i le_rfl = StarAlgHom.id ℂ (MatrixStage s i) :=
  Nat.leRecOn_self _

theorem connecting_succ (s : State R) (i j : ℕ) (h : i ≤ j) :
    connecting s i (j + 1) h.step = (next s j).comp (connecting s i j h) :=
  Nat.leRecOn_succ h _

instance matrixDirectedSystem (s : State R) :
    DirectedSystem (MatrixStage s) (connecting s · · ·) where
  map_self := by
    intro i x
    rw [connecting_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    induction k, hjk using Nat.le_induction with
    | base => rw [connecting_self]; rfl
    | succ k hjk ih =>
      rw [connecting_succ s j k hjk, connecting_succ s i k (hij.trans hjk)]
      change next s k (connecting s j k hjk (connecting s i j hij x)) =
        next s k (connecting s i k (hij.trans hjk) x)
      rw [ih]

theorem connecting_injective (s : State R) (i j : ℕ) (h : i ≤ j) :
    Function.Injective (connecting s i j h) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [connecting_self]
    exact fun _ _ eq => eq
  | succ j h ih =>
    rw [connecting_succ s i j h]
    exact (edge (matrixStates s j)).injective.comp ih

theorem weightedTrace_connecting (s : State R) (i j : ℕ) (h : i ≤ j)
    (x : MatrixStage s i) :
    weightedTrace (matrixStates s j) (connecting s i j h x) =
      weightedTrace (matrixStates s i) x := by
  induction j, h using Nat.le_induction with
  | base => rw [connecting_self]; rfl
  | succ j h ih =>
    rw [connecting_succ s i j h]
    exact ((edge (matrixStates s j)).trace_map (connecting s i j h x)).trans ih

end NonCalkinAlgebra.TraceWeightRefinement
