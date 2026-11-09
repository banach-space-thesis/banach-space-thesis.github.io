import NonCalkinAlgebra.TraceWeightRefinement
import Mathlib.Algebra.Star.Prod
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TraceWeightRefinement
open Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Blocks (m n : ℕ) := Mat m × Mat n

def sumIndexBlock (m n : ℕ) :
    Blocks m n →ₐ[ℂ] Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ where
  toFun p := fromBlocks p.1 0 0 p.2
  map_zero' := by
    ext i j
    cases i <;> cases j <;> rfl
  map_one' := fromBlocks_one
  map_add' := by
    intro p q
    ext i j
    cases i <;> cases j <;> simp [fromBlocks]
  map_mul' := by
    intro p q
    simp [fromBlocks_multiply]
  commutes' := by
    intro z
    ext i j
    cases i <;> cases j <;> simp [fromBlocks, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_apply]

/-- Block sum with the usual finite index set, as a unital *-algebra map. -/
def blockSum (m n : ℕ) : Blocks m n →⋆ₐ[ℂ] Mat (m + n) where
  __ := (reindexAlgEquiv ℂ ℂ finSumFinEquiv).toAlgHom.comp (sumIndexBlock m n)
  map_star' := by
    intro p
    apply Matrix.ext
    intro i j
    change fromBlocks (star p.1) 0 0 (star p.2)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
      star (fromBlocks p.1 0 0 p.2 (finSumFinEquiv.symm j) (finSumFinEquiv.symm i))
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      simp [fromBlocks, Matrix.star_eq_conjTranspose]

theorem blockSum_injective (m n : ℕ) : Function.Injective (blockSum m n) := by
  intro p q hpq
  have hb : fromBlocks p.1 0 0 p.2 = fromBlocks q.1 0 0 q.2 := by
    apply (reindexAlgEquiv ℂ ℂ (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n))).injective
    exact hpq
  apply Prod.ext
  · exact congrArg Matrix.toBlocks₁₁ hb
  · exact congrArg Matrix.toBlocks₂₂ hb

@[simp] theorem trace_blockSum {m n : ℕ} (p : Blocks m n) :
    Matrix.trace (blockSum m n p) = Matrix.trace p.1 + Matrix.trace p.2 := by
  change (∑ i : Fin (m+n), fromBlocks p.1 0 0 p.2
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm i)) = _
  calc
    _ = ∑ j : Fin m ⊕ Fin n, fromBlocks p.1 0 0 p.2 j j :=
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n)).symm.sum_comp
        (fun j => fromBlocks p.1 0 0 p.2 j j)
    _ = _ := by simp [Matrix.trace, Fintype.sum_sum_type, fromBlocks]

def leftEmbedding (m n : ℕ) : Blocks m n →⋆ₐ[ℂ] Blocks m (m + n) where
  __ := (AlgHom.fst ℂ (Mat m) (Mat n)).prod (blockSum m n).toAlgHom
  map_star' := fun p => Prod.ext rfl (map_star (blockSum m n) p)

def rightEmbedding (m n : ℕ) : Blocks m n →⋆ₐ[ℂ] Blocks (m + n) n where
  __ := (blockSum m n).toAlgHom.prod (AlgHom.snd ℂ (Mat m) (Mat n))
  map_star' := fun p => Prod.ext (map_star (blockSum m n) p) rfl

theorem leftEmbedding_injective (m n : ℕ) : Function.Injective (leftEmbedding m n) :=
  fun _ _ h => blockSum_injective m n (congrArg Prod.snd h)

theorem rightEmbedding_injective (m n : ℕ) : Function.Injective (rightEmbedding m n) :=
  fun _ _ h => blockSum_injective m n (congrArg Prod.fst h)

variable {R : Subring ℝ}

def weightedTrace (s : State R) (p : Blocks s.leftDim s.rightDim) : ℂ :=
  (s.leftWeight : ℂ) * Matrix.trace p.1 + (s.rightWeight : ℂ) * Matrix.trace p.2

theorem weightedTrace_one (s : State R) : weightedTrace s 1 = 1 := by
  simp only [weightedTrace, Prod.fst_one, Prod.snd_one, Matrix.trace_one, Fintype.card_fin]
  exact_mod_cast (by simpa only [mul_comm] using s.normalized :
    s.leftWeight * (s.leftDim : ℝ) + s.rightWeight * (s.rightDim : ℝ) = 1)

theorem weightedTrace_mul_comm (s : State R) (p q : Blocks s.leftDim s.rightDim) :
    weightedTrace s (p * q) = weightedTrace s (q * p) := by
  simp only [weightedTrace, Prod.fst_mul, Prod.snd_mul]
  rw [Matrix.trace_mul_comm p.1 q.1, Matrix.trace_mul_comm p.2 q.2]

theorem weightedTrace_left (s : State R) (h : s.rightWeight < s.leftWeight)
    (p : Blocks s.leftDim s.rightDim) :
    weightedTrace (s.subtractLeft h) (leftEmbedding s.leftDim s.rightDim p) =
      weightedTrace s p := by
  change ((s.leftWeight - s.rightWeight : ℝ) : ℂ) * Matrix.trace p.1 +
      (s.rightWeight : ℂ) * Matrix.trace (blockSum s.leftDim s.rightDim p) = _
  rw [trace_blockSum, Complex.ofReal_sub]
  unfold weightedTrace
  ring

theorem weightedTrace_right (s : State R) (h : s.leftWeight < s.rightWeight)
    (p : Blocks s.leftDim s.rightDim) :
    weightedTrace (s.subtractRight h) (rightEmbedding s.leftDim s.rightDim p) =
      weightedTrace s p := by
  change (s.leftWeight : ℂ) * Matrix.trace (blockSum s.leftDim s.rightDim p) +
      ((s.rightWeight - s.leftWeight : ℝ) : ℂ) * Matrix.trace p.2 = _
  rw [trace_blockSum, Complex.ofReal_sub]
  unfold weightedTrace
  ring

end NonCalkinAlgebra.TraceWeightRefinement
