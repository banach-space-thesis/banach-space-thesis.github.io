import NonCalkinAlgebra.FiniteBlockRefinement
import Mathlib.Data.Fintype.Pi

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
universe u

variable {ι : Type u}

/-- A dependent product with subsingleton coordinates outside a finite set is finite. -/
theorem finite_pi_of_finite_active {T : ι → Type u} [∀ i, Finite (T i)]
    (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (T i)) : Finite (∀ i, T i) := by
  refine Finite.of_injective (fun (x : ∀ i, T i) (i : s) => x i) ?_
  intro x y hxy
  funext i
  by_cases hi : i ∈ s
  · exact congrFun hxy ⟨i, hi⟩
  · letI := hs i hi
    exact Subsingleton.elim _ _

namespace Refinement
variable {C D : ι → Type u} {P : ∀ i, C i → Type u} {Q : ∀ i, D i → Type u}

/-- Multiplication of block multiplicities across coordinates, including
inactive singleton coordinates outside a finite set. -/
def pi (f : ∀ i, Refinement (P i) (Q i)) :
    Refinement (fun c : ∀ i, C i => ∀ i, P i (c i))
      (fun d : ∀ i, D i => ∀ i, Q i (d i)) where
  Copies d := ∀ i, (f i).Copies (d i)
  color d k i := (f i).color (d i) (k i)
  rows d :=
    { toFun := fun x i => (f i).rows (d i) ⟨x.1 i, x.2 i⟩
      invFun := fun y => ⟨fun i => ((f i).rows (d i)).symm (y i) |>.1,
        fun i => ((f i).rows (d i)).symm (y i) |>.2⟩
      left_inv := by
        intro x
        have h : (fun i => ((f i).rows (d i)).symm
            ((f i).rows (d i) ⟨x.1 i, x.2 i⟩)) = (fun i => ⟨x.1 i, x.2 i⟩) := by
          funext i
          exact Equiv.symm_apply_apply _ _
        exact congrArg (fun z : ∀ i, Σ k : (f i).Copies (d i), P i ((f i).color (d i) k) =>
          (⟨fun i => (z i).1, fun i => (z i).2⟩ :
            Σ k : ∀ i, (f i).Copies (d i), ∀ i, P i ((f i).color (d i) (k i)))) h
      right_inv := by
        intro y
        funext i
        exact Equiv.apply_symm_apply _ _ }

@[simp] theorem pi_rows_apply (f : ∀ i, Refinement (P i) (Q i))
    (d : ∀ i, D i) (k : (pi f).Copies d)
    (x : ∀ i, P i ((pi f).color d k i)) (i : ι) :
    (pi f).rows d ⟨k, x⟩ i = (f i).rows (d i) ⟨k i, x i⟩ := rfl

end Refinement
end NonCalkinAlgebra.FiniteBlockRefinement
