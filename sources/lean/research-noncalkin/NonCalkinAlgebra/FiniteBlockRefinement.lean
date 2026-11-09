import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
open Matrix

universe u
variable {C D E : Type u} {P : C → Type u} {Q : D → Type u} {R : E → Type u}

/-- Each target block is the direct sum of specified copies of source blocks. -/
structure Refinement (P : C → Type u) (Q : D → Type u) where
  Copies : D → Type u
  color : ∀ d, Copies d → C
  rows : ∀ d, (Σ k : Copies d, P (color d k)) ≃ Q d

abbrev Blocks (P : C → Type u) := ∀ c, Matrix (P c) (P c) ℂ

namespace Refinement
variable [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
variable [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
variable (f : Refinement P Q) [∀ d, Fintype (f.Copies d)]

private def duplicate (d : D) :
    Blocks P →+* (∀ k : f.Copies d, Matrix (P (f.color d k)) (P (f.color d k)) ℂ) where
  toFun x k := x (f.color d k)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

open Classical in
def blockMap (d : D) : Blocks P →⋆ₐ[ℂ] Matrix (Q d) (Q d) ℂ where
  __ := ((Matrix.reindexAlgEquiv ℂ ℂ (f.rows d)).toAlgHom.toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun k => P (f.color d k)) ℂ)).comp (f.duplicate d)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change Matrix.reindex (f.rows d) (f.rows d)
        (Matrix.blockDiagonal' (fun k => z • (1 : Matrix (P (f.color d k)) _ ℂ))) = z • 1
    rw [show (fun k : f.Copies d => z • (1 : Matrix (P (f.color d k)) _ ℂ)) =
      z • 1 by rfl, Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one]
    change (Matrix.reindexAlgEquiv ℂ ℂ (f.rows d)) (z • 1) = z • 1
    rw [map_smul, map_one]
  map_star' x := by
    apply Matrix.ext
    intro a b
    obtain ⟨⟨k, i⟩, rfl⟩ := (f.rows d).surjective a
    obtain ⟨⟨l, j⟩, rfl⟩ := (f.rows d).surjective b
    change Matrix.blockDiagonal' (fun k => star (x (f.color d k)))
        ((f.rows d).symm (f.rows d ⟨k, i⟩))
        ((f.rows d).symm (f.rows d ⟨l, j⟩)) =
      star (Matrix.blockDiagonal' (fun k => x (f.color d k))
        ((f.rows d).symm (f.rows d ⟨l, j⟩))
        ((f.rows d).symm (f.rows d ⟨k, i⟩)))
    simp only [Equiv.symm_apply_apply]
    by_cases h : k = l
    · subst l
      simp [Matrix.star_eq_conjTranspose]
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ h,
        Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm h), star_zero]

/-- Apply the same block refinement in each target summand. -/
def hom : Blocks P →⋆ₐ[ℂ] Blocks Q where
  toFun x d := f.blockMap d x
  map_zero' := funext fun d => map_zero (f.blockMap d)
  map_one' := funext fun d => map_one (f.blockMap d)
  map_add' x y := funext fun d => map_add (f.blockMap d) x y
  map_mul' x y := funext fun d => map_mul (f.blockMap d) x y
  commutes' z := funext fun d => (f.blockMap d).commutes z
  map_star' x := funext fun d => map_star (f.blockMap d) x

theorem hom_apply_same (x : Blocks P) (d : D) (k : f.Copies d)
    (i j : P (f.color d k)) :
    f.hom x d (f.rows d ⟨k, i⟩) (f.rows d ⟨k, j⟩) = x (f.color d k) i j := by
  classical
  change Matrix.blockDiagonal' (fun k => x (f.color d k))
    ((f.rows d).symm (f.rows d ⟨k, i⟩)) ((f.rows d).symm (f.rows d ⟨k, j⟩)) = _
  simp only [Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]

theorem hom_apply_ne (x : Blocks P) (d : D) {k l : f.Copies d}
    (h : k ≠ l) (i : P (f.color d k)) (j : P (f.color d l)) :
    f.hom x d (f.rows d ⟨k, i⟩) (f.rows d ⟨l, j⟩) = 0 := by
  classical
  change Matrix.blockDiagonal' (fun k => x (f.color d k))
    ((f.rows d).symm (f.rows d ⟨k, i⟩)) ((f.rows d).symm (f.rows d ⟨l, j⟩)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h]

theorem hom_injective (hc : ∀ c, ∃ d k, f.color d k = c) :
    Function.Injective f.hom := by
  intro x y h
  funext c
  obtain ⟨d, k, rfl⟩ := hc c
  ext i j
  have hentry := congrFun (congrFun (congrFun h d) (f.rows d ⟨k, i⟩)) (f.rows d ⟨k, j⟩)
  simpa only [f.hom_apply_same] using hentry

theorem trace_hom (x : Blocks P) (d : D) :
    (f.hom x d).trace = ∑ k : f.Copies d, (x (f.color d k)).trace := by
  change (∑ a : Q d, f.hom x d a a) = _
  rw [← (f.rows d).sum_comp (fun a => f.hom x d a a), Fintype.sum_sigma]
  simp only [hom_apply_same, Matrix.trace, Matrix.diag_apply]

end Refinement
end NonCalkinAlgebra.FiniteBlockRefinement
