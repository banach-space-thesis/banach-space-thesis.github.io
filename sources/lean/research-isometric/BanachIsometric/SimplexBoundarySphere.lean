import BanachIsometric.SphereGenerator
import BanachIsometric.RawSingularChains
import Mathlib.Analysis.NormedSpace.Normalize

/-!
# The actual boundary-simplex sphere maps

The standard `(n+2)`-simplex is centered at its barycenter, expressed in
the last `n+2` coordinates, and radially projected onto the ACTUAL Euclidean
`(n+1)`-sphere. The formula is used only on its boundary: each omitted
coordinate proves nonvanishing. In particular, no extension of the sphere
map across the whole simplex is assumed.

These maps supply the faces of a canonical singular sphere cycle. This
module proves the actual shared-face identities, without claiming that
the resulting class generates homology or that Hurewicz is injective.
-/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology
open SphereGenerator
open NormedSpace

def simplexCenter (n : ℕ) : ℝ := 1 / (n + 3 : ℕ)

theorem simplexCenter_pos (n : ℕ) : 0 < simplexCenter n := by
  exact one_div_pos.mpr (by positivity)

def centeredSimplexVector (n : ℕ) :
    C(Simplex (n + 2), EuclideanSpace ℝ (Fin (n + 2))) where
  toFun w := WithLp.toLp 2 (fun j => w j.succ - simplexCenter n)
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 2) => ℝ)).comp
    exact continuous_pi fun j =>
      ((continuous_apply j.succ).comp continuous_subtype_val).sub continuous_const

@[simp] theorem centeredSimplexVector_apply (n : ℕ)
    (w : Simplex (n + 2)) (j : Fin (n + 2)) :
    centeredSimplexVector n w j = w j.succ - simplexCenter n := rfl

theorem centeredSimplexVector_eq_zero (n : ℕ) (w : Simplex (n + 2))
    (h : centeredSimplexVector n w = 0) : ∀ i, w i = simplexCenter n := by
  have ht : ∀ j : Fin (n + 2), w j.succ = simplexCenter n := by
    intro j
    have hj := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 2)) => v j) h
    exact sub_eq_zero.mp hj
  intro i
  induction i using Fin.cases with
  | zero =>
      have hs := stdSimplex.sum_eq_one w
      rw [Fin.sum_univ_succ] at hs
      simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hs
      dsimp [simplexCenter] at hs ⊢
      have hn : (n + 3 : ℝ) ≠ 0 := by positivity
      push_cast at hs ⊢
      field_simp at hs ⊢
      nlinarith
  | succ j => exact ht j

@[simp] theorem simplex_face_missing {n : ℕ} (i : Fin (n + 2)) (w : Simplex n) :
    face i w i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove w i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp

theorem centeredSimplexVector_face_ne_zero (n : ℕ) (i : Fin (n + 3))
    (w : Simplex (n + 1)) : centeredSimplexVector n (face i w) ≠ 0 := by
  intro h
  have hi := centeredSimplexVector_eq_zero n (face i w) h i
  rw [simplex_face_missing] at hi
  exact (simplexCenter_pos n).ne' hi.symm

def boundarySimplexSphereFace (n : ℕ) (i : Fin (n + 3)) :
    C(Simplex (n + 1), Sph (n + 1)) where
  toFun w := ⟨normalize (centeredSimplexVector n (face i w)),
    mem_sphere_zero_iff_norm.mpr
      (norm_normalize (centeredSimplexVector_face_ne_zero n i w))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hv := (centeredSimplexVector n).continuous.comp (face i).continuous
    exact (hv.norm.inv₀ fun w => norm_ne_zero_iff.mpr
      (centeredSimplexVector_face_ne_zero n i w)).smul hv

theorem boundarySimplexSphereFace_face (n : ℕ) (i j : Fin (n + 2)) (h : i ≤ j) :
    (boundarySimplexSphereFace n j.succ).comp (face i) =
      (boundarySimplexSphereFace n i.castSucc).comp (face j) := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  change normalize (centeredSimplexVector n (face j.succ (face i w))) =
    normalize (centeredSimplexVector n (face i.castSucc (face j w)))
  exact congrArg (fun u => normalize (centeredSimplexVector n u))
    (ContinuousMap.congr_fun (face_face i j h) w)

end BanachIsometric.SingularPrism
