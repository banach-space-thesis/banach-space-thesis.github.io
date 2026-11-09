import BanachIsometric.SignedSimplexFacetOrientation
import BanachIsometric.SingularPrismGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The affine columns used for the facet sign are the actual radial vector
and derivatives of the actual simplex face map, in the oriented coordinates
of `SignedSimplexCoordinates`. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Matrix

theorem signedFace_pushforward (n : ℕ) (i : Fin (n + 2)) (w : Fin (n + 1) → ℝ) :
    FunOnFinite.linearMap ℝ ℝ i.succAbove w = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) w := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · rw [FunOnFinite.linearMap_apply_apply, Fin.insertNth_apply_same]
    simp [Fin.succAbove_ne]
  · rw [FunOnFinite.linearMap_apply_apply, Fin.insertNth_apply_succAbove]
    have h : Finset.univ.filter (fun x : Fin (n + 1) => i.succAbove x = i.succAbove k) = {k} := by
      ext x
      simp
    rw [h, Finset.sum_singleton]

theorem signedFace_barycentric (n : ℕ) (i : Fin (n + 2)) (w : Simplex n) :
    (face i w).val = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) w.val :=
  signedFace_pushforward n i w.val

def signedSimplexDirectionLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := signedSimplexDirection n
  map_add' x y := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [signedSimplexDirection, Finset.sum_add_distrib, add_comm]
    · rfl
  map_smul' r x := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [signedSimplexDirection, ← Finset.mul_sum]
    · rfl

def signedTailLinear (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x j := x j.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def signedFacetSlope (n : ℕ) (i : Fin (n + 2)) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ((signedTailLinear (n + 1)).comp
    ((FunOnFinite.linearMap ℝ ℝ i.succAbove).comp (signedSimplexDirectionLinear n))).toContinuousLinearMap

def signedFacetVector (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => signedFacetChartMatrix n i x j 0

theorem signedFacetSlope_apply (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) (j : Fin (n + 1)) :
    signedFacetSlope n i x j = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (signedSimplexDirection n x) j.succ := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (signedSimplexDirection n x) j.succ = _
  rw [signedFace_pushforward]

theorem signedFacetVector_apply (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) (j : Fin (n + 1)) :
    signedFacetVector n i x j =
      Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (signedSimplexBarycentric n x) j.succ - signedFacetCenter n := by
  simp [signedFacetVector, signedFacetChartMatrix, Fin.succAbove_zero]

theorem signedFacetVector_affine (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    signedFacetVector n i x = signedFacetVector n i 0 + signedFacetSlope n i x := by
  have hb : signedSimplexBarycentric n x =
      signedSimplexBarycentric n 0 + signedSimplexDirection n x := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [signedSimplexDirection, sub_eq_add_neg]
    · simp [signedSimplexDirection]
  funext j
  simp only [signedFacetVector_apply, signedFacetSlope_apply, Pi.add_apply]
  simp only [← signedFace_pushforward, hb, map_add, Pi.add_apply]
  ring

theorem signedFacetVector_hasFDerivAt (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    HasFDerivAt (signedFacetVector n i) (signedFacetSlope n i) x := by
  have hf : signedFacetVector n i = fun y => signedFacetVector n i 0 + signedFacetSlope n i y :=
    funext (signedFacetVector_affine n i)
  rw [hf]
  exact (signedFacetSlope n i).hasFDerivAt.const_add _

theorem signedFacetChartMatrix_succ (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ)
    (a : Fin (n + 1)) (b : Fin n) :
    signedFacetChartMatrix n i x a b.succ = signedFacetSlope n i (Pi.single b 1) a := by
  simp [signedFacetChartMatrix, Fin.succAbove_zero, signedFacetSlope_apply]

end BanachIsometric.SingularPrism
