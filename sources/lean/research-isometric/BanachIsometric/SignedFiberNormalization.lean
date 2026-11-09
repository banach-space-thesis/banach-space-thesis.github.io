import BanachIsometric.SignedFiberCount
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Orientation normalization of actual signed fiber counts

Linear equivalences have their expected determinant sign, and the identity has
count one precisely on the source. These are statements about the actual fiber
count, proved directly, not axioms specifying a proposed degree theory.
-/

namespace BanachIsometric

open Set Function
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem signedFiberSum_linearEquiv (A : E ≃L[ℝ] E) (s : Set E) (y : E) :
    signedFiberSum A (fun _ => (A : E →L[ℝ] E)) s y =
      if A.symm y ∈ s then (SignType.sign (A : E →L[ℝ] E).det : ℝ) else 0 := by
  classical
  have hxy (x : E) : A x = y ↔ x = A.symm y := by
    constructor
    · intro hx
      exact A.injective (hx.trans (A.apply_symm_apply y).symm)
    · intro hx
      rw [hx, A.apply_symm_apply]
  have hp : {x : E | x ∈ s ∧ A x = y} =
      if A.symm y ∈ s then {A.symm y} else ∅ := by
    ext x
    by_cases hx : x = A.symm y
    · subst x
      simp
    · by_cases hs : A.symm y ∈ s <;> simp [hxy, hx, hs]
  unfold signedFiberSum
  change (∑' x : {x : E | x ∈ s ∧ A x = y},
    (SignType.sign (A : E →L[ℝ] E).det : ℝ)) = _
  rw [hp]
  by_cases hs : A.symm y ∈ s <;> simp [hs]

theorem signedFiberCount_linearEquiv (A : E ≃L[ℝ] E) (s : Set E) (y : E) :
    signedFiberCount A (fun _ => (A : E →L[ℝ] E)) s y =
      if A.symm y ∈ s then (SignType.sign (A : E →L[ℝ] E).det : ℤ) else 0 := by
  classical
  have hfin : {x : E | x ∈ s ∧ A x = y}.Finite := by
    apply (finite_singleton (A.symm y)).subset
    intro x hx
    exact A.injective (hx.2.trans (A.apply_symm_apply y).symm)
  have hcast := signedFiberSum_eq_coe_signedFiberCount A
    (fun _ => (A : E →L[ℝ] E)) s y hfin
  rw [signedFiberSum_linearEquiv] at hcast
  have hh : ((signedFiberCount A (fun _ => (A : E →L[ℝ] E)) s y : ℤ) : ℝ) =
      ((if A.symm y ∈ s then (SignType.sign (A : E →L[ℝ] E).det : ℤ) else 0) : ℝ) := by
    simpa only [Int.cast_ite, SignType.intCast_cast, Int.cast_zero] using hcast.symm
  exact_mod_cast hh

theorem signedFiberCount_id (s : Set E) (y : E) :
    signedFiberCount (id : E → E) (fun _ => ContinuousLinearMap.id ℝ E) s y =
      if y ∈ s then 1 else 0 := by
  have hdet : (ContinuousLinearMap.id ℝ E).det = 1 := by
    change LinearMap.det (1 : Module.End ℝ E) = 1
    exact map_one (LinearMap.det : Module.End ℝ E →* ℝ)
  simpa [hdet] using signedFiberCount_linearEquiv (ContinuousLinearEquiv.refl ℝ E) s y

end BanachIsometric
