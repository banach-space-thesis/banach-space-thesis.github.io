import BanachIsometric.VectorChainSplitting
import Mathlib.Tactic.Abel

/-! The chosen vector-space sections give actual degree-one contraction maps.
Their boundary equations are proved in degree zero and every positive degree.
The homology projection and inclusion are actual chain maps. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting

variable {K : Type*} [Field K] (C : ℕ → ModuleCat.{u} K)
  (d : ∀ n, C (n + 1) →ₗ[K] C n)
  (hd : ∀ n, (d n).comp (d (n + 1)) = 0)

def boundaryRemainder (n : ℕ) : C n →ₗ[K] boundaries C d hd n :=
  (cycleProjection C d hd n - (homologySection C d hd n).comp
    (homologyProjection C d hd n)).codRestrict (boundaries C d hd n) (by
      intro x
      apply (Submodule.Quotient.mk_eq_zero (boundaries C d hd n)).mp
      change (boundaries C d hd n).mkQ
        (cycleProjection C d hd n x - homologySection C d hd n (homologyProjection C d hd n x)) = 0
      rw [map_sub, quotient_homologySection]
      exact sub_self _)

def contraction (n : ℕ) : C n →ₗ[K] C (n + 1) :=
  (boundaryLift C d hd n).comp (boundaryRemainder C d hd n)

theorem differential_contraction (n : ℕ) (x : C n) :
    d n (contraction C d hd n x) =
      (cycleProjection C d hd n x).val -
        homologyInclusion C d hd n (homologyProjection C d hd n x) :=
  differential_boundaryLift C d hd n (boundaryRemainder C d hd n x)

theorem cycleProjection_boundary (n : ℕ) (x : C (n + 1)) :
    cycleProjection C d hd n (d n x) = boundaryMap C d hd n x :=
  cycleProjection_cycle C d hd n (boundaryMap C d hd n x)

theorem homologyProjection_boundary (n : ℕ) (x : C (n + 1)) :
    homologyProjection C d hd n (d n x) = 0 := by
  change (boundaries C d hd n).mkQ (cycleProjection C d hd n (d n x)) = 0
  rw [cycleProjection_boundary]
  exact (Submodule.Quotient.mk_eq_zero (boundaries C d hd n)).mpr ⟨x, rfl⟩

theorem differential_homologyInclusion (n : ℕ) (a : Homology C d hd (n + 1)) :
    d n (homologyInclusion C d hd (n + 1) a) = 0 :=
  (homologySection C d hd (n + 1) a).property

theorem boundaryRemainder_boundary (n : ℕ) (x : C (n + 1)) :
    boundaryRemainder C d hd n (d n x) = (boundaryMap C d hd n).rangeRestrict x := by
  apply Subtype.ext
  change cycleProjection C d hd n (d n x) -
    homologySection C d hd n (homologyProjection C d hd n (d n x)) = boundaryMap C d hd n x
  rw [homologyProjection_boundary, map_zero, sub_zero, cycleProjection_boundary]

theorem contraction_boundary (n : ℕ) (x : C (n + 1)) :
    contraction C d hd n (d n x) =
      boundaryLift C d hd n ((boundaryMap C d hd n).rangeRestrict x) := by
  change boundaryLift C d hd n (boundaryRemainder C d hd n (d n x)) = _
  rw [boundaryRemainder_boundary]

theorem contraction_zero_identity (x : C 0) :
    d 0 (contraction C d hd 0 x) =
      x - homologyInclusion C d hd 0 (homologyProjection C d hd 0 x) :=
  differential_contraction C d hd 0 x

theorem contraction_succ_identity (n : ℕ) (x : C (n + 1)) :
    d (n + 1) (contraction C d hd (n + 1) x) + contraction C d hd n (d n x) =
      x - homologyInclusion C d hd (n + 1) (homologyProjection C d hd (n + 1) x) := by
  rw [differential_contraction, contraction_boundary, cycleProjection_succ]
  abel

end BanachIsometric.VectorChainSplitting
