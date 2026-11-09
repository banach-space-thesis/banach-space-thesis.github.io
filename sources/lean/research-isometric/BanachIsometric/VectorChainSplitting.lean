import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual choices of linear sections split a nonnegative chain complex of
vector spaces. Degree-zero cycles are the whole degree-zero space. No finite
dimension or splitting hypothesis is imposed. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting

variable {K : Type*} [Field K] (C : ℕ → ModuleCat.{u} K)
  (d : ∀ n, C (n + 1) →ₗ[K] C n)
  (hd : ∀ n, (d n).comp (d (n + 1)) = 0)

def cycles : (n : ℕ) → Submodule K (C n)
  | 0 => ⊤
  | n + 1 => LinearMap.ker (d n)

def boundaryMap (n : ℕ) : C (n + 1) →ₗ[K] cycles C d n :=
  (d n).codRestrict (cycles C d n) (by
    intro x
    cases n with
    | zero => trivial
    | succ n => exact LinearMap.congr_fun (hd n) x)

abbrev boundaries (n : ℕ) := LinearMap.range (boundaryMap C d hd n)
abbrev Homology (n : ℕ) := cycles C d n ⧸ boundaries C d hd n

def boundaryLift (n : ℕ) : boundaries C d hd n →ₗ[K] C (n + 1) :=
  Classical.choose ((boundaryMap C d hd n).rangeRestrict.exists_rightInverse_of_surjective
    (boundaryMap C d hd n).range_rangeRestrict)

theorem boundaryMap_boundaryLift (n : ℕ) (b : boundaries C d hd n) :
    boundaryMap C d hd n (boundaryLift C d hd n b) = b.val := by
  have h := LinearMap.congr_fun
    (Classical.choose_spec ((boundaryMap C d hd n).rangeRestrict.exists_rightInverse_of_surjective
      (boundaryMap C d hd n).range_rangeRestrict)) b
  exact congrArg Subtype.val h

theorem differential_boundaryLift (n : ℕ) (b : boundaries C d hd n) :
    d n (boundaryLift C d hd n b) = b.val.val :=
  congrArg Subtype.val (boundaryMap_boundaryLift C d hd n b)

def cycleProjection : (n : ℕ) → C n →ₗ[K] cycles C d n
  | 0 => (LinearMap.id : C 0 →ₗ[K] C 0).codRestrict _ (by intro x; trivial)
  | n + 1 =>
      (LinearMap.id - (boundaryLift C d hd n).comp (boundaryMap C d hd n).rangeRestrict).codRestrict
        (cycles C d (n + 1)) (by
          intro x
          change d n (x - boundaryLift C d hd n ((boundaryMap C d hd n).rangeRestrict x)) = 0
          rw [map_sub, differential_boundaryLift]
          exact sub_self _)

theorem cycleProjection_zero (x : C 0) :
    (cycleProjection C d hd 0 x).val = x := rfl

theorem cycleProjection_succ (n : ℕ) (x : C (n + 1)) :
    (cycleProjection C d hd (n + 1) x).val =
      x - boundaryLift C d hd n ((boundaryMap C d hd n).rangeRestrict x) := rfl

theorem cycleProjection_cycle (n : ℕ) (z : cycles C d n) :
    cycleProjection C d hd n z.val = z := by
  cases n with
  | zero => rfl
  | succ n =>
      apply Subtype.ext
      rw [cycleProjection_succ]
      have hz : (boundaryMap C d hd n).rangeRestrict z.val = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        exact z.property
      rw [hz, map_zero, sub_zero]

def homologySection (n : ℕ) : Homology C d hd n →ₗ[K] cycles C d n :=
  Classical.choose ((boundaries C d hd n).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (boundaries C d hd n).mkQ_surjective))

theorem quotient_homologySection (n : ℕ) (a : Homology C d hd n) :
    (boundaries C d hd n).mkQ (homologySection C d hd n a) = a :=
  LinearMap.congr_fun
    (Classical.choose_spec ((boundaries C d hd n).mkQ.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (boundaries C d hd n).mkQ_surjective))) a

def homologyProjection (n : ℕ) : C n →ₗ[K] Homology C d hd n :=
  (boundaries C d hd n).mkQ.comp (cycleProjection C d hd n)

def homologyInclusion (n : ℕ) : Homology C d hd n →ₗ[K] C n :=
  (cycles C d n).subtype.comp (homologySection C d hd n)

theorem homologyProjection_inclusion (n : ℕ) (a : Homology C d hd n) :
    homologyProjection C d hd n (homologyInclusion C d hd n a) = a := by
  change (boundaries C d hd n).mkQ
    (cycleProjection C d hd n (homologySection C d hd n a).val) = a
  rw [cycleProjection_cycle, quotient_homologySection]

end BanachIsometric.VectorChainSplitting
