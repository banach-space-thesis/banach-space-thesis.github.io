import BanachIsometric.AlexanderWhitneyMap

/-! The actual front/back face restrictions of Alexander--Whitney terms,
including the two middle restrictions whose signed contributions cancel. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem simplexFrontProjection_face {n p : ℕ} (hp : p ≤ n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (i : Fin (p + 2)) :
    simplexFrontProjection (σ.comp (face (intervalFaceIndex (s := 0) (by omega : 0 + p ≤ n) i))) p hp =
      (simplexFrontProjection σ (p + 1) (by omega)).comp (face i) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun t : C(Simplex p, Simplex (n + 1)) => (σ (t x)).1)
    (intervalSimplex_face (by omega : 0 + p ≤ n) i).symm

theorem simplexBackProjection_face {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (i : Fin (q + 2)) :
    simplexBackProjection (σ.comp (face (intervalFaceIndex h.le i))) p q h =
      (simplexBackProjection σ p (q + 1) (by omega)).comp (face i) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun t : C(Simplex q, Simplex (n + 1)) => (σ (t x)).2)
    (intervalSimplex_face h.le i).symm

theorem simplexBackProjection_face_before {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (i : Fin (p + 1)) :
    simplexBackProjection (σ.comp (face (⟨i.val, by omega⟩ : Fin (n + 2)))) p q h =
      simplexBackProjection σ (p + 1) q (by omega) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun t : C(Simplex q, Simplex (n + 1)) => (σ (t x)).2)
    (face_intervalSimplex_before h.le (⟨i.val, by omega⟩ : Fin (n + 2))
      (by change i.val ≤ p; omega))

theorem simplexFrontProjection_face_after {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (i : Fin (q + 1)) :
    simplexFrontProjection (σ.comp (face (⟨p + 1 + i.val, by omega⟩ : Fin (n + 2)))) p (by omega) =
      simplexFrontProjection σ p (by omega) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun t : C(Simplex p, Simplex (n + 1)) => (σ (t x)).1)
    (face_intervalSimplex_after (by omega : 0 + p ≤ n)
      (⟨p + 1 + i.val, by omega⟩ : Fin (n + 2))
      (by change 0 + p < p + 1 + i.val; omega))

theorem simplexFrontProjection_face_last {n p : ℕ} (h : p + 1 ≤ n)
    (σ : RawSingularSimplex (X × Y) n) :
    (simplexFrontProjection σ (p + 1) h).comp (face (Fin.last (p + 1))) =
      simplexFrontProjection σ p (by omega) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun t : C(Simplex p, Simplex n) => (σ (t x)).1)
    (intervalSimplex_face_last (by omega : 0 + (p + 1) ≤ n))

theorem simplexBackProjection_face_zero {n p q : ℕ} (h : p + (q + 1) = n)
    (σ : RawSingularSimplex (X × Y) n) :
    (simplexBackProjection σ p (q + 1) h).comp (face (0 : Fin (q + 2))) =
      simplexBackProjection σ (p + 1) q (by omega) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun t : C(Simplex q, Simplex n) => (σ (t x)).2)
    (intervalSimplex_face_zero h.le)

end BanachIsometric.SingularAW
