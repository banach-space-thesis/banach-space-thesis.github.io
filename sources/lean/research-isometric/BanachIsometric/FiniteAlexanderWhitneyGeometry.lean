import BanachIsometric.FiniteNerveRawSingularMap
import BanachIsometric.AlexanderWhitneyGeometry

/-! Actual front/back subfaces of a strict ordered finite simplex. Their
literal barycentric singular simplices are exactly the front/back maps used
by the proved raw Alexander–Whitney construction. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism SingularAW

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def strictIntervalFace (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (s d : ℕ) (h : s + d ≤ n) : StrictOrderedSimplex K d := by
  let e := intervalEmbedding s d n h
  let w : Fin (d + 1) →o ι := v.val.val.comp e.toOrderHom
  refine ⟨⟨w, K.downward _ v.val.property _ ?_ ?_⟩,
    v.property.comp (intervalVertex_strictMono s d n h)⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨e j, Finset.mem_univ _, rfl⟩
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

@[simp] theorem strictIntervalFace_apply (K : Complex ι) {n : ℕ}
    (v : StrictOrderedSimplex K n) (s d : ℕ) (h : s + d ≤ n) (j : Fin (d + 1)) :
    (strictIntervalFace K v s d h).val.val j = v.val.val (intervalVertex s d n h j) := rfl

theorem barycentricSingularSimplex_intervalFace (K : Complex ι) {n : ℕ}
    (v : StrictOrderedSimplex K n) (s d : ℕ) (h : s + d ≤ n) :
    barycentricSingularSimplex K d (strictIntervalFace K v s d h) =
      (barycentricSingularSimplex K n v).comp (intervalSimplex s d n h) := by
  apply ContinuousMap.ext
  intro t
  exact faceBarycentricMap_naturality K (intervalVertex s d n h)
    (fun j => v.val.val j) v.val.property t

def strictFrontFace (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (p : ℕ) (hp : p ≤ n) : StrictOrderedSimplex K p :=
  strictIntervalFace K v 0 p (by omega)

def strictBackFace (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (p q : ℕ) (hpq : p + q = n) : StrictOrderedSimplex K q :=
  strictIntervalFace K v p q hpq.le

theorem barycentricSingularSimplex_frontFace (K : Complex ι) {n : ℕ}
    (v : StrictOrderedSimplex K n) (p : ℕ) (hp : p ≤ n) :
    barycentricSingularSimplex K p (strictFrontFace K v p hp) =
      (barycentricSingularSimplex K n v).comp (frontSimplex p n hp) :=
  barycentricSingularSimplex_intervalFace K v 0 p (by omega)

theorem barycentricSingularSimplex_backFace (K : Complex ι) {n : ℕ}
    (v : StrictOrderedSimplex K n) (p q : ℕ) (hpq : p + q = n) :
    barycentricSingularSimplex K q (strictBackFace K v p q hpq) =
      (barycentricSingularSimplex K n v).comp (backSimplex p q n hpq) :=
  barycentricSingularSimplex_intervalFace K v p q hpq.le

end BanachIsometric.FiniteNerve
