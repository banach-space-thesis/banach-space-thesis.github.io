import BanachIsometric.AlexanderWhitneyMap

/-! The two parenthesizations of three Alexander--Whitney cuts give
literally the same three simplex restrictions, with shared cut vertices. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def awProductAssoc : C((X × Y) × Z, X × (Y × Z)) :=
  ⟨fun x => (x.1.1, x.1.2, x.2),
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)⟩

theorem awTripleFront {n p q r : ℕ} (h : p + q + r = n)
    (σ : RawSingularSimplex ((X × Y) × Z) n) :
    simplexFrontProjection (simplexFrontProjection σ (p + q) (by omega)) p (by omega) =
      simplexFrontProjection (awProductAssoc.comp σ) p (by omega) := by
  have hcut : (frontSimplex (p + q) n (by omega)).comp (frontSimplex p (p + q) (by omega)) =
      frontSimplex p n (by omega) := by
    simpa only [frontSimplex, Nat.zero_add] using
      (intervalSimplex_comp (a := 0) (d := p + q) (n := n) (b := 0) (e := p) (by omega) (by omega))
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun z => (σ z).1.1) (DFunLike.congr_fun hcut x)

theorem awTripleMiddle {n p q r : ℕ} (h : p + q + r = n)
    (σ : RawSingularSimplex ((X × Y) × Z) n) :
    simplexBackProjection (simplexFrontProjection σ (p + q) (by omega)) p q rfl =
      simplexFrontProjection (simplexBackProjection (awProductAssoc.comp σ) p (q + r) (by omega))
        q (by omega) := by
  have hleft : (frontSimplex (p + q) n (by omega)).comp (backSimplex p q (p + q) rfl) =
      intervalSimplex p q n (by omega) := by
    simpa only [frontSimplex, backSimplex, Nat.zero_add] using
      (intervalSimplex_comp (a := 0) (d := p + q) (n := n) (b := p) (e := q) (by omega) (by omega))
  have hright : (backSimplex p (q + r) n (by omega)).comp (frontSimplex q (q + r) (by omega)) =
      intervalSimplex p q n (by omega) := by
    simpa only [frontSimplex, backSimplex, Nat.zero_add, Nat.add_zero] using
      (intervalSimplex_comp (a := p) (d := q + r) (n := n) (b := 0) (e := q) (by omega) (by omega))
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun z => (σ z).1.2) (DFunLike.congr_fun (hleft.trans hright.symm) x)

theorem awTripleBack {n p q r : ℕ} (h : p + q + r = n)
    (σ : RawSingularSimplex ((X × Y) × Z) n) :
    simplexBackProjection σ (p + q) r h =
      simplexBackProjection (simplexBackProjection (awProductAssoc.comp σ) p (q + r) (by omega)) q r rfl := by
  have hcut : (backSimplex p (q + r) n (by omega)).comp (backSimplex q r (q + r) rfl) =
      backSimplex (p + q) r n h := by
    simpa only [backSimplex] using
      (intervalSimplex_comp (a := p) (d := q + r) (n := n) (b := q) (e := r) (by omega) (by omega))
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun z => (σ z).2) (DFunLike.congr_fun hcut.symm x)

end BanachIsometric.SingularAW
