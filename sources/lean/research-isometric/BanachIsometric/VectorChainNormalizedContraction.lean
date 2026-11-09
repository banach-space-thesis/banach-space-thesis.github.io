import BanachIsometric.VectorChainContraction

/-! The explicit vector-space chain contraction has the normalized side
identities p h = 0, h i = 0 and h² = 0. They follow from the actual choices of
sections, with no extra compatibility hypotheses. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting

variable {K : Type*} [Field K] (C : ℕ → ModuleCat.{u} K)
  (d : ∀ n, C (n + 1) →ₗ[K] C n)
  (hd : ∀ n, (d n).comp (d (n + 1)) = 0)

theorem cycleProjection_boundaryLift (n : ℕ) (b : boundaries C d hd n) :
    cycleProjection C d hd (n + 1) (boundaryLift C d hd n b) = 0 := by
  apply Subtype.ext
  rw [cycleProjection_succ]
  have hb : (boundaryMap C d hd n).rangeRestrict (boundaryLift C d hd n b) = b :=
    Subtype.ext (boundaryMap_boundaryLift C d hd n b)
  rw [hb, sub_self]
  rfl

theorem homologyProjection_boundaryLift (n : ℕ) (b : boundaries C d hd n) :
    homologyProjection C d hd (n + 1) (boundaryLift C d hd n b) = 0 := by
  change (boundaries C d hd (n + 1)).mkQ
    (cycleProjection C d hd (n + 1) (boundaryLift C d hd n b)) = 0
  rw [cycleProjection_boundaryLift, map_zero]

theorem homologyProjection_contraction (n : ℕ) (x : C n) :
    homologyProjection C d hd (n + 1) (contraction C d hd n x) = 0 :=
  homologyProjection_boundaryLift C d hd n (boundaryRemainder C d hd n x)

theorem boundaryRemainder_inclusion (n : ℕ) (a : Homology C d hd n) :
    boundaryRemainder C d hd n (homologyInclusion C d hd n a) = 0 := by
  apply Subtype.ext
  change cycleProjection C d hd n (homologySection C d hd n a).val -
    homologySection C d hd n
      (homologyProjection C d hd n (homologyInclusion C d hd n a)) = 0
  rw [cycleProjection_cycle, homologyProjection_inclusion, sub_self]

theorem contraction_inclusion (n : ℕ) (a : Homology C d hd n) :
    contraction C d hd n (homologyInclusion C d hd n a) = 0 := by
  change boundaryLift C d hd n
    (boundaryRemainder C d hd n (homologyInclusion C d hd n a)) = 0
  rw [boundaryRemainder_inclusion, map_zero]

theorem contraction_boundaryLift (n : ℕ) (b : boundaries C d hd n) :
    contraction C d hd (n + 1) (boundaryLift C d hd n b) = 0 := by
  change boundaryLift C d hd (n + 1)
    (boundaryRemainder C d hd (n + 1) (boundaryLift C d hd n b)) = 0
  have hb : boundaryRemainder C d hd (n + 1) (boundaryLift C d hd n b) = 0 := by
    apply Subtype.ext
    change cycleProjection C d hd (n + 1) (boundaryLift C d hd n b) -
      homologySection C d hd (n + 1)
        (homologyProjection C d hd (n + 1) (boundaryLift C d hd n b)) = 0
    rw [cycleProjection_boundaryLift, homologyProjection_boundaryLift, map_zero, sub_self]
  rw [hb, map_zero]

theorem contraction_contraction (n : ℕ) (x : C n) :
    contraction C d hd (n + 1) (contraction C d hd n x) = 0 :=
  contraction_boundaryLift C d hd n (boundaryRemainder C d hd n x)

end BanachIsometric.VectorChainSplitting
