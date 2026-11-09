import NonCalkinAlgebra.OrderedCocycleSupport
import NonCalkinAlgebra.OrderedTwistedAlgebra
import NonCalkinAlgebra.TwistedConjugation
import NonCalkinAlgebra.TwistedSpanDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.OrderedTwistedAlgebra
open TwistedRegular CommutationChains
universe u
variable (Λ : Type u) [LinearOrder Λ]

/-- The actual chain in the completed algebra has countable closed-interval
supports for the discrete commutation relation. -/
theorem weaklySkeletonLike : WeaklySkeletonLike Across (pair Λ) := by
  classical
  intro a
  let c := OrderedCocycle.cocycle Λ
  let a₁ : closedSubalgebra c := a.1
  let a₂ : closedSubalgebra c := a.2
  obtain ⟨S₁, hS₁, hdet₁⟩ := countable_shift_determining_set c a₁
  obtain ⟨S₂, hS₂, hdet₂⟩ := countable_shift_determining_set c a₂
  let S : Set Λ := ⋃ g ∈ S₁ ∪ S₂, (↑(OrderedCocycle.orderSupport Λ g) : Set Λ)
  have hS : S.Countable := (hS₁.union hS₂).biUnion (fun g _ =>
    (OrderedCocycle.orderSupport Λ g).finite_toSet.countable)
  refine ⟨S, hS, ?_⟩
  intro i j hij hgap
  have hchars : ∀ g ∈ S₁ ∪ S₂,
      OrderedCocycle.alternating Λ g (OrderedCocycle.w Λ i 0) =
        OrderedCocycle.alternating Λ g (OrderedCocycle.w Λ j 0) ∧
      OrderedCocycle.alternating Λ g (OrderedCocycle.u Λ i) =
        OrderedCocycle.alternating Λ g (OrderedCocycle.u Λ j) := by
    intro g hg
    apply OrderedCocycle.alternating_constant_on_gap Λ g hij
    intro η hη hηI
    exact Set.disjoint_left.mp hgap hηI
      (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, hη⟩⟩)
  have hfirst : conjugateShift c (OrderedCocycle.w Λ i 0) a₁ =
      conjugateShift c (OrderedCocycle.w Λ j 0) a₁ := by
    apply hdet₁
    intro g hg
    rw [conjugateShift_shift, conjugateShift_shift]
    have hc := (hchars g (Or.inl hg)).1
    have heq : c (OrderedCocycle.w Λ i 0) g + c g (OrderedCocycle.w Λ i 0) =
        c (OrderedCocycle.w Λ j 0) g + c g (OrderedCocycle.w Λ j 0) := by
      simpa only [c, OrderedCocycle.alternating, add_comm] using hc
    rw [heq]
  have hsecond : conjugateShift c (OrderedCocycle.u Λ i) a₂ =
      conjugateShift c (OrderedCocycle.u Λ j) a₂ := by
    apply hdet₂
    intro g hg
    rw [conjugateShift_shift, conjugateShift_shift]
    have hc := (hchars g (Or.inr hg)).2
    have heq : c (OrderedCocycle.u Λ i) g + c g (OrderedCocycle.u Λ i) =
        c (OrderedCocycle.u Λ j) g + c g (OrderedCocycle.u Λ j) := by
      simpa only [c, OrderedCocycle.alternating, add_comm] using hc
    rw [heq]
  constructor
  · change a₁ * shiftInAlgebra c (OrderedCocycle.w Λ i 0) =
        shiftInAlgebra c (OrderedCocycle.w Λ i 0) * a₁ ↔
      a₁ * shiftInAlgebra c (OrderedCocycle.w Λ j 0) =
        shiftInAlgebra c (OrderedCocycle.w Λ j 0) * a₁
    rw [eq_comm, ← conjugateShift_eq_self_iff, hfirst, conjugateShift_eq_self_iff, eq_comm]
  · change shiftInAlgebra c (OrderedCocycle.u Λ i) * a₂ =
        a₂ * shiftInAlgebra c (OrderedCocycle.u Λ i) ↔
      shiftInAlgebra c (OrderedCocycle.u Λ j) * a₂ =
        a₂ * shiftInAlgebra c (OrderedCocycle.u Λ j)
    rw [← conjugateShift_eq_self_iff, hsecond, conjugateShift_eq_self_iff]

end NonCalkinAlgebra.OrderedTwistedAlgebra
