import BanachIsometric.AddCircleCovering

/-! The actual finite torus is covered by its real coordinate space, and its
actual homotopy groups in degrees at least two vanish. Each covering chart
comes from the proved quotient local inverse in every circle coordinate. -/

noncomputable section
namespace BanachIsometric

theorem isLocalHomeomorph_finitePi
    {ι : Type*} [Finite ι] {E B : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, TopologicalSpace (B i)]
    (p : ∀ i, E i → B i) (hp : ∀ i, IsLocalHomeomorph (p i)) :
    IsLocalHomeomorph (fun (x : ∀ i, E i) i => p i (x i)) := by
  intro x
  choose chart hx hchart using fun i => hp i (x i)
  refine ⟨OpenPartialHomeomorph.pi chart, ?_, ?_⟩
  · exact fun i _ => hx i
  · funext y i
    exact congrFun (hchart i) (y i)

def realTorusProjection {ι : Type*} (period : ι → ℝ) :
    (ι → ℝ) →+ (∀ i, AddCircle (period i)) where
  toFun x i := x i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem isCoveringMap_realTorusProjection {ι : Type*} [Fintype ι]
    (period : ι → ℝ) (hperiod : ∀ i, 0 < period i) :
    IsCoveringMap (realTorusProjection period) := by
  have hlocal : IsLocalHomeomorph (realTorusProjection period) := by
    apply isLocalHomeomorph_finitePi (fun i => ((↑) : ℝ → AddCircle (period i)))
    intro i
    letI : Fact (0 < period i) := ⟨hperiod i⟩
    exact AddCircle.isLocalHomeomorph_coe (period i)
  have hsurj : Function.Surjective (realTorusProjection period) := by
    intro y
    choose x hx using fun i => QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (period i)) (y i)
    exact ⟨x, funext hx⟩
  exact isCoveringMap_of_surjective_addGroup_localHomeomorph (realTorusProjection period) hlocal hsurj

theorem subsingleton_higherHomotopy_finiteTorus {ι : Type*} [Fintype ι]
    (period : ι → ℝ) (hperiod : ∀ i, 0 < period i) (n : ℕ) :
    Subsingleton (HomotopyGroup (Fin (n + 2)) (∀ i, AddCircle (period i)) 0) := by
  letI := subsingleton_homotopyGroup_realVector (N := Fin (n + 2)) (0 : ι → ℝ)
  exact (coveringHigherHomotopyEquiv (isCoveringMap_realTorusProjection period hperiod) 0 n).symm.injective.subsingleton

end BanachIsometric
