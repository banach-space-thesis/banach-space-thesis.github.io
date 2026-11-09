import BanachIsometric.RawUnionSmallCycles
import BanachIsometric.FiniteDimensionalObstruction
import Mathlib.RingTheory.Finiteness.Prod

/-! The two-set Mayer–Vietoris finiteness and vanishing consequences for
actual singular homology, using the overlap obstruction of a subordinate
cycle. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

theorem rawDegreeHomology_finiteDimensional_union (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (hHU : FiniteDimensional ℚ (RawDegreeHomology U n))
    (hHV : FiniteDimensional ℚ (RawDegreeHomology V n))
    (hHI : 0 < n → FiniteDimensional ℚ (RawDegreeHomology (U ∩ V : Set X) (n - 1))) :
    FiniteDimensional ℚ (RawDegreeHomology X n) := by
  cases n with
  | zero =>
      letI := hHU
      letI := hHV
      exact FiniteDimensional.of_surjective (rawDegreeHomologyComponentSum U V 0)
        (rawZeroHomologyComponentSum_surjective U V hcover)
  | succ n =>
      letI := hHU
      letI := hHV
      letI : FiniteDimensional ℚ (RawDegreeHomology (U ∩ V : Set X) n) := hHI (Nat.succ_pos n)
      exact finiteDimensional_of_surjective_with_obstruction (rawUnionPairToHomology U V n)
        (rawUnionPairToOverlapHomology U V n) (rawUnionPairToHomology_surjective U V hU hV hcover n)
        (LinearMap.range (rawDegreeHomologyComponentSum U V (n + 1)))
        (rawUnionPairToHomology_mem_component_range_of_overlap_zero U V n)

theorem rawDegreeHomology_subsingleton_union (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (hHU : Subsingleton (RawDegreeHomology U n))
    (hHV : Subsingleton (RawDegreeHomology V n))
    (hHI : 0 < n → Subsingleton (RawDegreeHomology (U ∩ V : Set X) (n - 1))) :
    Subsingleton (RawDegreeHomology X n) := by
  letI := hHU
  letI := hHV
  have hzero : ∀ q : RawDegreeHomology X n, q = 0 := by
    cases n with
    | zero =>
        intro q
        obtain ⟨a, rfl⟩ := rawZeroHomologyComponentSum_surjective U V hcover q
        rw [Subsingleton.elim a 0, map_zero]
    | succ n =>
        letI : Subsingleton (RawDegreeHomology (U ∩ V : Set X) n) := hHI (Nat.succ_pos n)
        intro q
        obtain ⟨z, rfl⟩ := rawUnionPairToHomology_surjective U V hU hV hcover n q
        obtain ⟨a, ha⟩ := rawUnionPairToHomology_mem_component_range_of_overlap_zero U V n z
          (Subsingleton.elim _ _)
        rw [Subsingleton.elim a 0, map_zero] at ha
        exact ha.symm
  exact ⟨fun q r => (hzero q).trans (hzero r).symm⟩

end BanachIsometric.SingularPrism
