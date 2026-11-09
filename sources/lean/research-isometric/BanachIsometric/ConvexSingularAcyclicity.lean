import BanachIsometric.RawPointHomology
import BanachIsometric.FiniteNervePolyhedron
import Mathlib.Analysis.Convex.Contractible

/-! Actual positive singular homology vanishes on contractible spaces and
on every nonempty convex coordinate face. This is a local acyclicity
foundation for a later simplicial/singular comparison, not that comparison. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

theorem rawPositiveHomology_contractible (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) : Subsingleton (RawPositiveHomology X n) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  have hid : (LinearMap.id : RawPositiveHomology X n →ₗ[ℚ] RawPositiveHomology X n) = 0 := by
    rw [← rawHomologyMap_id]
    exact rawHomologyMap_nullhomotopic n (ContinuousMap.id X) x H
  have hz (z : RawPositiveHomology X n) : z = 0 := LinearMap.congr_fun hid z
  exact ⟨fun z w => (hz z).trans (hz w).symm⟩

theorem rawPositiveHomology_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty) (n : ℕ) :
    Subsingleton (RawPositiveHomology s n) := by
  letI : ContractibleSpace s := hs.contractibleSpace hne
  exact rawPositiveHomology_contractible s n

theorem coordinateFace_rawPositiveHomology_subsingleton {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : Finset ι) (hne : s.Nonempty) (n : ℕ) :
    Subsingleton (RawPositiveHomology (FiniteNerve.coordinateFace s) n) := by
  apply rawPositiveHomology_convex (FiniteNerve.coordinateFace_convex s) _ n
  rw [FiniteNerve.coordinateFace_eq_convexHull]
  exact hne.to_set.image FiniteNerve.vertex |>.convexHull

end BanachIsometric.SingularPrism
