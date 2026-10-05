import ThesisCommon.Analysis.BooleanDensityHomogeneity
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Finite.Card

/-! Finite density in a T1 space means that the space itself is finite.
Consequently, a density-homogeneous element of finite principal density is
an actual order atom. -/
noncomputable section
open Set
namespace ThesisCommon
universe u

theorem finite_of_topologicalDensity_lt_aleph0 (X : Type u)
    [TopologicalSpace X] [T1Space X]
    (h : topologicalDensity X < Cardinal.aleph0) : Finite X := by
  obtain ⟨s, hs, hcard⟩ := exists_dense_card_eq_topologicalDensity X
  have hfin : s.Finite := Set.finite_coe_iff.mp (Cardinal.mk_lt_aleph0_iff.mp (hcard ▸ h))
  have heq : s = univ := by simpa only [hfin.isClosed.closure_eq] using hs.closure_eq
  exact Finite.of_finite_univ (heq ▸ hfin)

theorem aleph0_le_topologicalDensity_of_infinite (X : Type u)
    [TopologicalSpace X] [T1Space X] [Infinite X] :
    Cardinal.aleph0 ≤ topologicalDensity X := by
  by_contra h
  haveI : Finite X := finite_of_topologicalDensity_lt_aleph0 X (lt_of_not_ge h)
  exact not_finite X

theorem topologicalDensity_eq_card_of_finite (X : Type u)
    [TopologicalSpace X] [T1Space X] [Finite X] :
    topologicalDensity X = Cardinal.mk X := by
  obtain ⟨s, hs, hcard⟩ := exists_dense_card_eq_topologicalDensity X
  have heq : s = univ := by simpa only [s.toFinite.isClosed.closure_eq] using hs.closure_eq
  rw [heq, Cardinal.mk_univ] at hcard
  exact hcard.symm

theorem IsDensityHomogeneous.isAtom_of_principalDensity_lt_aleph0
    {B : Type u} [SemilatticeInf B] [OrderBot B] [TopologicalSpace B]
    [ContinuousInf B] [T1Space B] {a : B}
    (ha : IsDensityHomogeneous a) (h : principalDensity a < Cardinal.aleph0) : IsAtom a := by
  letI : Finite (Iic a) := finite_of_topologicalDensity_lt_aleph0 _ h
  have hfin : (Iic a).Finite := Set.finite_coe_iff.mp inferInstance
  refine ⟨ha.1, fun b hba => ?_⟩
  by_contra hb
  have hsub : Iic b ⊆ Iic a := Iic_subset_Iic.mpr hba.le
  letI : Finite (Iic b) := Set.finite_coe_iff.mpr (hfin.subset hsub)
  have hcard : Cardinal.mk (Iic b) = Cardinal.mk (Iic a) := by
    simpa only [principalDensity, topologicalDensity_eq_card_of_finite] using ha.2 b hb hba.le
  have hnat : Nat.card (Iic b) = Nat.card (Iic a) := by
    simpa only [Nat.card] using congrArg Cardinal.toNat hcard
  have heq := hfin.eq_of_subset_of_card_le hsub hnat.ge
  exact hba.not_ge (by simpa only [← heq] using (show a ∈ Iic a from le_rfl))

end ThesisCommon
