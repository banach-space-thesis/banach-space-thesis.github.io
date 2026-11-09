import BanachIsometric.SphereRepetition

/-! Transport of the explicit sphere repetition to an actual equator (or
any explicitly homeomorphic model). The finite-order condition is retained
as an explicit intermediate hypothesis. -/

noncomputable section
namespace BanachIsometric
open scoped Topology Topology.Homotopy

open SphereGenerator

theorem exists_positive_equatorRepetition_nullhomotopy_of_finiteOrder
    {Q G : Type*} [TopologicalSpace Q] [TopologicalSpace G] [Group G]
    (n : ℕ) (e : Q ≃ₜ Sph (n + 1)) (g : C(Q, G))
    (hg : g (e.symm (sphereBasepoint (n + 1))) = 1)
    (hfin : IsOfFinOrder (genLoopClass (sphereTargetMapGenLoop (n + 1)
      (g.comp ⟨e.symm, e.symm.continuous⟩) hg))) :
    ∃ d : ℕ, 0 < d ∧
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.const Q (1 : G))
        (g.comp ((⟨e.symm, e.symm.continuous⟩ : C(Sph (n + 1), Q)).comp
          ((sphereRepetition n d).comp ⟨e, e.continuous⟩)))) := by
  let eC : C(Q, Sph (n + 1)) := ⟨e, e.continuous⟩
  let eiC : C(Sph (n + 1), Q) := ⟨e.symm, e.symm.continuous⟩
  obtain ⟨d, hd, ⟨h⟩⟩ := exists_positive_sphereRepetition_nullhomotopy_of_finiteOrder
    n (g.comp eiC) hg hfin
  let hQ := (h.compContinuousMap eC).symm
  refine ⟨d, hd, ⟨hQ.cast ?_ ?_⟩⟩
  · ext q
    rfl
  · ext q
    rfl

end BanachIsometric
