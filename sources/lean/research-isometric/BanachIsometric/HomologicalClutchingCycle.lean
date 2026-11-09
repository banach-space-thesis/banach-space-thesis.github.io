import BanachIsometric.RawSingularHomology
import Mathlib.Tactic.Abel

/-! Clutching a cycle in the total space requires a boundary between two
equatorial graph chains. The correction projects through the equator. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open scoped Topology

variable {E G N S B P : Type*}
  [TopologicalSpace E] [TopologicalSpace G] [TopologicalSpace N]
  [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace P]

def rawGraphMap (g : C(E, G)) : C(E, E × G) := (ContinuousMap.id E).prodMk g

@[simp] theorem rawGraphMap_fst_comp (g : C(E, G)) :
    (ContinuousMap.fst : C(E × G, E)).comp (rawGraphMap g) = ContinuousMap.id E := rfl

theorem raw_cycle_difference_bounds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (n : ℕ) (z : rawCycles X n)
    (h : rawHomologyMap f n (Submodule.Quotient.mk z) =
      rawHomologyMap g n (Submodule.Quotient.mk z)) :
    ∃ w : RawRationalChains Y (n + 2),
      rawBoundary (n + 1) w = rawChainMap f (n + 1) z.val - rawChainMap g (n + 1) z.val := by
  rw [rawHomologyMap_mk, rawHomologyMap_mk] at h
  obtain ⟨w, hw⟩ := (Submodule.Quotient.eq (rawBoundaries Y n)).mp h
  refine ⟨w, ?_⟩
  have hv := congrArg (fun c : rawCycles Y n => c.val) hw
  exact hv

private theorem boundary_chainMap_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (c : RawRationalChains X (n + 1)) :
    rawBoundary n (rawChainMap f (n + 1) c) = rawChainMap f n (rawBoundary n c) :=
  LinearMap.congr_fun (rawChainMap_boundary f n) c

private theorem chainMap_apply_apply {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) (c : RawRationalChains X n) :
    rawChainMap g n (rawChainMap f n c) = rawChainMap (g.comp f) n c :=
  (LinearMap.congr_fun (rawChainMap_comp f g n) c).symm

theorem exists_raw_homological_clutching_lift
    (iN : C(E, N)) (iS : C(E, S)) (pN : C(N, B)) (pS : C(S, B))
    (liftN : C(N, P)) (liftS : C(S, P)) (γ : C(E × G, P)) (projection : C(P, B))
    (g : C(E, G)) (g₀ : G)
    (hN : liftN.comp iN = γ.comp (rawGraphMap (ContinuousMap.const E g₀)))
    (hS : liftS.comp iS = γ.comp (rawGraphMap g))
    (hpN : projection.comp liftN = pN) (hpS : projection.comp liftS = pS)
    (hpγ : projection.comp γ = (pN.comp iN).comp ContinuousMap.fst)
    (n : ℕ) (z : rawCycles E n)
    (bN : RawRationalChains N (n + 2)) (bS : RawRationalChains S (n + 2))
    (hbN : rawBoundary (n + 1) bN = rawChainMap iN (n + 1) z.val)
    (hbS : rawBoundary (n + 1) bS = rawChainMap iS (n + 1) z.val)
    (hgraph : rawHomologyMap (rawGraphMap g) n (Submodule.Quotient.mk z) =
      rawHomologyMap (rawGraphMap (ContinuousMap.const E g₀)) n (Submodule.Quotient.mk z)) :
    ∃ c : rawCycles P (n + 1), ∃ correction : rawCycles E (n + 1),
      rawChainMap projection (n + 2) c.val =
        rawChainMap pN (n + 2) bN - rawChainMap pS (n + 2) bS +
          rawChainMap (pN.comp iN) (n + 2) correction.val := by
  obtain ⟨w, hw⟩ := raw_cycle_difference_bounds _ _ n z hgraph
  refine ⟨⟨rawChainMap liftN (n + 2) bN - rawChainMap liftS (n + 2) bS +
      rawChainMap γ (n + 2) w, ?_⟩, ⟨rawChainMap ContinuousMap.fst (n + 2) w, ?_⟩, ?_⟩
  · change rawBoundary (n + 1) (rawChainMap liftN (n + 2) bN -
      rawChainMap liftS (n + 2) bS + rawChainMap γ (n + 2) w) = 0
    simp only [map_add, map_sub, boundary_chainMap_apply, hbN, hbS, hw, chainMap_apply_apply, hN, hS]
    abel
  · change rawBoundary (n + 1) (rawChainMap ContinuousMap.fst (n + 2) w) = 0
    simp only [boundary_chainMap_apply, hw, map_sub, chainMap_apply_apply, rawGraphMap_fst_comp, sub_self]
  · simp only [map_add, map_sub, chainMap_apply_apply, hpN, hpS, hpγ]

end BanachIsometric.SingularPrism
