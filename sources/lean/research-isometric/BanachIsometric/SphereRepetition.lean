import BanachIsometric.CubicalSphereDescent
import BanachIsometric.HomotopyRepetition

/-! An actual continuous sphere self-map is obtained by descending actual
concatenations of the cubical quotient generator. Postcomposition commutes
with this repetition. Finite order of a specified actual homotopy class then
gives an actual nullhomotopy of the pulled-back sphere map.

The finite-order hypothesis is explicit: no compact-group higher homotopy
finiteness theorem is asserted. Nor is the analytic index or Lipschitz
regularity of the repetition map asserted here. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open scoped Topology Topology.Homotopy unitInterval

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def mapGenLoop (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1, fun u hu => by rw [ContinuousMap.comp_apply, p.property u hu, hf]⟩

@[simp] theorem mapGenLoop_apply (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x)
    (u : N → unitInterval) : mapGenLoop f hf p u = f (p u) := rfl

@[simp] theorem mapGenLoop_const (f : C(X, Y)) (hf : f x = y) :
    mapGenLoop f hf (GenLoop.const : GenLoop N X x) = GenLoop.const := by
  ext u
  exact hf

theorem mapGenLoop_transAt [DecidableEq N] (f : C(X, Y)) (hf : f x = y)
    (i : N) (p q : GenLoop N X x) :
    mapGenLoop f hf (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f hf p) (mapGenLoop f hf q) := by
  ext u
  simp only [mapGenLoop_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

theorem mapGenLoop_repeat [DecidableEq N] (f : C(X, Y)) (hf : f x = y)
    (i : N) (p : GenLoop N X x) (d : ℕ) :
    mapGenLoop f hf (repeatGenLoop i p d) = repeatGenLoop i (mapGenLoop f hf p) d := by
  induction d with
  | zero => exact mapGenLoop_const f hf
  | succ d ih => rw [repeatGenLoop_succ, mapGenLoop_transAt, ih, repeatGenLoop_succ]

theorem targetGenLoopSphereMap_mapGenLoop (n : ℕ) (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop (Fin (n + 1)) X x) :
    targetGenLoopSphereMap n (mapGenLoop f hf p) = f.comp (targetGenLoopSphereMap n p) := by
  ext z
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  have h₁ := congrArg (fun g : C((Fin (n + 1) → unitInterval), Y) => g u)
    (targetGenLoopSphereMap_comp_cubeToSphere n (mapGenLoop f hf p))
  have h₂ := congrArg (fun g : C((Fin (n + 1) → unitInterval), X) => g u)
    (targetGenLoopSphereMap_comp_cubeToSphere n p)
  exact h₁.trans (congrArg f h₂).symm

def sphereRepetition (n d : ℕ) : C(Sph (n + 1), Sph (n + 1)) :=
  targetGenLoopSphereMap n (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d)

theorem sphereRepetition_basepoint (n d : ℕ) :
    sphereRepetition n d (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) :=
  targetGenLoopSphereMap_basepoint n _

theorem sphereRepetition_comp_cubeToSphere (n d : ℕ) :
    (sphereRepetition n d).comp (cubeToSphere (n + 1)) =
      (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d).1 :=
  targetGenLoopSphereMap_comp_cubeToSphere n _

theorem sphereMap_comp_repetition (n d : ℕ) (f : C(Sph (n + 1), X))
    (hf : f (sphereBasepoint (n + 1)) = x) :
    f.comp (sphereRepetition n d) =
      targetGenLoopSphereMap n
        (repeatGenLoop (0 : Fin (n + 1)) (sphereTargetMapGenLoop (n + 1) f hf) d) := by
  have he : mapGenLoop f hf (sphereGenerator (n + 1)) =
      sphereTargetMapGenLoop (n + 1) f hf := rfl
  rw [← he, ← mapGenLoop_repeat, targetGenLoopSphereMap_mapGenLoop]
  rfl

/-- A finite-order actual clutching class is killed by one of the actual
continuous sphere repetition maps. The returned object is a homotopy of
literal sphere maps, not merely an equality in a quotient group. -/
theorem exists_positive_sphereRepetition_nullhomotopy_of_finiteOrder (n : ℕ)
    (f : C(Sph (n + 1), X)) (hf : f (sphereBasepoint (n + 1)) = x)
    (hfin : IsOfFinOrder (genLoopClass (sphereTargetMapGenLoop (n + 1) f hf))) :
    ∃ d : ℕ, 0 < d ∧ Nonempty (ContinuousMap.Homotopy
      (f.comp (sphereRepetition n d)) (ContinuousMap.const _ x)) := by
  obtain ⟨d, hd, H⟩ := exists_positive_repeatGenLoop_nullhomotopic_of_finiteOrder
    (0 : Fin (n + 1)) (sphereTargetMapGenLoop (n + 1) f hf) hfin
  obtain ⟨H⟩ := H
  refine ⟨d, hd, ?_⟩
  rw [sphereMap_comp_repetition n d f hf, ← targetGenLoopSphereMap_const n]
  exact ⟨targetGenLoopSphereMapHomotopy n H⟩

end BanachIsometric.SphereGenerator
