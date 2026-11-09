/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from commit c66523531ff172d7f41913d94e56921e790a1b47 of
Vilin97/homotopy-groups-lean, Submission/Hurewicz/SphereLoopBridge.lean.
Only quotient descent of actual maps and actual relative homotopies is used.
-/
import BanachIsometric.CubicalSphereGenerator

noncomputable section
namespace BanachIsometric.SphereGenerator
open scoped Topology Topology.Homotopy unitInterval

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem targetGenLoop_factorsThrough_cubeToSphere (n : ℕ)
    (α : GenLoop (Fin (n + 1)) X x) :
    Function.FactorsThrough α.1 (cubeToSphere (n + 1)) := by
  intro u v huv
  rcases (cubeToSphere_eq_iff (n + 1) u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · rw [α.property u hu, α.property v hv]

def targetGenLoopSphereMap (n : ℕ) (α : GenLoop (Fin (n + 1)) X x) :
    C(Sph (n + 1), X) :=
  (isQuotientMap_cubeToSphere n).lift α.1
    (targetGenLoop_factorsThrough_cubeToSphere n α)

@[simp] theorem targetGenLoopSphereMap_comp_cubeToSphere (n : ℕ)
    (α : GenLoop (Fin (n + 1)) X x) :
    (targetGenLoopSphereMap n α).comp (cubeToSphere (n + 1)) = α.1 :=
  (isQuotientMap_cubeToSphere n).lift_comp _ _

theorem targetGenLoopSphereMap_basepoint (n : ℕ)
    (α : GenLoop (Fin (n + 1)) X x) :
    targetGenLoopSphereMap n α (sphereBasepoint (n + 1)) = x := by
  let u : Fin (n + 1) → unitInterval := fun _ ↦ 0
  have hu : u ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  calc
    targetGenLoopSphereMap n α (sphereBasepoint (n + 1)) =
        targetGenLoopSphereMap n α (cubeToSphere (n + 1) u) := by
          rw [cubeToSphere_boundary (n + 1) u hu]
    _ = α u := congrArg (fun f : C((Fin (n + 1) → unitInterval), X) ↦ f u)
      (targetGenLoopSphereMap_comp_cubeToSphere n α)
    _ = x := α.property u hu

@[simp] theorem targetGenLoopSphereMap_const (n : ℕ) :
    targetGenLoopSphereMap n (GenLoop.const : GenLoop (Fin (n + 1)) X x) =
      ContinuousMap.const (Sph (n + 1)) x := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  exact congrArg (fun f : C((Fin (n + 1) → unitInterval), X) ↦ f u)
    (targetGenLoopSphereMap_comp_cubeToSphere n GenLoop.const)

def sphereTargetMapGenLoop (m : ℕ) (f : C(Sph m, X))
    (hf : f (sphereBasepoint m) = x) : GenLoop (Fin m) X x :=
  ⟨f.comp (cubeToSphere m), fun u hu ↦ by
    rw [ContinuousMap.comp_apply, cubeToSphere_boundary m u hu, hf]⟩

@[simp] theorem targetGenLoopSphereMap_sphereTargetMapGenLoop (n : ℕ)
    (f : C(Sph (n + 1), X)) (hf : f (sphereBasepoint (n + 1)) = x) :
    targetGenLoopSphereMap n (sphereTargetMapGenLoop (n + 1) f hf) = f := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  exact congrArg (fun g : C((Fin (n + 1) → unitInterval), X) ↦ g u)
    (targetGenLoopSphereMap_comp_cubeToSphere n (sphereTargetMapGenLoop (n + 1) f hf))

theorem targetGenLoopHomotopyCurry_factorsThrough_cubeToSphere (n : ℕ)
    {α β : GenLoop (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    Function.FactorsThrough (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
      (cubeToSphere (n + 1)) := by
  intro u v huv
  apply ContinuousMap.ext
  intro t
  change H (t, u) = H (t, v)
  rcases (cubeToSphere_eq_iff (n + 1) u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · rw [H.eq_fst t hu, H.eq_fst t hv, α.property u hu, α.property v hv]

def targetGenLoopSphereHomotopyCurry (n : ℕ)
    {α β : GenLoop (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    C(Sph (n + 1), C(unitInterval, X)) :=
  (isQuotientMap_cubeToSphere n).lift
    (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
    (targetGenLoopHomotopyCurry_factorsThrough_cubeToSphere n H)

@[simp] theorem targetGenLoopSphereHomotopyCurry_apply_cubeToSphere (n : ℕ)
    {α β : GenLoop (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1))))
    (u : Fin (n + 1) → unitInterval) (t : unitInterval) :
    targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) t = H (t, u) :=
  congrArg (fun f : C((Fin (n + 1) → unitInterval), C(unitInterval, X)) ↦ f u t)
    ((isQuotientMap_cubeToSphere n).lift_comp
      (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
      (targetGenLoopHomotopyCurry_factorsThrough_cubeToSphere n H))

def targetGenLoopSphereMapHomotopy (n : ℕ)
    {α β : GenLoop (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    ContinuousMap.Homotopy (targetGenLoopSphereMap n α) (targetGenLoopSphereMap n β) where
  toContinuousMap := (targetGenLoopSphereHomotopyCurry n H).uncurry.comp ContinuousMap.prodSwap
  map_zero_left z := by
    obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
    change targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) 0 =
      targetGenLoopSphereMap n α (cubeToSphere (n + 1) u)
    rw [targetGenLoopSphereHomotopyCurry_apply_cubeToSphere]
    exact (H.map_zero_left u).trans
      (congrArg (fun f : C((Fin (n + 1) → unitInterval), X) ↦ f u)
        (targetGenLoopSphereMap_comp_cubeToSphere n α)).symm
  map_one_left z := by
    obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
    change targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) 1 =
      targetGenLoopSphereMap n β (cubeToSphere (n + 1) u)
    rw [targetGenLoopSphereHomotopyCurry_apply_cubeToSphere]
    exact (H.map_one_left u).trans
      (congrArg (fun f : C((Fin (n + 1) → unitInterval), X) ↦ f u)
        (targetGenLoopSphereMap_comp_cubeToSphere n β)).symm

theorem targetGenLoopSphereMapHomotopy_basepoint (n : ℕ)
    {α β : GenLoop (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1))))
    (t : unitInterval) :
    targetGenLoopSphereMapHomotopy n H (t, sphereBasepoint (n + 1)) = x := by
  let u : Fin (n + 1) → unitInterval := fun _ ↦ 0
  have hu : u ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  rw [← cubeToSphere_boundary (n + 1) u hu]
  change targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) t = _
  rw [targetGenLoopSphereHomotopyCurry_apply_cubeToSphere, H.eq_fst t hu, α.property u hu]

end BanachIsometric.SphereGenerator
