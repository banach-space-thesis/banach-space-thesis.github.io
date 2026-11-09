import BanachIsometric.CubicalSphereDescent
import BanachIsometric.ProductHigherHomotopy
import BanachIsometric.RawSingularHomotopyInvariance

/-!
# Actual homotopy classes act on actual sphere singular homology

A chosen homology class of the genuine sphere is pushed forward along the
actual descended sphere map of a cubical representative. The proved prism
homotopy invariance makes this well defined on Mathlib's ACTUAL homotopy
quotient. Naturality is also proved.

This is not yet a rational Hurewicz isomorphism: no canonical fundamental
generator, group additivity, or rational injectivity is assumed or asserted.
The source sphere and homology both have degree n+1.
-/

noncomputable section
namespace BanachIsometric.SingularPrism

open SphereGenerator
open scoped Topology Topology.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def sphereHomologyEvaluation (n : ℕ) (z : RawPositiveHomology (Sph (n + 1)) n) :
    HomotopyGroup (Fin (n + 1)) X x → RawPositiveHomology X n :=
  Quotient.lift
    (fun α : GenLoop (Fin (n + 1)) X x => rawHomologyMap (targetGenLoopSphereMap n α) n z)
    (by
      intro α β h
      obtain ⟨H⟩ := h
      exact LinearMap.congr_fun
        (rawHomologyMap_homotopy (targetGenLoopSphereMapHomotopy n H) n) z)

@[simp] theorem sphereHomologyEvaluation_class (n : ℕ)
    (z : RawPositiveHomology (Sph (n + 1)) n) (α : GenLoop (Fin (n + 1)) X x) :
    sphereHomologyEvaluation n z (genLoopClass α) =
      rawHomologyMap (targetGenLoopSphereMap n α) n z := rfl

theorem sphereHomologyEvaluation_natural (n : ℕ)
    (z : RawPositiveHomology (Sph (n + 1)) n) (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHomologyEvaluation n z (basedHomotopyGroupMap f hf a) =
      rawHomologyMap f n (sphereHomologyEvaluation n z a) := by
  induction a using Quotient.inductionOn with
  | h α =>
      change rawHomologyMap (targetGenLoopSphereMap n (mapGenLoop f hf α)) n z =
        rawHomologyMap f n (rawHomologyMap (targetGenLoopSphereMap n α) n z)
      rw [targetGenLoopSphereMap_mapGenLoop, rawHomologyMap_comp]
      rfl

theorem sphereHomologyEvaluation_homotopic_targets (n : ℕ)
    (z : RawPositiveHomology (Sph (n + 1)) n) (α β : GenLoop (Fin (n + 1)) X x)
    (h : GenLoop.Homotopic α β) :
    rawHomologyMap (targetGenLoopSphereMap n α) n z =
      rawHomologyMap (targetGenLoopSphereMap n β) n z := by
  exact congrArg (sphereHomologyEvaluation n z) (Quotient.sound h)

end BanachIsometric.SingularPrism
