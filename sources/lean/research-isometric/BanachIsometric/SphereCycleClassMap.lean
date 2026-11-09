import BanachIsometric.CanonicalSphereCycle
import BanachIsometric.SphereHomologyEvaluation
import BanachIsometric.RawPointHomology

/-! A natural map from actual homotopy classes to actual singular homology,
using the explicitly constructed sphere cycle. It kills the constant class.
Additivity, the sphere-generator identification, and rational injectivity
remain separate obligations and are not premises or conclusions here. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open SphereGenerator
open scoped Topology Topology.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def sphereCycleClassMap (n : ℕ) :
    HomotopyGroup (Fin (n + 1)) X x → RawPositiveHomology X n :=
  sphereHomologyEvaluation n (canonicalSphereClass n)

@[simp] theorem sphereCycleClassMap_class (n : ℕ)
    (α : GenLoop (Fin (n + 1)) X x) :
    sphereCycleClassMap n (genLoopClass α) =
      rawHomologyMap (targetGenLoopSphereMap n α) n (canonicalSphereClass n) := rfl

@[simp] theorem sphereCycleClassMap_one (n : ℕ) :
    sphereCycleClassMap (x := x) n 1 = 0 := by
  change rawHomologyMap (targetGenLoopSphereMap n
    (GenLoop.const : GenLoop (Fin (n + 1)) X x)) n (canonicalSphereClass n) = 0
  rw [targetGenLoopSphereMap_const, rawHomologyMap_const]
  rfl

theorem sphereCycleClassMap_natural (n : ℕ) (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereCycleClassMap n (basedHomotopyGroupMap f hf a) =
      rawHomologyMap f n (sphereCycleClassMap n a) :=
  sphereHomologyEvaluation_natural n (canonicalSphereClass n) f hf a

end BanachIsometric.SingularPrism
