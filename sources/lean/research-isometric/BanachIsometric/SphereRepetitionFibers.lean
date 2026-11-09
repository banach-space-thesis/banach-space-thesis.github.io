import BanachIsometric.GenLoopFiberSplit
import BanachIsometric.SphereRepetition

/-! Exact finite fibers of the actual repetition map. Over every non-pole
target, `sphereRepetition n d` has precisely `d` preimages. The proof is the
literal half-cube fiber equivalence and exact cube quotient fibers; no signed
degree, orientation or regularity law is assumed. -/

noncomputable section
namespace BanachIsometric
open scoped Topology Topology.Homotopy unitInterval

variable {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x z : X}

theorem finite_repeatGenLoop_fiber (i : N) (p : GenLoop N X x) (hz : z ≠ x)
    [Finite {u : N → unitInterval // p u = z}] (d : ℕ) :
    Finite {u : N → unitInterval // repeatGenLoop i p d u = z} := by
  induction d with
  | zero =>
    haveI : IsEmpty {u : N → unitInterval // repeatGenLoop i p 0 u = z} := ⟨fun u => hz u.property.symm⟩
    infer_instance
  | succ d ih =>
    letI := ih
    exact Finite.of_equiv _ (transAtFiberEquiv i (repeatGenLoop i p d) p hz)

theorem card_repeatGenLoop_fiber (i : N) (p : GenLoop N X x) (hz : z ≠ x)
    [Finite {u : N → unitInterval // p u = z}] (d : ℕ) :
    Nat.card {u : N → unitInterval // repeatGenLoop i p d u = z} =
      d * Nat.card {u : N → unitInterval // p u = z} := by
  induction d with
  | zero =>
    haveI : IsEmpty {u : N → unitInterval // repeatGenLoop i p 0 u = z} := ⟨fun u => hz u.property.symm⟩
    rw [Nat.zero_mul]
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
  | succ d ih =>
    letI := finite_repeatGenLoop_fiber i p hz d
    change Nat.card {u : N → unitInterval // GenLoop.transAt i (repeatGenLoop i p d) p u = z} = _
    rw [← Nat.card_congr (transAtFiberEquiv i (repeatGenLoop i p d) p hz), Nat.card_sum, ih]
    ring

namespace SphereGenerator

theorem subsingleton_cubeToSphere_fiber (n : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) :
    Subsingleton {u : Fin (n + 1) → unitInterval // cubeToSphere (n + 1) u = z} := by
  constructor
  intro u v
  apply Subtype.ext
  rcases (cubeToSphere_eq_iff _ _ _).mp (u.property.trans v.property.symm) with he | ⟨hu, _⟩
  · exact he
  · exact (hz (u.property.symm.trans (cubeToSphere_boundary _ _ hu))).elim

theorem card_cubeToSphere_fiber (n : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) :
    Nat.card {u : Fin (n + 1) → unitInterval // cubeToSphere (n + 1) u = z} = 1 := by
  letI := subsingleton_cubeToSphere_fiber n z hz
  obtain ⟨u, hu⟩ := cubeToSphere_surjective n z
  letI : Nonempty {u : Fin (n + 1) → unitInterval // cubeToSphere (n + 1) u = z} := ⟨⟨u, hu⟩⟩
  exact Nat.card_unique

def sphereDescentFiberMap (n : ℕ) (α : GenLoop (Fin (n + 1)) X x) :
    {u : Fin (n + 1) → unitInterval // α u = z} →
      {w : Sph (n + 1) // targetGenLoopSphereMap n α w = z} := fun u =>
  ⟨cubeToSphere (n + 1) u.val,
    (congrArg (fun g : C((Fin (n + 1) → unitInterval), X) => g u.val)
      (targetGenLoopSphereMap_comp_cubeToSphere n α)).trans u.property⟩

def sphereDescentFiberEquiv (n : ℕ) (α : GenLoop (Fin (n + 1)) X x) (hz : z ≠ x) :
    {u : Fin (n + 1) → unitInterval // α u = z} ≃
      {w : Sph (n + 1) // targetGenLoopSphereMap n α w = z} :=
  Equiv.ofBijective (sphereDescentFiberMap n α) ⟨by
    intro u v he
    have hγ : cubeToSphere (n + 1) u.val = cubeToSphere (n + 1) v.val := congrArg Subtype.val he
    apply Subtype.ext
    rcases (cubeToSphere_eq_iff _ _ _).mp hγ with heq | ⟨hu, _⟩
    · exact heq
    · exact (hz (u.property.symm.trans (α.property u.val hu))).elim,
    by
      intro w
      obtain ⟨u, hu⟩ := cubeToSphere_surjective n w.val
      have hα : α u = z := by
        have h := congrArg (fun g : C((Fin (n + 1) → unitInterval), X) => g u)
          (targetGenLoopSphereMap_comp_cubeToSphere n α)
        change targetGenLoopSphereMap n α (cubeToSphere (n + 1) u) = α u at h
        exact h.symm.trans ((congrArg (targetGenLoopSphereMap n α) hu).trans w.property)
      exact ⟨⟨u, hα⟩, Subtype.ext hu⟩⟩

theorem finite_sphereRepetition_fiber (n d : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) :
    Finite {w : Sph (n + 1) // sphereRepetition n d w = z} := by
  letI : Subsingleton {u : Fin (n + 1) → unitInterval // sphereGenerator (n + 1) u = z} :=
    subsingleton_cubeToSphere_fiber n z hz
  letI := finite_repeatGenLoop_fiber (0 : Fin (n + 1)) (sphereGenerator (n + 1)) hz d
  exact Finite.of_equiv _ (sphereDescentFiberEquiv n
    (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d) hz)

theorem card_sphereRepetition_fiber (n d : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) :
    Nat.card {w : Sph (n + 1) // sphereRepetition n d w = z} = d := by
  letI : Subsingleton {u : Fin (n + 1) → unitInterval // sphereGenerator (n + 1) u = z} :=
    subsingleton_cubeToSphere_fiber n z hz
  change Nat.card {w : Sph (n + 1) // targetGenLoopSphereMap n
    (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d) w = z} = d
  rw [← Nat.card_congr (sphereDescentFiberEquiv n
    (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d) hz)]
  rw [card_repeatGenLoop_fiber _ _ hz]
  change d * Nat.card {u : Fin (n + 1) → unitInterval // cubeToSphere (n + 1) u = z} = d
  rw [card_cubeToSphere_fiber n z hz, mul_one]

end SphereGenerator
end BanachIsometric
