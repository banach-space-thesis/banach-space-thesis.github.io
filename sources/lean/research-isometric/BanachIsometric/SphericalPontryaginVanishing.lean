import BanachIsometric.SphericalGraphHomology
import BanachIsometric.SingularPontryaginCoproduct
import BanachIsometric.RawDegreeHomology

/-! A based spherical class of positive even degree vanishes in the actual
rational homology of a topological monoid whose homology is bounded above. -/

noncomputable section
universe u
namespace BanachIsometric.SingularPrism
open SphereGenerator SingularAW SingularEZ
open scoped Topology

variable {X : Type*} {G : Type u} [TopologicalSpace X] [TopologicalSpace G] [Monoid G] [ContinuousMul G]

theorem rawHomologyMap_even_sphere_image_zero
    (N : ℕ) (hBound : ∀ q, N < q → Subsingleton (RawDegreeHomology G q))
    (n : ℕ) (e : X ≃ₜ Sph (n + 1)) (f : C(X, G))
    (hf : f (e.symm (sphereBasepoint (n + 1))) = 1)
    (j : ℕ) (hj : Even (j + 1)) (z : rawCycles X j) :
    rawHomologyMap f j (Submodule.Quotient.mk z) = 0 := by
  let a : RawHomology G (j + 1) := rawHomologyMap f j (Submodule.Quotient.mk z)
  have hb (q : ℕ) (hq : N < q) : Subsingleton (RawHomology G q) := by
    cases q with
    | zero => omega
    | succ q => exact hBound (q + 1) hq
  change a = 0
  apply rawPontryagin_even_class_zero_of_diagonal_graph_sum G N hb (Nat.succ_pos _) hj a
  simp only [rawFullHomologyMap_positive]
  have h := rawHomologyMap_diagonal_sphere_image n e f j z
  change rawHomologyMap (rawGraphMap (ContinuousMap.id G)) j a =
    rawHomologyMap (rawGraphMap (ContinuousMap.const G (f (e.symm (sphereBasepoint (n + 1)))))) j a +
      rawHomologyMap (rawVerticalGraph (f (e.symm (sphereBasepoint (n + 1))))) j a at h
  rw [hf] at h
  exact h

end BanachIsometric.SingularPrism
