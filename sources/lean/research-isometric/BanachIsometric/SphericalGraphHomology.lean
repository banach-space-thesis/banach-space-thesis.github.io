import BanachIsometric.SplitGraphHomology
import BanachIsometric.SphereSeparatedPinch

/-! The actual sphere pinches give the graph formula in singular homology.
In particular, a spherical homology class satisfies the diagonal identity
in the actual product space. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open SphereGenerator
open scoped Topology

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]

theorem rawHomologyMap_graph_split_of_sphere_homeomorph
    (n : ℕ) (e : X ≃ₜ Sph (n + 1)) (g : C(X, G)) (j : ℕ) (z : rawCycles X j) :
    rawHomologyMap (rawGraphMap g) j (Submodule.Quotient.mk z) =
      rawHomologyMap (rawGraphMap (ContinuousMap.const X (g (e.symm (sphereBasepoint (n + 1))))))
        j (Submodule.Quotient.mk z) +
      rawHomologyMap (rawVerticalGraph (e.symm (sphereBasepoint (n + 1)))) j
        (rawHomologyMap g j (Submodule.Quotient.mk z)) := by
  let forward : C(X, Sph (n + 1)) := ⟨e, e.continuous⟩
  let back : C(Sph (n + 1), X) := ⟨e.symm, e.symm.continuous⟩
  let pinch (b : Bool) := back.comp ((sphereBoxPinch n b).comp forward)
  let U (b : Bool) := forward ⁻¹' spherePinchOpenCover n b
  let x₀ := e.symm (sphereBasepoint (n + 1))
  have hOpen (b : Bool) : IsOpen (U b) := (isOpen_spherePinchOpenCover n b).preimage forward.continuous
  have hCover (x : X) : ∃ b, x ∈ U b := mem_spherePinchOpenCover n (e x)
  have hPinch (b : Bool) (x : X) (hx : x ∈ U b) : pinch b x = x₀ := by
    change e.symm (sphereBoxPinch n b (e x)) = x₀
    rw [sphereBoxPinch_eq_basepoint_of_notMem n b (e x) hx]
  have hid : back.comp ((ContinuousMap.id (Sph (n + 1))).comp forward) = ContinuousMap.id X := by
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply x
  let H (b : Bool) : (ContinuousMap.id X).Homotopy (pinch b) :=
    ((ContinuousMap.Homotopy.refl back).comp
      ((sphereBoxPinchHomotopy n b).compContinuousMap forward)).cast hid rfl
  exact rawHomologyMap_graph_split (pinch false) (pinch true) g x₀ U hOpen hCover
    (hPinch false) (hPinch true) (H false) (H true) j z

theorem rawHomologyMap_graph_eq_constant_of_sphere_class_zero
    (n : ℕ) (e : X ≃ₜ Sph (n + 1)) (g : C(X, G)) (g₀ : G)
    (hbase : g (e.symm (sphereBasepoint (n + 1))) = g₀)
    (j : ℕ) (z : rawCycles X j) (hz : rawHomologyMap g j (Submodule.Quotient.mk z) = 0) :
    rawHomologyMap (rawGraphMap g) j (Submodule.Quotient.mk z) =
      rawHomologyMap (rawGraphMap (ContinuousMap.const X g₀)) j (Submodule.Quotient.mk z) := by
  have h := rawHomologyMap_graph_split_of_sphere_homeomorph n e g j z
  rwa [hbase, hz, map_zero, add_zero] at h

private theorem homologyMap_apply_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (j : ℕ) (z : RawPositiveHomology X j) :
    rawHomologyMap g j (rawHomologyMap f j z) = rawHomologyMap (g.comp f) j z :=
  (LinearMap.congr_fun (rawHomologyMap_comp f g j) z).symm

theorem rawHomologyMap_diagonal_sphere_image
    (n : ℕ) (e : X ≃ₜ Sph (n + 1)) (f : C(X, G)) (j : ℕ) (z : rawCycles X j) :
    let x₀ := e.symm (sphereBasepoint (n + 1))
    let a := rawHomologyMap f j (Submodule.Quotient.mk z)
    rawHomologyMap (rawGraphMap (ContinuousMap.id G)) j a =
      rawHomologyMap (rawGraphMap (ContinuousMap.const G (f x₀))) j a +
        rawHomologyMap (rawVerticalGraph (f x₀)) j a := by
  let x₀ := e.symm (sphereBasepoint (n + 1))
  let pair : C(X × X, G × G) := (f.comp ContinuousMap.fst).prodMk (f.comp ContinuousMap.snd)
  have hd : pair.comp (rawGraphMap (ContinuousMap.id X)) = (rawGraphMap (ContinuousMap.id G)).comp f := rfl
  have hh : pair.comp (rawGraphMap (ContinuousMap.const X x₀)) =
      (rawGraphMap (ContinuousMap.const G (f x₀))).comp f := rfl
  have hv : pair.comp (rawVerticalGraph x₀) = (rawVerticalGraph (f x₀)).comp f := rfl
  have h := congrArg (fun a : RawPositiveHomology (X × X) j => rawHomologyMap pair j a)
    (rawHomologyMap_graph_split_of_sphere_homeomorph n e (ContinuousMap.id X) j z)
  change rawHomologyMap pair j (rawHomologyMap (rawGraphMap (ContinuousMap.id X)) j (Submodule.Quotient.mk z)) =
    rawHomologyMap pair j
      (rawHomologyMap (rawGraphMap (ContinuousMap.const X x₀)) j (Submodule.Quotient.mk z) +
        rawHomologyMap (rawVerticalGraph x₀) j
          (rawHomologyMap (ContinuousMap.id X) j (Submodule.Quotient.mk z))) at h
  rw [map_add] at h
  simp only [rawHomologyMap_id, LinearMap.id_apply, homologyMap_apply_apply, hd, hh, hv] at h
  simpa only [homologyMap_apply_apply] using h

end BanachIsometric.SingularPrism
