import BanachIsometric.EquatorCoordinates
import BanachIsometric.RawPointHomology

/-! Two actual hemisphere chains with a common equator boundary determine a
sphere cycle. The equator inclusion is explicitly null-homotopic in the sphere. -/

noncomputable section
namespace BanachIsometric
open Set Metric SingularPrism
open scoped Topology unitInterval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def closedHemisphereInclusion (v : sphere (0 : V) 1) :
    C(closedHemisphere v, sphere (0 : V) 1) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem closedHemisphereInclusion_comp_equatorNorth (v : sphere (0 : V) 1) :
    (closedHemisphereInclusion v).comp (equatorNorth v) = equatorInclusion v := rfl

@[simp] theorem closedHemisphereInclusion_comp_equatorSouth (v : sphere (0 : V) 1) :
    (closedHemisphereInclusion (-v)).comp (equatorSouth v) = equatorInclusion v := rfl

def equatorInclusionNullHomotopy (v : sphere (0 : V) 1) :
    (equatorInclusion v).Homotopy (ContinuousMap.const (EquatorSphere v) v) := by
  let H : (ContinuousMap.const (EquatorSphere v) v).Homotopy (equatorInclusion v) := {
    toContinuousMap := (hemisphereContraction v).comp
      ((ContinuousMap.fst : C(unitInterval × EquatorSphere v, unitInterval)).prodMk
        ((equatorNorth v).comp ContinuousMap.snd))
    map_zero_left := fun x => hemisphereContraction_zero v (equatorNorth v x)
    map_one_left := fun x => hemisphereContraction_one v (equatorNorth v x) }
  exact H.symm

theorem rawHomologyMap_equatorInclusion_eq_zero (v : sphere (0 : V) 1) (n : ℕ) :
    rawHomologyMap (equatorInclusion v) n = 0 :=
  rawHomologyMap_nullhomotopic n (equatorInclusion v) v (equatorInclusionNullHomotopy v)

def hemisphericalBaseCycle (v : sphere (0 : V) 1) (n : ℕ) (z : rawCycles (EquatorSphere v) n)
    (bN : RawRationalChains (closedHemisphere v) (n + 2))
    (bS : RawRationalChains (closedHemisphere (-v)) (n + 2))
    (hbN : rawBoundary (n + 1) bN = rawChainMap (equatorNorth v) (n + 1) z.val)
    (hbS : rawBoundary (n + 1) bS = rawChainMap (equatorSouth v) (n + 1) z.val) :
    rawCycles (sphere (0 : V) 1) (n + 1) := by
  refine ⟨rawChainMap (closedHemisphereInclusion v) (n + 2) bN -
    rawChainMap (closedHemisphereInclusion (-v)) (n + 2) bS, ?_⟩
  have hN := LinearMap.congr_fun (rawChainMap_boundary (closedHemisphereInclusion v) (n + 1)) bN
  have hS := LinearMap.congr_fun (rawChainMap_boundary (closedHemisphereInclusion (-v)) (n + 1)) bS
  have hCompN := LinearMap.congr_fun
    (rawChainMap_comp (equatorNorth v) (closedHemisphereInclusion v) (n + 1)) z.val
  have hCompS := LinearMap.congr_fun
    (rawChainMap_comp (equatorSouth v) (closedHemisphereInclusion (-v)) (n + 1)) z.val
  simp only [LinearMap.comp_apply, hbN, hbS] at hN hS
  simp only [LinearMap.comp_apply, closedHemisphereInclusion_comp_equatorNorth,
    closedHemisphereInclusion_comp_equatorSouth] at hCompN hCompS
  change rawBoundary (n + 1) (rawChainMap (closedHemisphereInclusion v) (n + 2) bN -
    rawChainMap (closedHemisphereInclusion (-v)) (n + 2) bS) = 0
  rw [map_sub, hN, hS, ← hCompN, ← hCompS, sub_self]

end BanachIsometric
