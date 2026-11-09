import BanachIsometric.HemisphericalBaseCycle
import BanachIsometric.ExactSectionHemisphere
import BanachIsometric.RawAcyclicFillers

/-! The actual hemisphere contractions give literal prism chains. Their
sphere class agrees with that of any hemisphere chains with the same exact
equator boundary, including the normalized affine cones. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace
open scoped Topology unitInterval

theorem rawChainMap_const_even_cycle_eq_zero {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : Even (n + 1)) (y : Y) (c : rawCycles X n) :
    rawChainMap (ContinuousMap.const X y) (n + 1) c.val = 0 := by
  let f : C(X, Unit) := ContinuousMap.const X Unit.unit
  let g : C(Unit, Y) := ContinuousMap.const Unit y
  let b := rawChainMap f (n + 1) c.val
  let constantSimplex := ContinuousMap.const (Simplex (n + 1)) Unit.unit
  have hb : b = Finsupp.single constantSimplex (b constantSimplex) := rawChain_subsingleton_single (n + 1) Unit.unit b
  have hcycle : rawBoundary n b = 0 := (rawCyclesMap f n c).property
  have hne : ¬ Even (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.even_add_one]
    exact not_not.mpr hn
  rw [hb, rawBoundary_const_single, if_neg hne, one_smul] at hcycle
  have hcoef : b constantSimplex = 0 := by
    have h := congrArg (fun a : RawRationalChains Unit n => a (ContinuousMap.const (Simplex n) Unit.unit)) hcycle
    change Finsupp.single (ContinuousMap.const (Simplex n) Unit.unit) (b constantSimplex)
      (ContinuousMap.const (Simplex n) Unit.unit) = (0 : RawRationalChains Unit n) _ at h
    simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using h
  have hb0 : b = 0 := by rw [hb, hcoef, Finsupp.single_zero]
  change rawChainMap (g.comp f) (n + 1) c.val = 0
  rw [rawChainMap_comp]
  change rawChainMap g (n + 1) b = 0
  rw [hb0, map_zero]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem hemisphereContraction_mem_closedHemisphere (v : sphere (0 : V) 1)
    (z : unitInterval × closedHemisphere v) : hemisphereContraction v z ∈ closedHemisphere v := by
  change 0 ≤ inner ℝ v.val
    (normalize ((1 - (z.1 : ℝ)) • v.val + (z.1 : ℝ) • z.2.val.val))
  simp only [NormedSpace.normalize, real_inner_smul_right, inner_add_right]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2) real_inner_self_nonneg)
      (mul_nonneg z.1.property.1 z.2.property))

def closedHemispherePoleHomotopy (v : sphere (0 : V) 1) :
    (ContinuousMap.const (closedHemisphere v) (hemispherePole v)).Homotopy
      (ContinuousMap.id (closedHemisphere v)) where
  toContinuousMap := ⟨fun z => ⟨hemisphereContraction v z, hemisphereContraction_mem_closedHemisphere v z⟩,
    (hemisphereContraction v).continuous.subtype_mk _⟩
  map_zero_left x := Subtype.ext (hemisphereContraction_zero v x)
  map_one_left x := Subtype.ext (hemisphereContraction_one v x)

theorem closedHemisphere_contractible (v : sphere (0 : V) 1) : ContractibleSpace (closedHemisphere v) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨hemispherePole v, ⟨(closedHemispherePoleHomotopy v).symm⟩⟩

def rawHemispherePrismChain {X : Type*} [TopologicalSpace X] (v : sphere (0 : V) 1)
    (j : C(X, closedHemisphere v)) (n : ℕ) (z : rawCycles X n) :
    RawRationalChains (closedHemisphere v) (n + 2) :=
  rawPrism ((closedHemispherePoleHomotopy v).compContinuousMap j) (n + 1) z.val

theorem rawHemispherePrismChain_boundary {X : Type*} [TopologicalSpace X] (v : sphere (0 : V) 1)
    (j : C(X, closedHemisphere v)) (n : ℕ) (z : rawCycles X n) (heven : Even (n + 1)) :
    rawBoundary (n + 1) (rawHemispherePrismChain v j n z) = rawChainMap j (n + 1) z.val := by
  let H := (closedHemispherePoleHomotopy v).compContinuousMap j
  have h := LinearMap.congr_fun (rawPrism_chain_identity H n) z.val
  change rawBoundary (n + 1) (rawHemispherePrismChain v j n z) +
    rawPrism H n (rawBoundary n z.val) = rawChainMap j (n + 1) z.val -
      rawChainMap (ContinuousMap.const X (hemispherePole v)) (n + 1) z.val at h
  rwa [z.property, map_zero, add_zero, rawChainMap_const_even_cycle_eq_zero n heven, sub_zero] at h

theorem hemisphericalBaseCycle_class_eq (v : sphere (0 : V) 1) (n : ℕ)
    (z : rawCycles (EquatorSphere v) n)
    (bN bN' : RawRationalChains (closedHemisphere v) (n + 2))
    (bS bS' : RawRationalChains (closedHemisphere (-v)) (n + 2))
    (hbN : rawBoundary (n + 1) bN = rawChainMap (equatorNorth v) (n + 1) z.val)
    (hbN' : rawBoundary (n + 1) bN' = rawChainMap (equatorNorth v) (n + 1) z.val)
    (hbS : rawBoundary (n + 1) bS = rawChainMap (equatorSouth v) (n + 1) z.val)
    (hbS' : rawBoundary (n + 1) bS' = rawChainMap (equatorSouth v) (n + 1) z.val) :
    (Submodule.Quotient.mk (hemisphericalBaseCycle v n z bN bS hbN hbS) :
      RawPositiveHomology (sphere (0 : V) 1) (n + 1)) =
        Submodule.Quotient.mk (hemisphericalBaseCycle v n z bN' bS' hbN' hbS') := by
  letI := closedHemisphere_contractible v
  letI := closedHemisphere_contractible (-v)
  obtain ⟨cN, hcN⟩ := raw_positive_cycle_bounds_of_contractible (n + 1) (bN - bN')
    (by rw [map_sub, hbN, hbN', sub_self])
  obtain ⟨cS, hcS⟩ := raw_positive_cycle_bounds_of_contractible (n + 1) (bS - bS')
    (by rw [map_sub, hbS, hbS', sub_self])
  apply (Submodule.Quotient.eq (rawBoundaries (sphere (0 : V) 1) (n + 1))).mpr
  refine ⟨rawChainMap (closedHemisphereInclusion v) (n + 3) cN -
    rawChainMap (closedHemisphereInclusion (-v)) (n + 3) cS, ?_⟩
  apply Subtype.ext
  have hN := LinearMap.congr_fun (rawChainMap_boundary (closedHemisphereInclusion v) (n + 2)) cN
  have hS := LinearMap.congr_fun (rawChainMap_boundary (closedHemisphereInclusion (-v)) (n + 2)) cS
  simp only [LinearMap.comp_apply, hcN, hcS] at hN hS
  change rawBoundary (n + 2) (rawChainMap (closedHemisphereInclusion v) (n + 3) cN -
    rawChainMap (closedHemisphereInclusion (-v)) (n + 3) cS) =
      (rawChainMap (closedHemisphereInclusion v) (n + 2) bN -
        rawChainMap (closedHemisphereInclusion (-v)) (n + 2) bS) -
      (rawChainMap (closedHemisphereInclusion v) (n + 2) bN' -
        rawChainMap (closedHemisphereInclusion (-v)) (n + 2) bS')
  rw [map_sub, hN, hS, map_sub, map_sub]
  abel

end BanachIsometric.SingularPrism
