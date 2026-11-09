import BanachIsometric.RawZeroSingularHomology
import Mathlib.Topology.Homotopy.Contractible

/-! The actual augmentation computes degree-zero singular homology of a
contractible space. This complements the positive-degree face acyclicity. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

def rawAugmentation (X : Type*) [TopologicalSpace X] : RawRationalChains X 0 →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

theorem rawAugmentation_single (X : Type*) [TopologicalSpace X]
    (simplex : RawSingularSimplex X 0) (a : ℚ) :
    rawAugmentation X (Finsupp.single simplex a) = a :=
  Finsupp.lsum_single _ _ _ _

theorem rawAugmentation_boundary (X : Type*) [TopologicalSpace X] :
    (rawAugmentation X).comp (rawBoundary 0) = 0 := by
  apply Finsupp.lhom_ext
  intro simplex a
  simp only [LinearMap.comp_apply, rawBoundary_single, map_sum, map_zsmul,
    rawAugmentation_single, LinearMap.zero_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • a) = 0
  simp [Fin.sum_univ_two]

def rawZeroHomologyAugmentation (X : Type*) [TopologicalSpace X] :
    RawZeroHomology X →ₗ[ℚ] ℚ :=
  (LinearMap.range (rawBoundary (X := X) 0)).liftQ (rawAugmentation X)
    (LinearMap.range_le_ker_iff.mpr (rawAugmentation_boundary X))

def rawZeroHomologyPoint {X : Type*} [TopologicalSpace X] (x : X) :
    ℚ →ₗ[ℚ] RawZeroHomology X :=
  (LinearMap.range (rawBoundary (X := X) 0)).mkQ.comp
    (Finsupp.lsingle (ContinuousMap.const (Simplex 0) x))

theorem rawZeroHomologyAugmentation_point {X : Type*} [TopologicalSpace X] (x : X) :
    (rawZeroHomologyAugmentation X).comp (rawZeroHomologyPoint x) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change rawAugmentation X (Finsupp.single (ContinuousMap.const (Simplex 0) x) a) = a
  exact rawAugmentation_single _ _ _

theorem rawZeroHomologyMap_const_factor {X : Type*} [TopologicalSpace X] (x : X) :
    rawZeroHomologyMap (ContinuousMap.const X x) =
      (rawZeroHomologyPoint x).comp (rawZeroHomologyAugmentation X) := by
  have hc : rawChainMap (ContinuousMap.const X x) 0 =
      (Finsupp.lsingle (ContinuousMap.const (Simplex 0) x)).comp (rawAugmentation X) := by
    apply Finsupp.lhom_ext
    intro simplex a
    simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      LinearMap.comp_apply, rawAugmentation_single, Finsupp.lsingle_apply]
    rfl
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawChainMap (ContinuousMap.const X x) 0 c) =
      Submodule.Quotient.mk (Finsupp.single (ContinuousMap.const (Simplex 0) x) (rawAugmentation X c))
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hc c)

def rawZeroHomologyContractibleEquiv (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] : RawZeroHomology X ≃ₗ[ℚ] ℚ := by
  let x := Classical.choose (id_nullhomotopic X)
  let H := Classical.choice (Classical.choose_spec (id_nullhomotopic X))
  refine LinearEquiv.ofLinear (rawZeroHomologyAugmentation X) (rawZeroHomologyPoint x)
    (rawZeroHomologyAugmentation_point x) ?_
  rw [← rawZeroHomologyMap_const_factor, ← rawZeroHomologyMap_homotopy H, rawZeroHomologyMap_id]

end BanachIsometric.SingularPrism
