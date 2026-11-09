import BanachIsometric.SingularCrossNaturality

/-! The actual homology class of a point and the quotient augmentation
in degree zero. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW VectorChainSplitting

variable (X : Type u) [TopologicalSpace X]

def rawHomologyPoint (x : X) : RawHomology X 0 :=
  rawFactorHomologyProjection X 0 (Finsupp.single (ContinuousMap.const (Simplex 0) x) 1)

def rawFullZeroAugmentation : RawHomology X 0 →ₗ[ℚ] ℚ :=
  (boundaries (rawFactorObjects X) (rawBoundary (X := X)) (rawBoundary_squared (X := X)) 0).liftQ
    ((rawAugmentation X).comp (RawHomologyCycles X 0).subtype) (by
      rintro _ ⟨c, rfl⟩
      exact LinearMap.congr_fun (rawAugmentation_boundary X) c)

@[simp] theorem rawFullZeroAugmentation_projection (c : RawRationalChains X 0) :
    rawFullZeroAugmentation X (rawFactorHomologyProjection X 0 c) = rawAugmentation X c :=
  rfl

@[simp] theorem rawFullZeroAugmentation_point (x : X) :
    rawFullZeroAugmentation X (rawHomologyPoint X x) = 1 :=
  rawAugmentation_single X _ 1

theorem rawFullHomologyMap_point {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    rawFullHomologyMap f 0 (rawHomologyPoint X x) = rawHomologyPoint Y (f x) := by
  let c : RawHomologyCycles X 0 := ⟨Finsupp.single (ContinuousMap.const (Simplex 0) x) 1, trivial⟩
  change rawFullHomologyMap f 0 (rawFactorHomologyProjection X 0 c.val) = _
  rw [rawFullHomologyMap_cycle]
  change rawFactorHomologyProjection Y 0
    (rawChainMap f 0 (Finsupp.single (ContinuousMap.const (Simplex 0) x) 1)) = _
  simp only [rawHomologyPoint, rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

end BanachIsometric.SingularEZ
