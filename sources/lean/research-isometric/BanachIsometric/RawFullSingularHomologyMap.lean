import BanachIsometric.SingularKunneth

/-! Continuous maps act on the actual singular homology in every
nonnegative degree. In positive degrees this is the original raw map. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW VectorChainSplitting CategoryTheory

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def rawFullCyclesMap (f : C(X, Y)) (n : ℕ) : RawHomologyCycles X n →ₗ[ℚ] RawHomologyCycles Y n :=
  chainCyclesMap (hd := rawBoundary_squared (X := X)) (he := rawBoundary_squared (X := Y))
    (rawRationalChainMap f) n

def rawFullHomologyMap (f : C(X, Y)) (n : ℕ) : RawHomology X n →ₗ[ℚ] RawHomology Y n :=
  chainHomologyMap (hd := rawBoundary_squared (X := X)) (he := rawBoundary_squared (X := Y))
    (rawRationalChainMap f) n

theorem rawFullHomologyMap_cycle (f : C(X, Y)) (n : ℕ) (c : RawHomologyCycles X n) :
    rawFullHomologyMap f n (rawFactorHomologyProjection X n c.val) =
      rawFactorHomologyProjection Y n (rawChainMap f n c.val) :=
  chainHomologyMap_projection_cycle (hd := rawBoundary_squared (X := X))
    (he := rawBoundary_squared (X := Y)) (rawRationalChainMap f) n c

theorem rawFullHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    rawFullHomologyMap (g.comp f) n = (rawFullHomologyMap g n).comp (rawFullHomologyMap f n) := by
  have h : rawRationalChainMap (g.comp f) = rawRationalChainMap f ≫ rawRationalChainMap g := by
    apply HomologicalComplex.Hom.ext
    funext m
    exact ModuleCat.hom_ext_iff.mpr (rawChainMap_comp f g m)
  simp only [rawFullHomologyMap]
  rw [h]
  exact chainHomologyMap_comp (hd := rawBoundary_squared (X := X))
    (he := rawBoundary_squared (X := Y)) (hb := rawBoundary_squared (X := Z)) _ _ n

theorem rawFullHomologyMap_id (n : ℕ) : rawFullHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
  have h : rawRationalChainMap (ContinuousMap.id X) = 𝟙 (rawRationalChainComplex X) := by
    apply HomologicalComplex.Hom.ext
    funext m
    exact ModuleCat.hom_ext_iff.mpr (rawChainMap_id m)
  simp only [rawFullHomologyMap]
  rw [h]
  exact chainHomologyMap_id (hd := rawBoundary_squared (X := X)) n

theorem rawFullHomologyMap_positive (f : C(X, Y)) (n : ℕ) :
    rawFullHomologyMap f (n + 1) = rawHomologyMap f n := by
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | H c => rfl

end BanachIsometric.SingularEZ
