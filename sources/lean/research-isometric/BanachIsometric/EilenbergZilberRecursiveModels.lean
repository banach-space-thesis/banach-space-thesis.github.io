import BanachIsometric.EilenbergZilberUniversalBoundary
import BanachIsometric.EilenbergZilberBaseAugmentation

/-! Actual universal Eilenberg--Zilber chains are constructed recursively by
filling on literal contractible simplex products. The universal boundary
identity is proved, including degree one via the actual augmentation. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

def universalBoundaryCandidate {n : ℕ} (U : UniversalProductChains n)
    (p q : ℕ) (_h : p + q = n + 1) : RawRationalChains (Simplex p × Simplex q) n :=
  universalCrossEvaluation U
    (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))

def universalProductFamily : (n : ℕ) → UniversalProductChains n
  | 0 => universalProductBase
  | n + 1 => fun p q h => rawBoundaryChoice n (universalBoundaryCandidate (universalProductFamily n) p q h)

theorem universalBoundaryCandidate_cycle_of_compatible {n : ℕ}
    {U : UniversalProductChains n} {V : UniversalProductChains (n + 1)}
    (hUV : UniversalBoundaryCompatible U V) (p q : ℕ) (h : p + q = (n + 1) + 1) :
    rawBoundary n (universalBoundaryCandidate V p q h) = 0 := by
  have hc := LinearMap.congr_fun
    (universalCrossEvaluation_boundary_of_compatible (X := Simplex p) (Y := Simplex q) hUV)
    (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))
  have hd := LinearMap.congr_fun (rawTensorTotalBoundary_squared (Simplex p) (Simplex q))
    (universalTensorGenerator p q)
  change rawTensorTotalBoundary (Simplex p) (Simplex q)
    (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q)) = 0 at hd
  change rawBoundary n (universalBoundaryCandidate V p q h) =
    universalCrossEvaluation U (rawTensorTotalBoundary (Simplex p) (Simplex q)
      (rawTensorTotalBoundary (Simplex p) (Simplex q) (universalTensorGenerator p q))) at hc
  rw [hd, map_zero] at hc
  exact hc

theorem universalProductFamily_compatible (n : ℕ) :
    UniversalBoundaryCompatible (universalProductFamily n) (universalProductFamily (n + 1)) := by
  induction n with
  | zero =>
    intro p q h
    change rawBoundary 0 (rawBoundaryChoice 0 (universalBoundaryCandidate universalProductBase p q h)) =
      universalBoundaryCandidate universalProductBase p q h
    apply rawBoundaryChoice_spec
    letI := simplex_product_contractible p q
    exact raw_augmentation_zero_bounds_of_contractible _ (universalProductBase_boundary_augmentation p q)
  | succ n ih =>
    intro p q h
    change rawBoundary (n + 1)
      (rawBoundaryChoice (n + 1) (universalBoundaryCandidate (universalProductFamily (n + 1)) p q h)) =
        universalBoundaryCandidate (universalProductFamily (n + 1)) p q h
    apply rawBoundaryChoice_spec
    letI := simplex_product_contractible p q
    exact raw_positive_cycle_bounds_of_contractible n _
      (universalBoundaryCandidate_cycle_of_compatible ih p q h)

end BanachIsometric.SingularEZ
