import BanachIsometric.EilenbergZilberProductModelIdentity

/-! Acyclic-model fillings give a genuine chain homotopy from
crossproduct after Alexander--Whitney to the identity on unnormalized
singular chains of the product. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

def universalProductHomotopyFamily : (n : ℕ) → RawRationalChains (Simplex n × Simplex n) (n + 1)
  | 0 => rawBoundaryChoice 0 (productModelDifference 0)
  | n + 1 => rawBoundaryChoice (n + 1)
      (productModelHomotopyCandidate (universalProductHomotopyFamily n))

theorem universalProductHomotopyFamily_zero :
    rawBoundary 0 (universalProductHomotopyFamily 0) = productModelDifference 0 := by
  apply rawBoundaryChoice_spec
  letI := simplex_product_contractible 0 0
  apply raw_augmentation_zero_bounds_of_contractible
  simp only [productModelDifference, map_sub, rawProductComposite_augmentation, sub_self]

theorem universalProductHomotopyFamily_succ (n : ℕ) :
    rawBoundary (n + 1) (universalProductHomotopyFamily (n + 1)) =
      productModelHomotopyCandidate (universalProductHomotopyFamily n) := by
  induction n with
  | zero =>
    apply rawBoundaryChoice_spec
    letI := simplex_product_contractible 1 1
    apply raw_positive_cycle_bounds_of_contractible
    simp only [productModelHomotopyCandidate, productModelDifference, map_sub,
      rawProductComposite_boundary, productHomotopy_zero_of_model universalProductHomotopyFamily_zero,
      sub_self]
  | succ n ih =>
    apply rawBoundaryChoice_spec
    letI := simplex_product_contractible (n + 2) (n + 2)
    apply raw_positive_cycle_bounds_of_contractible
    have hdd := LinearMap.congr_fun (rawBoundary_squared (X := Simplex (n + 2) × Simplex (n + 2)) n)
      (universalProductGenerator (n + 2))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    simp only [productModelHomotopyCandidate, productModelDifference, map_sub,
      rawProductComposite_boundary, productHomotopy_succ_of_model ih, hdd, map_zero, sub_zero, sub_self]

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def rawProductHomotopy (n : ℕ) :
    RawRationalChains (X × Y) n →ₗ[ℚ] RawRationalChains (X × Y) (n + 1) :=
  universalProductHomotopyEvaluation (universalProductHomotopyFamily n)

theorem rawProductHomotopy_zero (c : RawRationalChains (X × Y) 0) :
    rawBoundary 0 (rawProductHomotopy 0 c) = rawProductComposite 0 c - c :=
  productHomotopy_zero_of_model universalProductHomotopyFamily_zero c

theorem rawProductHomotopy_succ (n : ℕ) (c : RawRationalChains (X × Y) (n + 1)) :
    rawBoundary (n + 1) (rawProductHomotopy (n + 1) c) + rawProductHomotopy n (rawBoundary n c) =
      rawProductComposite (n + 1) c - c := by
  change rawBoundary (n + 1)
    (universalProductHomotopyEvaluation (universalProductHomotopyFamily (n + 1)) c) +
      universalProductHomotopyEvaluation (universalProductHomotopyFamily n) (rawBoundary n c) = _
  rw [productHomotopy_succ_of_model (universalProductHomotopyFamily_succ n), sub_add_cancel]

end BanachIsometric.SingularEZ
