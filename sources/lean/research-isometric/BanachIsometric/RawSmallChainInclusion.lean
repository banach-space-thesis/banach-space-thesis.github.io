import BanachIsometric.RawSmallChainCoordinates

/-! Pointwise forms of the actual small-chain inclusion and its naturality. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)

theorem exists_rawSmallCoordinates_of_mem (n : ℕ) (c : RawRationalChains X n)
    (hc : c ∈ rawSmallChainCarrier U n) :
    ∃ d : RawSmallCoordinates U n, rawSmallCoordinateInclusion U n d = c := by
  refine ⟨rawSmallCoordinateEquiv U n ⟨c, hc⟩, ?_⟩
  rw [← rawSmallCoordinateEquiv_symm_coe, LinearEquiv.symm_apply_apply]

theorem rawSmallCoordinateInclusion_boundary_apply (n : ℕ) (c : RawSmallCoordinates U (n + 1)) :
    rawBoundary n (rawSmallCoordinateInclusion U (n + 1) c) =
      rawSmallCoordinateInclusion U n (rawSmallCoordinateBoundary U n c) :=
  LinearMap.congr_fun (rawSmallCoordinateInclusion_boundary U n) c

end BanachIsometric.SingularPrism
