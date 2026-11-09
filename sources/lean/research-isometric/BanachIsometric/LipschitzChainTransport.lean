import BanachIsometric.LipschitzNeighborhoodChainComparison
import BanachIsometric.RawSingularHomology

/-! Transport of the actual Lipschitz cycle and filling comparison through
a bi-Lipschitz homeomorphism of target spaces. -/

noncomputable section
namespace BanachIsometric.SingularPrism.LipschitzNeighborhoodRetraction

open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E]
variable {s : Set E} (D : LipschitzNeighborhoodRetraction s)
variable {X : Type*} [PseudoMetricSpace X] (e : X ≃ₜ s)
variable {L M : ℝ≥0} (he : LipschitzWith L e) (hi : LipschitzWith M e.symm)

private def forwardMap : C(X, s) := ⟨e, e.continuous⟩

private def inverseMap : C(s, X) := ⟨e.symm, e.symm.continuous⟩

private theorem rawChainMap_homeomorph_left (n : ℕ) (c : RawRationalChains X n) :
    rawChainMap (inverseMap e) n (rawChainMap (forwardMap e) n c) = c := by
  have h : (inverseMap e).comp (forwardMap e) = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  have hcomp := LinearMap.congr_fun (rawChainMap_comp (forwardMap e) (inverseMap e) n) c
  rw [h, rawChainMap_id] at hcomp
  exact hcomp.symm

variable [NormedSpace ℝ E]

include D e hi in
theorem exists_lipschitz_cycle_representative_homeomorph (n : ℕ)
    (c : RawRationalChains X (n + 1)) (hc : rawBoundary n c = 0) :
    ∃ d : RawRationalChains X (n + 1), d ∈ rawLipschitzCarrier X (n + 1) ∧
      rawBoundary n d = 0 ∧
        ∃ a : RawRationalChains X (n + 2), rawBoundary (n + 1) a = c - d := by
  let f := forwardMap e
  let g := inverseMap e
  have hc' : rawBoundary n (rawChainMap f (n + 1) c) = 0 := by
    have h := LinearMap.congr_fun (rawChainMap_boundary f n) c
    simpa only [LinearMap.comp_apply, hc, map_zero] using h
  obtain ⟨d, hd, hd0, a, ha⟩ := D.exists_lipschitz_cycle_representative n _ hc'
  refine ⟨rawChainMap g (n + 1) d, rawChainMap_preserves_lipschitz g hi (n + 1) hd,
    ?_, rawChainMap g (n + 2) a, ?_⟩
  · have h := LinearMap.congr_fun (rawChainMap_boundary g n) d
    simpa only [LinearMap.comp_apply, hd0, map_zero] using h
  · have h := LinearMap.congr_fun (rawChainMap_boundary g (n + 1)) a
    change rawBoundary (n + 1) (rawChainMap g (n + 2) a) =
      rawChainMap g (n + 1) (rawBoundary (n + 1) a) at h
    rw [h, ha, map_sub]
    exact congrArg (fun x => x - rawChainMap g (n + 1) d) (rawChainMap_homeomorph_left e _ c)

include D e he hi in
theorem exists_lipschitz_boundary_filling_homeomorph (n : ℕ)
    (c : RawRationalChains X (n + 1)) (hc : c ∈ rawLipschitzCarrier X (n + 1))
    (a : RawRationalChains X (n + 2)) (ha : rawBoundary (n + 1) a = c) :
    ∃ b : RawRationalChains X (n + 2), b ∈ rawLipschitzCarrier X (n + 2) ∧
      rawBoundary (n + 1) b = c := by
  let f := forwardMap e
  let g := inverseMap e
  have ha' : rawBoundary (n + 1) (rawChainMap f (n + 2) a) = rawChainMap f (n + 1) c := by
    have h := LinearMap.congr_fun (rawChainMap_boundary f (n + 1)) a
    simpa only [LinearMap.comp_apply, ha] using h
  obtain ⟨b, hb, hb0⟩ := D.exists_lipschitz_boundary_filling n _
    (rawChainMap_preserves_lipschitz f he (n + 1) hc) _ ha'
  refine ⟨rawChainMap g (n + 2) b, rawChainMap_preserves_lipschitz g hi (n + 2) hb, ?_⟩
  have h := LinearMap.congr_fun (rawChainMap_boundary g (n + 1)) b
  change rawBoundary (n + 1) (rawChainMap g (n + 2) b) =
    rawChainMap g (n + 1) (rawBoundary (n + 1) b) at h
  rw [h, hb0]
  exact rawChainMap_homeomorph_left e _ c

end BanachIsometric.SingularPrism.LipschitzNeighborhoodRetraction
