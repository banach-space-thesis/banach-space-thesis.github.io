import BanachIsometric.AffineSubdivisionCarrier

/-! Affine chains carried by an actual convex subset realize as genuine
singular chains of that subset, with its inherited topology. The ambient
comparison is proved, retaining all original affine coordinates. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineCarrierSimplex {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : {v : Fin (n + 1) → E // ∀ i, v i ∈ s}) : RawSingularSimplex s n where
  toFun w := ⟨affineSingularSimplex v.val w, affineSingularSimplex_mem_convex hs v.val v.property w⟩
  continuous_toFun := (affineSingularSimplex v.val).continuous.subtype_mk _

def affineCarrierInclusion (s : Set E) : C(s, E) := ⟨Subtype.val, continuous_subtype_val⟩

theorem affineCarrierSimplex_ambient {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : {v : Fin (n + 1) → E // ∀ i, v i ∈ s}) :
    (affineCarrierInclusion s).comp (affineCarrierSimplex hs v) = affineSingularSimplex v.val := rfl

def affineCarrierRealization {s : Set E} (hs : Convex ℝ s) (n : ℕ) :
    affineCarrier s n →ₗ[ℚ] RawRationalChains s n :=
  (Finsupp.lmapDomain ℚ ℚ (affineCarrierSimplex hs)).comp
    (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) {v : Fin (n + 1) → E | ∀ i, v i ∈ s}).toLinearMap

theorem affineCarrierRealization_single {s : Set E} (hs : Convex ℝ s) (n : ℕ)
    (v : Fin (n + 1) → E) (hv : ∀ i, v i ∈ s) (a : ℚ) :
    affineCarrierRealization hs n ⟨Finsupp.single v a, Finsupp.single_mem_supported ℚ a hv⟩ =
      Finsupp.single (affineCarrierSimplex hs ⟨v, hv⟩) a := by
  let e := Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    {v : Fin (n + 1) → E | ∀ i, v i ∈ s}
  have hc : (⟨Finsupp.single v a, Finsupp.single_mem_supported ℚ a hv⟩ : affineCarrier s n) =
      e.symm (Finsupp.single ⟨v, hv⟩ a) := by
    apply Subtype.ext
    exact (Finsupp.supportedEquivFinsupp_symm_single (M := ℚ) (R := ℚ)
      {v : Fin (n + 1) → E | ∀ i, v i ∈ s} ⟨v, hv⟩ a).symm
  change Finsupp.lmapDomain ℚ ℚ (affineCarrierSimplex hs) (e _) = _
  rw [hc, e.apply_symm_apply]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem affineCarrierRealization_ambient {s : Set E} (hs : Convex ℝ s) (n : ℕ) :
    (rawChainMap (affineCarrierInclusion s) n).comp (affineCarrierRealization hs n) =
      (affineChainRealization n).comp (affineCarrier s n).subtype := by
  let e := Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    {v : Fin (n + 1) → E | ∀ i, v i ∈ s}
  have h : ((rawChainMap (affineCarrierInclusion s) n).comp
        (affineCarrierRealization hs n)).comp e.symm.toLinearMap =
      ((affineChainRealization n).comp (affineCarrier s n).subtype).comp e.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro v a
    have hc : e.symm (Finsupp.single v a) =
        (⟨Finsupp.single v.val a, Finsupp.single_mem_supported ℚ a v.property⟩ : affineCarrier s n) := by
      apply Subtype.ext
      exact Finsupp.supportedEquivFinsupp_symm_single (M := ℚ) (R := ℚ)
        {v : Fin (n + 1) → E | ∀ i, v i ∈ s} v a
    change rawChainMap (affineCarrierInclusion s) n
        (affineCarrierRealization hs n (e.symm (Finsupp.single v a))) =
      affineChainRealization n (e.symm (Finsupp.single v a)).val
    rw [hc, affineCarrierRealization_single]
    change rawChainMap (affineCarrierInclusion s) n
        (Finsupp.single (affineCarrierSimplex hs v) a) =
      affineChainRealization n (Finsupp.single v.val a)
    simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      affineCarrierSimplex_ambient, affineChainRealization_single]
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ := e.symm.surjective c
  exact LinearMap.congr_fun h d

end BanachIsometric.SingularPrism
