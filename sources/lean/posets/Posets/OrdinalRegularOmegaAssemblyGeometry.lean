import Posets.OrdinalRegularOmegaAssemblyClosure

/-! Geometric specialization: each coordinate map and its section build
the insertion itself by pullback and zero extension. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
  {L : ℕ → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
local instance ordinalOmegaGeometryCoordinateGroup (i : ℕ) : NormedAddCommGroup C(L i, 𝕜) := inferInstance
local instance ordinalOmegaGeometryCoordinateSpace (i : ℕ) : NormedSpace 𝕜 C(L i, 𝕜) := inferInstance
local instance ordinalOmegaGeometrySumGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaGeometrySumSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaGeometryDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance ordinalOmegaGeometryDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

variable (H : ℕ → Set K) [∀ i, CompactSpace (H i)]
  (hH : Pairwise (fun i j => Disjoint (H i) (H j))) (hHo : ∀ i, IsClopen (H i))
  (p : ∀ i, C(H i, L i)) (q : ∀ i, C(L i, H i))
  (hsection : ∀ i, Function.RightInverse (q i) (p i))

def ordinalOmegaGeometricInsertion : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K :=
  wolfeDisjointSynthesis H hH
    (fun i => ordinalOmegaBandInsertIsometry (𝕜 := 𝕜) H i (hHo i) (p i) (q i) (hsection i))
    (fun i f => ordinalBandInsert_support (𝕜 := 𝕜) (H i) (hHo i) (p i) f)

theorem ordinalOmegaGeometricInsertion_norm (f : OrdinalBlockFunctionSum 𝕜 L) :
    ‖ordinalOmegaGeometricInsertion H hH hHo p q hsection f‖ = ‖f‖ :=
  wolfeDisjointSynthesis_norm H hH _ _ f

theorem ordinalOmega_geometric_factors_from_leaf_mass
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hqescape : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, (q i x).val ∈ U)
    (S : ℕ → Set K) (hSH : ∀ i, S i ⊆ H i)
    (hq : ∀ i x, (q i x).val ∈ closure (S i))
    (V : ℕ → K → Set K) (hVH : ∀ i y, y ∈ S i → V i y ⊆ H i)
    (hV : ∀ i y, y ∈ S i → IsClopen (V i y))
    (hcV : ∀ i y, y ∈ S i → IsCompact (V i y))
    (hp : ∀ i y (hy : y ∈ S i) z (hz : z ∈ V i y),
      p i ⟨z, hVH i y hy hz⟩ = p i ⟨y, hSH i hy⟩)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 10 * ε < d)
    (hd : ∀ i y (hy : y ∈ S i),
      d ≤ ‖T (JLMS.clopenIndicator (V i y) (hV i y hy) (hcV i y hy)) y‖)
    (hmass : ∀ i y, y ∈ S i → ‖JLMS.atomicRestriction M (H i \ V i y)
      ((JLMS.evaluation y).comp T)‖ ≤ ε)
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation (q i x).val).comp T)‖ ≤ ε) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] OrdinalBlockFunctionSum 𝕜 L,
      R.comp (T.comp (ordinalOmegaGeometricInsertion H hH hHo p q hsection)) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 1 / (d - 10 * ε) := by
  let J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K :=
    fun i => ordinalOmegaBandInsertIsometry (𝕜 := 𝕜) H i (hHo i) (p i) (q i) (hsection i)
  let qK : ∀ i, C(L i, K) := fun i =>
    ⟨fun x => (q i x).val, continuous_subtype_val.comp (q i).continuous⟩
  have hsupp : ∀ i f, Function.support (J i f) ⊆ H i :=
    fun i f => ordinalBandInsert_support (𝕜 := 𝕜) (H i) (hHo i) (p i) f
  have hread : ∀ i (f : C(L i, 𝕜)) x, J i f (qK i x) = f x := by
    intro i f x
    exact ordinalBandInsert_read (H i) (hHo i) (p i) (q i) (hsection i) f x
  have hconst : ∀ i y, y ∈ S i → ∀ f : C(L i, 𝕜), ∀ z ∈ V i y, J i f z = J i f y := by
    intro i y hy f z hz
    exact ordinalBandInsert_constant_on_fiber (H i) (hHo i) (p i) f
      ⟨z, hVH i y hy hz⟩ ⟨y, hSH i hy⟩ (hp i y hy z hz)
  exact ordinalOmega_factors_from_ambient_leaf_mass M T H hH hHo
    (fun i => isCompact_iff_compactSpace.mpr inferInstance) J hsupp qK hqescape S hq hread
    V hVH hV hcV hconst hε hgap hd hmass hcross

end Posets
