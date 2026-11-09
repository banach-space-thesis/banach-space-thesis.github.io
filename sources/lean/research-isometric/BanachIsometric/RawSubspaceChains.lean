import BanachIsometric.RawSingularChains
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! An actual subspace inclusion identifies its singular chains with the
chains supported on simplices contained in the subspace. This gives the
chain-level overlap and sum formulas for a cover by two sets. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

def rawSubspaceInclusion (U : Set X) : C(U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def rawSubspaceMapOfSubset {U V : Set X} (h : U ⊆ V) : C(U, V) :=
  ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

def rawSubspaceChainInclusion (U : Set X) (n : ℕ) :
    RawRationalChains U n →ₗ[ℚ] RawRationalChains X n :=
  rawChainMap (rawSubspaceInclusion U) n

theorem rawSubspaceChainInclusion_injective (U : Set X) (n : ℕ) :
    Function.Injective (rawSubspaceChainInclusion U n) := by
  apply Finsupp.mapDomain_injective
  intro a b hab
  apply ContinuousMap.ext
  intro z
  exact Subtype.ext (ContinuousMap.congr_fun hab z)

theorem rawSubspaceChainInclusion_boundary (U : Set X) (n : ℕ) :
    (rawBoundary n).comp (rawSubspaceChainInclusion U (n + 1)) =
      (rawSubspaceChainInclusion U n).comp (rawBoundary n) :=
  rawChainMap_boundary (rawSubspaceInclusion U) n

theorem rawSubspaceChainInclusion_boundary_apply (U : Set X) (n : ℕ)
    (c : RawRationalChains U (n + 1)) :
    rawBoundary n (rawSubspaceChainInclusion U (n + 1) c) =
      rawSubspaceChainInclusion U n (rawBoundary n c) :=
  LinearMap.congr_fun (rawSubspaceChainInclusion_boundary U n) c

theorem rawSubspaceChainInclusion_comp {U V : Set X} (h : U ⊆ V) (n : ℕ) :
    (rawSubspaceChainInclusion V n).comp (rawChainMap (rawSubspaceMapOfSubset h) n) =
      rawSubspaceChainInclusion U n := by
  unfold rawSubspaceChainInclusion rawChainMap
  rw [← Finsupp.lmapDomain_comp]
  rfl

theorem rawSubspaceChainInclusion_comp_apply {U V : Set X} (h : U ⊆ V) (n : ℕ)
    (c : RawRationalChains U n) :
    rawSubspaceChainInclusion V n (rawChainMap (rawSubspaceMapOfSubset h) n c) =
      rawSubspaceChainInclusion U n c :=
  LinearMap.congr_fun (rawSubspaceChainInclusion_comp h n) c

theorem range_rawSubspaceChainInclusion (U : Set X) (n : ℕ) :
    LinearMap.range (rawSubspaceChainInclusion U n) =
      Finsupp.supported ℚ ℚ {σ : RawSingularSimplex X n | Set.range σ ⊆ U} := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction with
    | zero =>
        rw [map_zero]
        exact Submodule.zero_mem _
    | single_add σ a c _ _ ih =>
        rw [map_add]
        refine add_mem ?_ ih
        simp only [rawSubspaceChainInclusion, rawChainMap, Finsupp.lmapDomain_apply,
          Finsupp.mapDomain_single]
        apply Finsupp.single_mem_supported ℚ a
        rintro _ ⟨z, rfl⟩
        exact (σ z).property
  · rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    let τ : RawSingularSimplex U n :=
      ⟨fun z => ⟨σ z, hσ (Set.mem_range_self z)⟩, σ.continuous.subtype_mk _⟩
    refine ⟨Finsupp.single τ 1, ?_⟩
    have hτ : (rawSubspaceInclusion U).comp τ = σ := by
      ext z
      rfl
    simp only [rawSubspaceChainInclusion, rawChainMap, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, hτ]

theorem range_rawSubspaceChainInclusion_inter (U V : Set X) (n : ℕ) :
    LinearMap.range (rawSubspaceChainInclusion (U ∩ V) n) =
      LinearMap.range (rawSubspaceChainInclusion U n) ⊓
        LinearMap.range (rawSubspaceChainInclusion V n) := by
  simp only [range_rawSubspaceChainInclusion, ← Finsupp.supported_inter]
  congr 1
  ext σ
  constructor
  · intro h
    exact ⟨fun _ hz => (h hz).1, fun _ hz => (h hz).2⟩
  · rintro ⟨hU, hV⟩
    exact fun _ hz => ⟨hU hz, hV hz⟩

end BanachIsometric.SingularPrism
