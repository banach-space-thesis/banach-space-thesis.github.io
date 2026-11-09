import BanachIsometric.FiniteNerveSimplicialSet
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import BanachIsometric.RationalFreeModule
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Actual rational simplicial chains of a finite face complex. The ordinary
strict ordered faces form a boundary-invariant submodule of the free
simplicial module on weakly ordered vertex tuples. The chain relation is
proved using the actual alternating-face identity, not an assumed boundary.
These are combinatorial chains; no singular realization comparison is used. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open CategoryTheory Simplicial AlgebraicTopology Module

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def weakRationalSimplicialModule (K : Complex ι) : SimplicialObject (ModuleCat ℚ) :=
  (orderedSimplicialSet K) ⋙ rationalFreeModule

abbrev WeakRationalChains (K : Complex ι) (n : ℕ) := OrderedSimplex K n →₀ ℚ

def weakRationalBoundary (K : Complex ι) (n : ℕ) :
    WeakRationalChains K (n + 1) →ₗ[ℚ] WeakRationalChains K n :=
  (AlternatingFaceMapComplex.objD (weakRationalSimplicialModule K) n).hom

theorem weakRationalBoundary_squared (K : Complex ι) (n : ℕ) :
    (weakRationalBoundary K n).comp (weakRationalBoundary K (n + 1)) = 0 :=
  ModuleCat.hom_ext_iff.mp (AlternatingFaceMapComplex.d_squared (weakRationalSimplicialModule K) n)

theorem weakRationalBoundary_single (K : Complex ι) (n : ℕ) (v : OrderedSimplex K (n + 1)) :
    weakRationalBoundary K n (Finsupp.single v 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (orderedFace K i v) 1 := by
  have he : weakRationalBoundary K n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.lmapDomain ℚ ℚ (orderedFace K i) := by
    simp only [weakRationalBoundary, AlternatingFaceMapComplex.objD,
      ModuleCat.hom_sum, ModuleCat.hom_smul]
    rfl
  rw [he]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact rationalFreeModule_map_single (orderedFace K i) v 1

def strictSupported (K : Complex ι) (n : ℕ) : Submodule ℚ (WeakRationalChains K n) :=
  Finsupp.supported ℚ ℚ {v | StrictMono v.val}

abbrev RationalChains (K : Complex ι) (n : ℕ) := strictSupported K n

def rationalChainBasis (K : Complex ι) (n : ℕ) :
    Basis (StrictOrderedSimplex K n) ℚ (RationalChains K n) :=
  (Finsupp.basisSingleOne : Basis (StrictOrderedSimplex K n) ℚ (StrictOrderedSimplex K n →₀ ℚ)).map
    (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) {v : OrderedSimplex K n | StrictMono v.val}).symm

@[simp] theorem rationalChainBasis_coe (K : Complex ι) (n : ℕ) (v : StrictOrderedSimplex K n) :
    (rationalChainBasis K n v : WeakRationalChains K n) = Finsupp.single v.val 1 := by
  simpa only [rationalChainBasis, Basis.map_apply, Finsupp.coe_basisSingleOne] using
    Finsupp.supportedEquivFinsupp_symm_single (M := ℚ) (R := ℚ)
      {v : OrderedSimplex K n | StrictMono v.val} v (1 : ℚ)

instance (K : Complex ι) (n : ℕ) : FiniteDimensional ℚ (WeakRationalChains K n) := by
  infer_instance

instance (K : Complex ι) (n : ℕ) : FiniteDimensional ℚ (RationalChains K n) := by
  infer_instance

theorem weakRationalBoundary_mem_strict (K : Complex ι) (n : ℕ) :
    strictSupported K (n + 1) ≤ (strictSupported K n).comap (weakRationalBoundary K n) := by
  rw [strictSupported, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  change weakRationalBoundary K n (Finsupp.single v 1) ∈ strictSupported K n
  rw [weakRationalBoundary_single]
  apply Submodule.sum_mem
  intro i _
  exact (strictSupported K n).toAddSubgroup.zsmul_mem
    (Finsupp.single_mem_supported ℚ 1 (orderedFace_strictMono K i v hv)) _

def rationalBoundary (K : Complex ι) (n : ℕ) : RationalChains K (n + 1) →ₗ[ℚ] RationalChains K n :=
  ((weakRationalBoundary K n).comp (strictSupported K (n + 1)).subtype).codRestrict
    (strictSupported K n) (fun x => weakRationalBoundary_mem_strict K n x.property)

@[simp] theorem rationalBoundary_coe (K : Complex ι) (n : ℕ) (x : RationalChains K (n + 1)) :
    (rationalBoundary K n x : WeakRationalChains K n) = weakRationalBoundary K n x.val := rfl

theorem rationalBoundary_basis (K : Complex ι) (n : ℕ) (v : StrictOrderedSimplex K (n + 1)) :
    rationalBoundary K n (rationalChainBasis K (n + 1) v) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • rationalChainBasis K n (strictOrderedFace K i v) := by
  apply Subtype.ext
  rw [rationalBoundary_coe, rationalChainBasis_coe, weakRationalBoundary_single]
  simp [strictOrderedFace]

theorem rationalBoundary_squared (K : Complex ι) (n : ℕ) :
    (rationalBoundary K n).comp (rationalBoundary K (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (weakRationalBoundary_squared K n) x.val

def rationalChainComplex (K : Complex ι) : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℚ (RationalChains K n))
    (fun n => ModuleCat.ofHom (rationalBoundary K n))
    (fun n => ModuleCat.hom_ext (rationalBoundary_squared K n))

theorem subsingleton_rationalChains_of_card_le (K : Complex ι) (n : ℕ)
    (hn : Fintype.card ι ≤ n) : Subsingleton (RationalChains K n) := by
  letI : IsEmpty {v : OrderedSimplex K n | StrictMono v.val} :=
    isEmpty_strictOrderedSimplex K n hn
  exact (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    {v : OrderedSimplex K n | StrictMono v.val}).injective.subsingleton

end BanachIsometric.FiniteNerve
