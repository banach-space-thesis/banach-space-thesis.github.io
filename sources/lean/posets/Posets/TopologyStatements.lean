import Posets.QuotientStatements
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Topology.Order.Compact

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon Filter Topology
open scoped ZeroAtInfty Cardinal
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

abbrev OrdinalSpace (α : Ordinal.{0}) := C(Set.Icc (0 : Ordinal.{0}) α, 𝕜)

/-- Proposition 3.1. C(α) is interpreted as C([0,α]); the source does not
explicitly specify endpoints, and this convention is recorded for review. -/
def Proposition_3_1 (α : Ordinal.{0}) : Prop :=
  Ordinal.omega0 ≤ α →
  HasUniqueMaximalClosedIdeal 𝕜 (OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α) ∧
  ((∀ c : Cardinal.{0}, ℵ₀ < c → c.IsRegular → ∀ n : ℕ, 2 ≤ n →
    ¬ Nonempty (OrdinalSpace 𝕜 α ≃L[𝕜] OrdinalSpace 𝕜 (c.ord * (n : Ordinal)))) →
      IsMaximalClosedIdeal 𝕜
        {T : OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α |
          DoesNotFactorIdentity 𝕜 T (OrdinalSpace 𝕜 α)})

def Proposition_3_4 : Prop :=
  Nonempty (Fin 4 ↪ NontrivialClosedIdeals 𝕜
    (OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal))) →L[𝕜]
     OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal))))) ∧
  MissingSeparableIdealCount 𝕜

/-- Lemma 4.5, including the topological sum and both isometric identifications. -/
def Lemma_4_5 (𝒜 : ℕ → Set (Set ℕ)) : Prop :=
  (∀ n, IsAlmostDisjoint (𝒜 n)) →
  ∃ ℬ : Set (Set ℕ), IsAlmostDisjoint ℬ ∧
    Nonempty (Mrowka ℬ ≃ₜ (Σ n : ℕ, Mrowka (𝒜 n))) ∧
    Nonempty (Space 𝕜 ℬ ≃ₗᵢ[𝕜] C₀((Σ n : ℕ, Mrowka (𝒜 n)), 𝕜)) ∧
    Nonempty (C₀((Σ n : ℕ, Mrowka (𝒜 n)), 𝕜) ≃ₗᵢ[𝕜]
      DependentCZeroSum 𝕜 (fun n => Space 𝕜 (𝒜 n)))

def collapse {K : Type*} (L : Set K) : OnePoint K → OnePoint L
  | none => none
  | some x => if h : x ∈ L then some ⟨x, h⟩ else none

/-- Lemma 4.6: continuity and surjectivity of the stated collapse map, and
the actual isometric extension-by-zero homomorphism on C₀. -/
def Lemma_4_6 (K : Type*) [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
    (L : Set K) : Prop :=
  IsOpen L → Continuous (collapse L) ∧ Function.Surjective (collapse L) ∧
  ∃ ι : BoundedHom 𝕜 C₀(L, 𝕜) C₀(K, 𝕜), Isometry ι ∧
    ∀ f x, ι f x = if h : x ∈ L then f ⟨x, h⟩ else 0

def Scattered (K : Type*) [TopologicalSpace K] : Prop :=
  ∀ s : Set K, s.Nonempty → ∃ x ∈ s, ∃ U : Set K, IsOpen U ∧ s ∩ U = {x}

/-- Isolated points are bundled with their open-singleton proof. -/
def Isolated (K : Type*) [TopologicalSpace K] := {x : K // IsOpen ({x} : Set K)}

def singletonFunction {K : Type*} [TopologicalSpace K] [T2Space K]
    (x : Isolated K) : C₀(K, 𝕜) where
  toFun := ({x.val} : Set K).indicator (fun _ => 1)
  continuous_toFun := continuous_indicator
    (by simp [show IsClopen ({x.val} : Set K) from ⟨isClosed_singleton, x.property⟩])
      continuous_const.continuousOn
  zero_at_infty' := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(isCompact_singleton (x := x.val)).compl_mem_cocompact] with k hk
    exact (Set.indicator_of_notMem hk _).symm

/-- Lemma 4.17. The coefficient is T(1_{x})(z), equal to the singleton mass
of T*δ_z. No dual representation is assumed as a field. -/
def Lemma_4_17 (K L : Type) [TopologicalSpace K] [TopologicalSpace L]
    [LocallyCompactSpace K] [LocallyCompactSpace L] [T2Space K] [T2Space L]
    [Infinite K] [Infinite L] (T : C₀(K, 𝕜) →L[𝕜] C₀(L, 𝕜)) : Prop :=
  Scattered K → Scattered L →
  ∃ E : Set K, E ⊆ derivedSet Set.univ ∧ Cardinal.mk E ≤ Cardinal.mk (Isolated L) ∧
    ∀ f : C₀(K, 𝕜), (∀ y ∈ E, f y = 0) → ∀ z : Isolated L,
      T f z.val = ∑' x : Isolated K, T (singletonFunction 𝕜 x) z.val * f x.val

end Posets
