import ThesisCommon.Analysis.ContinuousMapPullback
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.DerivedSet
import Mathlib.Logic.Denumerable

/-! The first infinite case of the countable compact-space classification.
A countably infinite compact Hausdorff space with exactly one possible
nonisolated point is homeomorphic to [0,ω]. In particular this applies when
its first Cantor--Bendixson derivative is a singleton. No classification
theorem or assumed Banach-space isomorphism is used. -/

noncomputable section
open Filter Topology Set
universe u
namespace ThesisCommon

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem isOpen_singleton_of_not_mem_derivedSet_univ (x : K)
    (hx : x ∉ derivedSet (Set.univ : Set K)) : IsOpen ({x} : Set K) := by
  rw [isOpen_singleton_iff_punctured_nhds]
  simpa only [mem_derivedSet, AccPt, Filter.principal_univ, inf_top_eq, not_neBot] using hx

/-- Removing the unique possible nonisolated point leaves a discrete space. -/
def countableCompactComplementDiscrete (p : K)
    (hp : ∀ x, x ≠ p → IsOpen ({x} : Set K)) :
    DiscreteTopology ({p}ᶜ : Set K) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have hx : IsOpen ({x.val} : Set K) := hp x.val x.property
  have hs : Subtype.val ⁻¹' ({x.val} : Set K) = ({x} : Set ({p}ᶜ : Set K)) := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
  rw [← hs]
  exact hx.preimage continuous_subtype_val

/-- A countably infinite compact space with only one possible accumulation
point is the one-point compactification of the natural numbers. -/
def countableCompactOnePointHomeomorph [Countable K] [Infinite K] (p : K)
    (hp : ∀ x, x ≠ p → IsOpen ({x} : Set K)) : K ≃ₜ OnePoint ℕ := by
  let S : Set K := {p}ᶜ
  letI : DiscreteTopology S := countableCompactComplementDiscrete p hp
  letI : Infinite S := (Set.finite_singleton p).infinite_compl.to_subtype
  let en : ℕ ≃ S := Classical.choice inferInstance
  let hn : ℕ ≃ₜ S :=
    { toEquiv := en
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let j : ℕ → K := fun n => (hn n).val
  have hj : Topology.IsEmbedding j := Topology.IsEmbedding.subtypeVal.comp hn.isEmbedding
  have hrange : Set.range j = {p}ᶜ := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact (hn n).property
    · intro hx
      obtain ⟨n, hn⟩ := hn.surjective ⟨x, hx⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  exact (OnePoint.equivOfIsEmbeddingOfRangeEq p j hj hrange).symm

def countableCompactOmegaNatPoint (n : ℕ) : OrdinalInterval (Ordinal.omega0 : Ordinal.{u}) :=
  ⟨n, bot_le, (Ordinal.nat_lt_omega0 n).le⟩

def countableCompactOmegaEndpoint : OrdinalInterval (Ordinal.omega0 : Ordinal.{u}) :=
  ⟨Ordinal.omega0, bot_le, le_rfl⟩

theorem countableCompactOmegaNatPoint_tendsto :
    Tendsto countableCompactOmegaNatPoint.{u} atTop (𝓝 countableCompactOmegaEndpoint) := by
  apply tendsto_subtype_rng.2
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 ha
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    change (k : Ordinal) < (n : Ordinal)
    exact_mod_cast (Nat.lt_of_succ_le hn)
  · intro a ha
    exact Eventually.of_forall fun n => (Ordinal.nat_lt_omega0 n).trans ha

def countableCompactOmegaOnePointMap : OnePoint ℕ → OrdinalInterval (Ordinal.omega0 : Ordinal.{u}) :=
  OnePoint.rec countableCompactOmegaEndpoint countableCompactOmegaNatPoint

theorem countableCompactOmegaOnePointMap_bijective :
    Function.Bijective countableCompactOmegaOnePointMap.{u} := by
  constructor
  · intro x y h
    induction x using OnePoint.rec with
    | infty =>
      induction y using OnePoint.rec with
      | infty => rfl
      | coe n =>
        have hval : (Ordinal.omega0 : Ordinal.{u}) = n := congrArg Subtype.val h
        exact ((Ordinal.nat_lt_omega0 n).ne hval.symm).elim
    | coe n =>
      induction y using OnePoint.rec with
      | infty =>
        have hval : (n : Ordinal.{u}) = Ordinal.omega0 := congrArg Subtype.val h
        exact ((Ordinal.nat_lt_omega0 n).ne hval).elim
      | coe m =>
        congr 1
        have hval : (n : Ordinal.{u}) = m := congrArg Subtype.val h
        exact_mod_cast hval
  · intro a
    obtain ha | ha := lt_or_eq_of_le a.property.2
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 ha
      exact ⟨(n : OnePoint ℕ), Subtype.ext hn.symm⟩
    · exact ⟨OnePoint.infty, Subtype.ext ha.symm⟩

def countableCompactOmegaOnePointHomeomorph :
    OnePoint ℕ ≃ₜ OrdinalInterval (Ordinal.omega0 : Ordinal.{u}) :=
  (show Continuous (Equiv.ofBijective _ countableCompactOmegaOnePointMap_bijective.{u}) from
    (OnePoint.continuous_iff_from_nat _).2 countableCompactOmegaNatPoint_tendsto).homeoOfEquivCompactToT2

/-- The first infinite ordinal model of a countably infinite compact space. -/
def countableCompactOmegaHomeomorph [Countable K] [Infinite K] (p : K)
    (hp : ∀ x, x ≠ p → IsOpen ({x} : Set K)) :
    K ≃ₜ OrdinalInterval (Ordinal.omega0 : Ordinal.{u}) :=
  (countableCompactOnePointHomeomorph p hp).trans countableCompactOmegaOnePointHomeomorph

def countableCompactOmegaContinuousEquiv {𝕜 : Type*} [RCLike 𝕜]
    [Countable K] [Infinite K] (p : K)
    (hp : ∀ x, x ≠ p → IsOpen ({x} : Set K)) :
    C(K, 𝕜) ≃L[𝕜] OrdinalContinuous 𝕜 (Ordinal.omega0 : Ordinal.{u}) :=
  continuousMapHomeomorphEquiv (countableCompactOmegaHomeomorph p hp)

/-- A singleton first derived set suffices for the concrete ordinal model. -/
def countableCompactOmegaHomeomorphOfDerivedSingleton [Countable K] [Infinite K] (p : K)
    (hp : derivedSet (Set.univ : Set K) = {p}) :
    K ≃ₜ OrdinalInterval (Ordinal.omega0 : Ordinal.{u}) :=
  countableCompactOmegaHomeomorph p fun x hx =>
    isOpen_singleton_of_not_mem_derivedSet_univ x (by simpa [hp] using hx)

end ThesisCommon
