import Posets.OrdinalIdealTransportDiagonalFactorization
import Posets.OrdinalIdealTransportSingularModel
import Posets.OrdinalIdealTransportLowRank
import JLMS.OrdinalSpaceSingularReplication

/-! Primary factorisation for singular initial ordinal C-spaces. The proof
uses the genuine regular-block sum and its bounded scalar diagonalisation.
Finite powers are transported through the proved singular square equivalence. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem singularInitialOrdinal_hasUPFP {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (hs : ¬ c.IsRegular) : ThesisCommon.HasUPFP 𝕜 (OrdinalSpace 𝕜 c.ord) := by
  have h := regularOrdinalSum_hasUPFP (𝕜 := 𝕜)
    (Cardinal.isRegular_cof (Cardinal.isSuccLimit_ord hc)) (singularRegularCardinal c)
    (singularRegularCardinal_regular hc) (singularRegularCardinal_uncountable hc)
    (singularRegularCardinal_index_small hc) (singularRegularCardinal_strictMono hc)
  let e := CZeroSum.congrRightIsometry (fun i : Set.Iio c.ord.cof.ord =>
    ordinalSpaceCongrIsometry (𝕜 := 𝕜) (singularRegularCardinal_ord hc i))
  exact (h.of_equiv e.toContinuousLinearEquiv).of_equiv
    (ordinalSingularRegularSumEquiv (𝕜 := 𝕜) hc hs).symm

theorem proposition_3_1_singular {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (hs : ¬ c.IsRegular) : Proposition_3_1 𝕜 c.ord := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) c.ord) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (singularInitialOrdinal_hasUPFP (𝕜 := 𝕜) hc hs).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

theorem infiniteInitialOrdinal_hasUPFP {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c) :
    ThesisCommon.HasUPFP 𝕜 (OrdinalSpace 𝕜 c.ord) := by
  by_cases he : c = Cardinal.aleph0
  · subst c
    have h := ordinalOmega_hasUPFP (𝕜 := 𝕜)
    rw [Cardinal.ord_aleph0]
    exact h
  · by_cases hr : c.IsRegular
    · exact initialOrdinal_hasUPFP hr (lt_of_le_of_ne hc (Ne.symm he))
    · exact singularInitialOrdinal_hasUPFP hc hr

theorem proposition_3_1_infinite_initial {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c) :
    Proposition_3_1 𝕜 c.ord := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) c.ord) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (infiniteInitialOrdinal_hasUPFP (𝕜 := 𝕜) hc).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

theorem uniqueMaximalClosed_initial_finiteMultiple {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) :
    ThesisCommon.HasUniqueMaximalClosedIdeal 𝕜
      (OrdinalSpace 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal)) →L[𝕜]
        OrdinalSpace 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal))) := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  exact (uniqueMaximalClosed_ordinal_finiteMultiple_iff c.ord hκ n).mpr
    ((proposition_3_1_infinite_initial hc hκ).1)

def ordinalSingularFiniteMultipleEquiv {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (hs : ¬ c.IsRegular) (n : ℕ) :
    OrdinalSpace 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal)) ≃L[𝕜] OrdinalSpace 𝕜 c.ord := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  exact (ordinalSpaceFinitePower (𝕜 := 𝕜) c.ord hκ n).trans
    (finitePiCollapseEquiv (ordinalSpaceSingularInitialSquareEquiv (𝕜 := 𝕜) c hc hs) n)

theorem singularInitialFiniteMultiple_hasUPFP {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    ThesisCommon.HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal))) :=
  (singularInitialOrdinal_hasUPFP hc hs).of_equiv (ordinalSingularFiniteMultipleEquiv hc hs n).symm

theorem proposition_3_1_singular_finiteMultiple {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    Proposition_3_1 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal)) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) (c.ord * ((n+1 : ℕ) : Ordinal))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP
    (singularInitialFiniteMultiple_hasUPFP (𝕜 := 𝕜) hc hs n).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
