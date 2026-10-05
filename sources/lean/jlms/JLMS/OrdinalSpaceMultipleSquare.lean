import JLMS.OrdinalSpaceFiniteSquare
import JLMS.OrdinalSpaceMultipleSum
import JLMS.OrdinalSpacePowerReduction

/-!
# Square equivalences for the power normal form

A positive multiple of a square-isomorphic space remains square-isomorphic
when the multiplier is finite. An infinite multiplier is handled by the
constant c₀-sum decomposition. Together these cover the positive multiplier
below κ in the ordinal power normal form κ^γ η.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance multipleSquareFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance multipleSquareFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance multipleSquareEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance multipleSquareEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

theorem exists_nat_succ_of_positive_finite_ordinal {η : Ordinal.{u}}
    (hη : 0 < η) (hfinite : η < Ordinal.omega0) : ∃ n : ℕ, η = ((n + 1 : ℕ) : Ordinal) := by
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hfinite
  have hmpos : 0 < m := by rw [hm] at hη; exact_mod_cast hη
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  exact ⟨n, by simpa only [hn, Nat.succ_eq_add_one] using hm⟩

def ordinalSpaceInfiniteMultipleSquareEquiv (β η : Ordinal.{u})
    (hβ : Ordinal.omega0 ≤ β) (hη : Ordinal.omega0 ≤ η)
    (habs : η = β ∨ η + β = β) :
    OrdinalC 𝕜 (β * η) ≃L[𝕜] OrdinalC 𝕜 (β * η) × OrdinalC 𝕜 (β * η) := by
  have hβη : Ordinal.omega0 ≤ β * η :=
    hβ.trans (Ordinal.le_mul_left β (Ordinal.omega0_pos.trans_le hη))
  letI := ordinalIioInfinite η hη
  let e := (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) (β * η) hβη).trans
    (ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) β η hβ hη habs)
  exact e.trans ((CZeroSum.infiniteSquareIsometry (𝕜 := 𝕜) (Set.Iio η)
    (ordinalEndpointZero 𝕜 β)).toContinuousLinearEquiv.trans (e.symm.prodCongr e.symm))

def ordinalSpaceMultipleSquareEquiv (β η : Ordinal.{u})
    (hβ : Ordinal.omega0 ≤ β) (hη : 0 < η) (habs : η = β ∨ η + β = β)
    (e : OrdinalC 𝕜 β ≃L[𝕜] OrdinalC 𝕜 β × OrdinalC 𝕜 β) :
    OrdinalC 𝕜 (β * η) ≃L[𝕜] OrdinalC 𝕜 (β * η) × OrdinalC 𝕜 (β * η) := by
  by_cases hinf : Ordinal.omega0 ≤ η
  · exact ordinalSpaceInfiniteMultipleSquareEquiv β η hβ hinf habs
  · have hex := exists_nat_succ_of_positive_finite_ordinal hη (lt_of_not_ge hinf)
    let n := Classical.choose hex
    have hn : η = ((n + 1 : ℕ) : Ordinal) := Classical.choose_spec hex
    let d := (ordinalSpaceCongrIsometry (𝕜 := 𝕜) (congrArg (β * ·) hn)).toContinuousLinearEquiv
    exact d.trans ((ordinalSpaceFiniteMultipleSquareEquiv β hβ n e).trans
      (d.symm.prodCongr d.symm))

def ordinalSpacePowerMultipleSquareEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ η : Ordinal.{u}) (hγ : 1 ≤ γ) (hη : 0 < η) (hηκ : η < c.ord)
    (e : OrdinalC 𝕜 (c.ord ^ γ) ≃L[𝕜]
      OrdinalC 𝕜 (c.ord ^ γ) × OrdinalC 𝕜 (c.ord ^ γ)) :
    OrdinalC 𝕜 (c.ord ^ γ * η) ≃L[𝕜]
      OrdinalC 𝕜 (c.ord ^ γ * η) × OrdinalC 𝕜 (c.ord ^ γ * η) := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hpow : c.ord ≤ c.ord ^ γ := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right (Ordinal.omega0_pos.trans_le hκ) hγ
  exact ordinalSpaceMultipleSquareEquiv _ _ (hκ.trans hpow) hη
    (Or.inr (small_add_eq_of_initial_le c hc _ η hpow hηκ)) e

theorem ordinalSpaceReduction_above_initial_square_of_powerSquares
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) (α : Ordinal.{u})
    (hcard : α.card ≤ c) (hα : c.ord ^ (2 : Ordinal) ≤ α)
    (hpower : ∀ γ : Ordinal.{u}, 2 ≤ γ → γ.card ≤ c → Nonempty
      (OrdinalC 𝕜 (c.ord ^ γ) ≃L[𝕜] OrdinalC 𝕜 (c.ord ^ γ) × OrdinalC 𝕜 (c.ord ^ γ))) :
    OrdinalSpaceReduction 𝕜 α := by
  obtain ⟨γ, hγ, hγcard, η, hη, hηκ, ⟨d⟩⟩ :=
    exists_ordinalSpace_power_normalForm_cardBound (𝕜 := 𝕜) c hc α hcard hα
  obtain ⟨e⟩ := hpower γ hγ hγcard
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hpow : c.ord ≤ c.ord ^ (2 : Ordinal) := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right (Ordinal.omega0_pos.trans_le hκ) (one_le_two : (1 : Ordinal) ≤ 2)
  have hinf : Ordinal.omega0 ≤ α := hκ.trans (hpow.trans hα)
  refine Or.inr (Or.inl ⟨hinf, ⟨?_⟩⟩)
  exact d.trans ((ordinalSpacePowerMultipleSquareEquiv c hc γ η (one_le_two.trans hγ) hη hηκ e).trans
    ((d.symm.prodCongr d.symm).trans (ordinalSpaceDoubleIsometry (𝕜 := 𝕜) α hinf).symm.toContinuousLinearEquiv))

end JLMS
