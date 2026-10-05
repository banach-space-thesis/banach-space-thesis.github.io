import JLMS.OrdinalSpaceMultipleSum
import JLMS.OrdinalSpaceAbsorption
import JLMS.OrdinalSpaceReduction

/-!
# Infinite quotients below the square of an initial ordinal

For κω≤α≤κ², ordinal division and absorption of the remainder identify
C[0,α] with the infinite constant c₀ sum indexed by [0,α/κ). Such a sum
is isometric to its square. This proves the sufficient infinite-quotient
branch of Kislyakov's Lemma 3.4 without a classification hypothesis.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance initialInfiniteFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance initialInfiniteFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance initialInfiniteEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance initialInfiniteEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

theorem initialInfiniteQuotient_omega_le (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α : Ordinal.{u}) (hlo : c.ord * Ordinal.omega0 ≤ α) :
    Ordinal.omega0 ≤ α / c.ord := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le
    (by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc)
  exact (Ordinal.le_div hκ.ne').mpr hlo

def ordinalSpaceInitialInfiniteSumEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α : Ordinal.{u}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalC 𝕜 α ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio (α / c.ord) => ordinalEndpointZero 𝕜 c.ord) := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hκpos : 0 < c.ord := Ordinal.omega0_pos.trans_le hκ
  have hη := initialInfiniteQuotient_omega_le c hc α hlo
  have hηκ : α / c.ord ≤ c.ord := Ordinal.div_le_of_le_mul hhi
  have habs : α / c.ord = c.ord ∨ α / c.ord + c.ord = c.ord := by
    rcases hηκ.eq_or_lt with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (small_add_eq_of_initial_le c hc c.ord (α / c.ord) le_rfl hlt)
  have hmul : c.ord ≤ c.ord * (α / c.ord) :=
    Ordinal.le_mul_left _ (Ordinal.omega0_pos.trans_le hη)
  exact (ordinalSpaceCongrIsometry (𝕜 := 𝕜) (Ordinal.div_add_mod α c.ord).symm).toContinuousLinearEquiv.trans
    ((ordinalSpaceSmallRemainder c hc _ _ hmul (Ordinal.mod_lt _ hκpos.ne')).trans
      ((ordinalSpaceEndpointZeroBoundedEquiv _ (hκ.trans hmul)).trans
        (ordinalEndpointZeroMultipleSumEquiv c.ord (α / c.ord) hκ hη habs)))

def ordinalSpaceInitialInfiniteSquareEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α : Ordinal.{u}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 α × OrdinalC 𝕜 α := by
  letI := ordinalIioInfinite (α / c.ord) (initialInfiniteQuotient_omega_le c hc α hlo)
  let e := ordinalSpaceInitialInfiniteSumEquiv (𝕜 := 𝕜) c hc α hlo hhi
  exact e.trans ((CZeroSum.infiniteSquareIsometry (𝕜 := 𝕜) (Set.Iio (α / c.ord))
    (ordinalEndpointZero 𝕜 c.ord)).toContinuousLinearEquiv.trans (e.symm.prodCongr e.symm))

theorem ordinalSpaceReduction_of_initial_infiniteQuotient
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α : Ordinal.{u}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalSpaceReduction 𝕜 α := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hα : Ordinal.omega0 ≤ α := hκ.trans
    ((Ordinal.le_mul_left c.ord Ordinal.omega0_pos).trans hlo)
  refine Or.inr (Or.inl ⟨hα, ⟨?_⟩⟩)
  exact (ordinalSpaceInitialInfiniteSquareEquiv (𝕜 := 𝕜) c hc α hlo hhi).trans
    (ordinalSpaceDoubleIsometry (𝕜 := 𝕜) α hα).symm.toContinuousLinearEquiv

end JLMS
