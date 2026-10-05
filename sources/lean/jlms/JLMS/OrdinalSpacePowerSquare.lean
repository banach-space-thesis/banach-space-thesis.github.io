import JLMS.OrdinalSpacePowerLimit

/-!
# Higher initial-ordinal powers are isomorphic to their squares

Kislyakov Lemma 3.2 is assembled from its successor and limit cases.
For every infinite initial base κ, exponent γ≥2 with |γ|≤|κ|, the
endpoint-zero function space at κ^γ is isomorphic to κ copies of itself.
The ordinary continuous-function space is consequently isomorphic to
its square. No ordinal classification hypothesis is assumed.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance powerSquareFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance powerSquareFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance powerSquareEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerSquareEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

theorem nonempty_ordinalEndpointZeroPowerReplication (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (hcard : γ.card ≤ c) :
    Nonempty (ordinalEndpointZero 𝕜 (c.ord ^ γ) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ γ))) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨β, rfl⟩ | hlim
  · norm_num at hγ
  · have hβ : 1 ≤ β := Order.lt_succ_iff.mp ((by norm_num : (1 : Ordinal) < 2).trans_le hγ)
    exact ⟨ordinalEndpointZeroPowerSuccessorReplication (𝕜 := 𝕜) c hc β hβ⟩
  · exact ⟨ordinalEndpointZeroPowerLimitReplication (𝕜 := 𝕜) c hc γ hlim hcard⟩

/-- The square isomorphism required above the square of an initial ordinal. -/
def ordinalSpaceInitialPowerSquareEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (hcard : γ.card ≤ c) :
    OrdinalC 𝕜 (c.ord ^ γ) ≃L[𝕜]
      OrdinalC 𝕜 (c.ord ^ γ) × OrdinalC 𝕜 (c.ord ^ γ) := by
  letI := ordinalIioInfinite c.ord (by simpa using Cardinal.ord_le_ord.mpr hc)
  let f := ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) (c.ord ^ γ)
    (ordinalInitialPower_infinite c hc γ (one_le_two.trans hγ))
  let r := Classical.choice (nonempty_ordinalEndpointZeroPowerReplication (𝕜 := 𝕜) c hc γ hγ hcard)
  let e := f.trans r
  exact e.trans ((CZeroSum.infiniteSquareIsometry (𝕜 := 𝕜) (Set.Iio c.ord)
    (ordinalEndpointZero 𝕜 (c.ord ^ γ))).toContinuousLinearEquiv.trans (e.symm.prodCongr e.symm))

end JLMS
