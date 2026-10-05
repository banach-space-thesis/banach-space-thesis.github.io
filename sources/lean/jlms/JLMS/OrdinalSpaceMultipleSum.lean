import JLMS.OrdinalSpaceBlocksDecomposition
import JLMS.OrdinalSpaceMultiples
import JLMS.OrdinalSpaceEndpointAbsorption
import JLMS.OrdinalSpaceSumAbsorptionBounded
import JLMS.CZeroSumOperators

/-!
# Constant c₀ sums in ordinal multiples

This is the sufficient direction of Kislyakov's Corollary 3.1. The
sequence ξ ↦ κξ has constant block length κ. The base summand is absorbed
when γ=κ or γ+κ=κ. The construction works for every infinite γ; no limit
assumption is needed. We record uniform bounds eight in each direction.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance multipleSumFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance multipleSumFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance multipleSumEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance multipleSumEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def ordinalEndpointZeroCongrIsometry {α β : Ordinal.{u}} (h : α = β) :
    ordinalEndpointZero 𝕜 α ≃ₗᵢ[𝕜] ordinalEndpointZero 𝕜 β := by
  subst β
  exact LinearIsometryEquiv.refl 𝕜 _

theorem ordinalIioInfinite (γ : Ordinal.{u}) (hγ : Ordinal.omega0 ≤ γ) :
    Infinite (Set.Iio γ) := by
  apply Infinite.of_injective
    (fun n : ℕ => (⟨(n : Ordinal), (Ordinal.nat_lt_omega0 n).trans_le hγ⟩ : Set.Iio γ))
  intro m n h
  have h' : (m : Ordinal.{u}) = (n : Ordinal.{u}) :=
    congrArg (fun x : Set.Iio γ => x.val) h
  exact_mod_cast h'

theorem ordinalMultipleMap_blockLength (κ γ : Ordinal.{u}) (hκ : 0 < κ)
    (ξ : Set.Iio γ) : ordinalSpaceBlockLength (ordinalMultipleMap κ γ hκ) ξ = κ :=
  ordinalMultipleMap_successor_gap κ γ hκ ξ.val ξ.prop

def ordinalMultipleBlockSumIsometry (κ γ : Ordinal.{u}) (hκ : Ordinal.omega0 ≤ κ) :
    CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜
      (ordinalSpaceBlockLength (ordinalMultipleMap κ γ (Ordinal.omega0_pos.trans_le hκ)) ξ))
      ≃ₗᵢ[𝕜] CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ) :=
  CZeroSum.congrRightIsometry (fun ξ => ordinalEndpointZeroCongrIsometry
    (ordinalMultipleMap_blockLength κ γ (Ordinal.omega0_pos.trans_le hκ) ξ))

def ordinalEndpointZeroMultipleBlocksEquiv (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) :
    ordinalEndpointZero 𝕜 (κ * γ) ≃L[𝕜]
      ordinalEndpointZero 𝕜 γ × CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ) :=
  (ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜) (ordinalMultipleMap κ γ (Ordinal.omega0_pos.trans_le hκ))
    (ordinalMultipleMap_strictMono κ γ _) (ordinalMultipleMap_zero κ γ _)
    (ordinalMultipleMap_endpoint κ γ _)
    (fun ξ => by rw [ordinalMultipleMap_blockLength]; exact hκ)).trans
      ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr
        (ordinalMultipleBlockSumIsometry (𝕜 := 𝕜) κ γ hκ).toContinuousLinearEquiv)

theorem norm_ordinalEndpointZeroMultipleBlocksEquiv_le (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (f : ordinalEndpointZero 𝕜 (κ * γ)) :
    ‖ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜) κ γ hκ f‖ ≤ 2 * ‖f‖ := by
  let e := ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (ordinalMultipleMap κ γ (Ordinal.omega0_pos.trans_le hκ))
    (ordinalMultipleMap_strictMono κ γ _) (ordinalMultipleMap_zero κ γ _)
    (ordinalMultipleMap_endpoint κ γ _)
    (fun ξ => by rw [ordinalMultipleMap_blockLength]; exact hκ)
  change max ‖(e f).1‖ ‖ordinalMultipleBlockSumIsometry (𝕜 := 𝕜) κ γ hκ (e f).2‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_ordinalEndpointZeroBlocksEquiv_apply_le _ _ _ _ _ f

theorem norm_ordinalEndpointZeroMultipleBlocksEquiv_symm_le (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ)
    (f : ordinalEndpointZero 𝕜 γ × CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ)) :
    ‖(ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜) κ γ hκ).symm f‖ ≤ 2 * ‖f‖ := by
  let e := ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (ordinalMultipleMap κ γ (Ordinal.omega0_pos.trans_le hκ))
    (ordinalMultipleMap_strictMono κ γ _) (ordinalMultipleMap_zero κ γ _)
    (ordinalMultipleMap_endpoint κ γ _)
    (fun ξ => by rw [ordinalMultipleMap_blockLength]; exact hκ)
  let d := ordinalMultipleBlockSumIsometry (𝕜 := 𝕜) κ γ hκ
  change ‖e.symm (f.1, d.symm f.2)‖ ≤ _
  calc
    _ ≤ 2 * ‖(f.1, d.symm f.2)‖ := norm_ordinalEndpointZeroBlocksEquiv_symm_apply_le _ _ _ _ _ _
    _ = 2 * ‖f‖ := by simp only [Prod.norm_def, d.symm.norm_map]

def ordinalEndpointZeroMultipleBaseAbsorption (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ) (habs : γ = κ ∨ γ + κ = κ) :
    (ordinalEndpointZero 𝕜 γ × CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ))
      ≃L[𝕜] CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ) := by
  letI := ordinalIioInfinite γ hγ
  by_cases heq : γ = κ
  · subst γ
    exact (cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) (Set.Iio κ) (ordinalEndpointZero 𝕜 κ)).symm.toContinuousLinearEquiv
  · exact ordinalEndpointZeroSumAbsorbLeft (Set.Iio γ) γ κ hγ hκ (habs.resolve_left heq)

theorem norm_ordinalEndpointZeroMultipleBaseAbsorption_le (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ) (habs : γ = κ ∨ γ + κ = κ)
    (f : ordinalEndpointZero 𝕜 γ × CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ)) :
    ‖ordinalEndpointZeroMultipleBaseAbsorption (𝕜 := 𝕜) κ γ hκ hγ habs f‖ ≤ 4 * ‖f‖ := by
  letI := ordinalIioInfinite γ hγ
  unfold ordinalEndpointZeroMultipleBaseAbsorption
  split_ifs with heq
  · subst γ
    change ‖(cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) (Set.Iio κ)
      (ordinalEndpointZero 𝕜 κ)).symm f‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  · exact norm_cZeroSumAbsorbs_le (𝕜 := 𝕜) (Set.Iio γ)
      (ordinalEndpointZeroAbsorbLeft (𝕜 := 𝕜) γ κ hγ hκ (habs.resolve_left heq))
      (by norm_num) (norm_ordinalEndpointZeroAbsorbLeft_le (𝕜 := 𝕜) γ κ hγ hκ _) f

theorem norm_ordinalEndpointZeroMultipleBaseAbsorption_symm_le (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ) (habs : γ = κ ∨ γ + κ = κ)
    (f : CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ)) :
    ‖(ordinalEndpointZeroMultipleBaseAbsorption (𝕜 := 𝕜) κ γ hκ hγ habs).symm f‖ ≤ 4 * ‖f‖ := by
  letI := ordinalIioInfinite γ hγ
  unfold ordinalEndpointZeroMultipleBaseAbsorption
  split_ifs with heq
  · subst γ
    change ‖cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) (Set.Iio κ)
      (ordinalEndpointZero 𝕜 κ) f‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  · exact norm_cZeroSumAbsorbs_symm_le (𝕜 := 𝕜) (Set.Iio γ)
      (ordinalEndpointZeroAbsorbLeft (𝕜 := 𝕜) γ κ hγ hκ (habs.resolve_left heq))
      (by norm_num) (norm_ordinalEndpointZeroAbsorbLeft_symm_le (𝕜 := 𝕜) γ κ hγ hκ _) f

/-- Kislyakov Corollary 3.1, with the constant block sum made explicit. -/
def ordinalEndpointZeroMultipleSumEquiv (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ) (habs : γ = κ ∨ γ + κ = κ) :
    ordinalEndpointZero 𝕜 (κ * γ) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ) :=
  (ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜) κ γ hκ).trans
    (ordinalEndpointZeroMultipleBaseAbsorption (𝕜 := 𝕜) κ γ hκ hγ habs)

theorem norm_ordinalEndpointZeroMultipleSumEquiv_le (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ) (habs : γ = κ ∨ γ + κ = κ)
    (f : ordinalEndpointZero 𝕜 (κ * γ)) :
    ‖ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) κ γ hκ hγ habs f‖ ≤ 8 * ‖f‖ := by
  have h₁ := norm_ordinalEndpointZeroMultipleBlocksEquiv_le κ γ hκ f
  have h₂ := norm_ordinalEndpointZeroMultipleBaseAbsorption_le κ γ hκ hγ habs
    (ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜) κ γ hκ f)
  change ‖ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) κ γ hκ hγ habs f‖ ≤
    4 * ‖ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜) κ γ hκ f‖ at h₂
  linarith

theorem norm_ordinalEndpointZeroMultipleSumEquiv_symm_le (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ) (habs : γ = κ ∨ γ + κ = κ)
    (f : CZeroSum 𝕜 (fun _ : Set.Iio γ => ordinalEndpointZero 𝕜 κ)) :
    ‖(ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) κ γ hκ hγ habs).symm f‖ ≤ 8 * ‖f‖ := by
  have h₁ := norm_ordinalEndpointZeroMultipleBaseAbsorption_symm_le κ γ hκ hγ habs f
  have h₂ := norm_ordinalEndpointZeroMultipleBlocksEquiv_symm_le κ γ hκ
    ((ordinalEndpointZeroMultipleBaseAbsorption (𝕜 := 𝕜) κ γ hκ hγ habs).symm f)
  change ‖(ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) κ γ hκ hγ habs).symm f‖ ≤
    2 * ‖(ordinalEndpointZeroMultipleBaseAbsorption (𝕜 := 𝕜) κ γ hκ hγ habs).symm f‖ at h₂
  linarith

end JLMS
