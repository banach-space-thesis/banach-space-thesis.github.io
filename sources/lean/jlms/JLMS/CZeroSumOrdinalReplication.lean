import JLMS.CZeroSumAdjacentAbsorption
import JLMS.OrdinalOmegaBlocks

/-!
# Replication from absorption at ordinal successors

Every limit ordinal is a union of consecutive blocks of order type ω.
Reindexing by these blocks converts successor absorption into the
natural-number adjacent-absorption theorem. This is the general Banach
space assembly step in Kislyakov Lemma 3.3.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open Set Ordinal Order
open scoped Ordinal
namespace JLMS
universe u u' v w
variable {𝕜 : Type w} [RCLike 𝕜]

local instance ordinalReplicationSumGroup {J : Type*} (F : J → Type*)
    [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)] :
    NormedAddCommGroup (CZeroSum 𝕜 F) := inferInstance
local instance ordinalReplicationSumSpace {J : Type*} (F : J → Type*)
    [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 F) := inferInstance

/-- Uniform absorption at consecutive ordinal coordinates gives replication
of the entire c₀ sum. -/
theorem nonempty_cZeroSum_ordinalReplication (γ : Ordinal.{u}) (hγ : IsSuccLimit γ)
    (I : Type u') [Infinite I] (E : Iio γ → Type v)
    [∀ a, NormedAddCommGroup (E a)] [∀ a, NormedSpace 𝕜 (E a)]
    {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ a : Iio γ, ∃ e : E ⟨succ a.val, hγ.succ_lt a.property⟩ ≃L[𝕜]
        CZeroSum 𝕜 (fun _ : I => E a) × E ⟨succ a.val, hγ.succ_lt a.property⟩,
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    Nonempty (CZeroSum 𝕜 E ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => CZeroSum 𝕜 E)) := by
  obtain ⟨_hγ0, η, rfl⟩ := Ordinal.isSuccLimit_iff_omega0_dvd.1 hγ
  let e := ordinalOmegaBlockEquiv η
  let W : Iio η → ℕ → Type v := fun b n => E (e (b, n))
  have hW : ∀ b n, ∃ f : W b (n + 1) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : I => W b n) × W b (n + 1),
      ‖f.toContinuousLinearMap‖ * ‖f.symm.toContinuousLinearMap‖ ≤ K := by
    intro b n
    have hs : (⟨succ (e (b, n)).val, hγ.succ_lt (e (b, n)).property⟩ : Iio (ω * η)) =
        e (b, n + 1) := Subtype.ext (ordinalOmegaBlockEquiv_succ η b n).symm
    dsimp only [W]
    rw [← hs]
    exact he (e (b, n))
  obtain ⟨f⟩ := nonempty_cZeroSum_adjacentReplication (𝕜 := 𝕜) I W hK hW
  let r : CZeroSum 𝕜 E ≃ₗᵢ[𝕜] CZeroSum 𝕜 (fun b => CZeroSum 𝕜 (W b)) :=
    (CZeroSum.reindex (𝕜 := 𝕜) (E := E) e).trans
      (CZeroSum.prodIsometry (𝕜 := 𝕜) (E := W)).symm
  exact ⟨r.toContinuousLinearEquiv.trans (f.trans
    (CZeroSum.congrRightIsometry (fun _ : I => r.symm)).toContinuousLinearEquiv)⟩

/-- The same hypotheses also identify the ordinal-indexed c₀ sum with its square. -/
theorem nonempty_cZeroSum_ordinalSquare (γ : Ordinal.{u}) (hγ : IsSuccLimit γ)
    (I : Type u') [Infinite I] (E : Iio γ → Type v)
    [∀ a, NormedAddCommGroup (E a)] [∀ a, NormedSpace 𝕜 (E a)]
    {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ a : Iio γ, ∃ e : E ⟨succ a.val, hγ.succ_lt a.property⟩ ≃L[𝕜]
        CZeroSum 𝕜 (fun _ : I => E a) × E ⟨succ a.val, hγ.succ_lt a.property⟩,
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    Nonempty (CZeroSum 𝕜 E ≃L[𝕜] CZeroSum 𝕜 E × CZeroSum 𝕜 E) := by
  obtain ⟨e⟩ := nonempty_cZeroSum_ordinalReplication γ hγ I E hK he
  exact ⟨e.trans ((CZeroSum.infiniteSquareIsometry (𝕜 := 𝕜) I
    (CZeroSum 𝕜 E)).toContinuousLinearEquiv.trans (e.symm.prodCongr e.symm))⟩

end JLMS
