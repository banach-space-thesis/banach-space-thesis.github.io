import JLMS.OrdinalEndpointColumnTail
import JLMS.AtomicMatrixEntry

/-!
# The bounded left-limit functional of Ogden's endpoint column

The endpoint column is constant on some final tail below κ. Its constant
value is unique, linear in T, and bounded by ‖T‖. This constructs the actual
bounded functional needed for the Loy--Willis jump, without assuming the
existence or continuity of a limit functional.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)

local instance endpointLimitOperatorGroup : NormedAddCommGroup
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance
local instance endpointLimitOperatorSpace : NormedSpace 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance

def initialEndpointColumnLimit (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) : 𝕜 :=
  Classical.choose (Classical.choose_spec
    (exists_constant_initialOrdinalEndpointColumn_tail hc hu T)).2

theorem exists_initialEndpointColumnLimit_tail
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    ∃ β < c.ord, ∀ x : OrdinalInterval c.ord, β < x.val → x.val < c.ord →
      ordinalOperatorMatrix c.ord T x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
        initialEndpointColumnLimit hc hu T := by
  let h := exists_constant_initialOrdinalEndpointColumn_tail hc hu T
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    Classical.choose_spec (Classical.choose_spec h).2⟩

theorem initialEndpointColumnLimit_eq_of_tail
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    {β : Ordinal.{u}} (hβ : β < c.ord) (a : 𝕜)
    (h : ∀ x : OrdinalInterval c.ord, β < x.val → x.val < c.ord →
      ordinalOperatorMatrix c.ord T x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = a) :
    initialEndpointColumnLimit hc hu T = a := by
  obtain ⟨γ, hγ, hg⟩ := exists_initialEndpointColumnLimit_tail hc hu T
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  have hlim := Ordinal.aleph0_le_cof.mp hcf.le
  have hξ : Order.succ (max β γ) < c.ord := hlim.succ_lt (max_lt hβ hγ)
  let x : OrdinalInterval c.ord := ⟨Order.succ (max β γ), Ordinal.zero_le _, hξ.le⟩
  have hxβ : β < x.val := (le_max_left β γ).trans_lt (Order.lt_succ _)
  have hxγ : γ < x.val := (le_max_right β γ).trans_lt (Order.lt_succ _)
  exact (hg x hxγ hξ).symm.trans (h x hxβ hξ)

theorem initialEndpointColumnLimit_add
    (S T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    initialEndpointColumnLimit hc hu (S + T) =
      initialEndpointColumnLimit hc hu S + initialEndpointColumnLimit hc hu T := by
  obtain ⟨β, hβ, hs⟩ := exists_initialEndpointColumnLimit_tail hc hu S
  obtain ⟨γ, hγ, ht⟩ := exists_initialEndpointColumnLimit_tail hc hu T
  apply initialEndpointColumnLimit_eq_of_tail hc hu (S + T) (max_lt hβ hγ)
  intro x hx hxα
  have he := (ordinalOperatorEntryCLM (𝕜 := 𝕜) c.ord x
    ⟨c.ord, Ordinal.zero_le _, le_rfl⟩).map_add S T
  change ordinalOperatorMatrix c.ord (S + T) x _ =
    ordinalOperatorMatrix c.ord S x _ + ordinalOperatorMatrix c.ord T x _ at he
  rw [he, hs x ((le_max_left β γ).trans_lt hx) hxα,
    ht x ((le_max_right β γ).trans_lt hx) hxα]

theorem initialEndpointColumnLimit_smul (a : 𝕜)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    initialEndpointColumnLimit hc hu (a • T) = a • initialEndpointColumnLimit hc hu T := by
  obtain ⟨β, hβ, ht⟩ := exists_initialEndpointColumnLimit_tail hc hu T
  apply initialEndpointColumnLimit_eq_of_tail hc hu (a • T) hβ
  intro x hx hxα
  have he := (ordinalOperatorEntryCLM (𝕜 := 𝕜) c.ord x
    ⟨c.ord, Ordinal.zero_le _, le_rfl⟩).map_smul a T
  change ordinalOperatorMatrix c.ord (a • T) x _ = a • ordinalOperatorMatrix c.ord T x _ at he
  rw [he, ht x hx hxα]

theorem norm_initialEndpointColumnLimit_le
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    ‖initialEndpointColumnLimit hc hu T‖ ≤ ‖T‖ := by
  obtain ⟨β, hβ, ht⟩ := exists_initialEndpointColumnLimit_tail hc hu T
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  have hξ : Order.succ β < c.ord := (Ordinal.aleph0_le_cof.mp hcf.le).succ_lt hβ
  let x : OrdinalInterval c.ord := ⟨Order.succ β, Ordinal.zero_le _, hξ.le⟩
  rw [← ht x (Order.lt_succ β) hξ]
  exact (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (ordinalOperatorRow c.ord T x) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩).trans
      (norm_ordinalOperatorRow_le c.ord T x)

def initialEndpointColumnLimitCLM :
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →L[𝕜] 𝕜 := by
  let L : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₗ[𝕜] 𝕜 :=
    { toFun := initialEndpointColumnLimit (𝕜 := 𝕜) hc hu
      map_add' := initialEndpointColumnLimit_add (𝕜 := 𝕜) hc hu
      map_smul' := initialEndpointColumnLimit_smul (𝕜 := 𝕜) hc hu }
  exact L.mkContinuous 1 (fun (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) => by
    change ‖initialEndpointColumnLimit (𝕜 := 𝕜) hc hu T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_initialEndpointColumnLimit_le (𝕜 := 𝕜) hc hu T)

@[simp] theorem initialEndpointColumnLimitCLM_apply
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    initialEndpointColumnLimitCLM (𝕜 := 𝕜) hc hu T = initialEndpointColumnLimit hc hu T := rfl

end JLMS
