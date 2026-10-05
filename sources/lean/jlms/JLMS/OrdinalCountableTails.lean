import JLMS.OrdinalTailConstancy
import Mathlib.Topology.Algebra.Module.Basic

/-!
# One ordinal tail for a countably generated closed function subspace

All members of a countable family become constant on one common tail when
the endpoint has uncountable cofinality. The tail condition defines a closed
vector subspace, so the same tail works for their closed linear span.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalTailSpace (α β : Ordinal.{u}) : Submodule 𝕜 (OrdinalC 𝕜 α) where
  carrier := {f | ∀ x : OrdinalInterval α, β < x.val → f x = f ⟨α, Ordinal.zero_le _, le_rfl⟩}
  zero_mem' := by intro x hx; rfl
  add_mem' := by intro f g hf hg x hx; simp only [ContinuousMap.add_apply, hf x hx, hg x hx]
  smul_mem' := by intro c f hf x hx; simp only [ContinuousMap.smul_apply, hf x hx]

theorem ordinalTailSpace_isClosed (α β : Ordinal.{u}) :
    IsClosed (ordinalTailSpace (𝕜 := 𝕜) α β : Set (OrdinalC 𝕜 α)) := by
  change IsClosed {f : OrdinalC 𝕜 α | ∀ x : OrdinalInterval α, β < x.val →
    f x = f ⟨α, Ordinal.zero_le _, le_rfl⟩}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _hx =>
    isClosed_eq (ContinuousMap.evalCLM (R := 𝕜) x).continuous
      (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜)
        (⟨α, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval α)).continuous

theorem exists_common_ordinal_tail {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (f : ℕ → OrdinalC 𝕜 α) :
    ∃ β < α, ∀ n, f n ∈ ordinalTailSpace α β := by
  have h (n) := exists_constant_ordinalC_tail hα (f n)
  choose b hb hf using h
  have hs : (⨆ n, b n) < α := Ordinal.iSup_lt_ord_lift (by simpa using hα) hb
  refine ⟨⨆ n, b n, hs, fun n x hx => ?_⟩
  exact hf n x ((Ordinal.le_iSup b n).trans_lt hx)

theorem exists_closedSpan_ordinal_tail {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (f : ℕ → OrdinalC 𝕜 α) :
    ∃ β < α, (Submodule.span 𝕜 (Set.range f)).topologicalClosure ≤ ordinalTailSpace α β := by
  obtain ⟨β, hβ, hh⟩ := exists_common_ordinal_tail hα f
  refine ⟨β, hβ, Submodule.topologicalClosure_minimal _ ?_ (ordinalTailSpace_isClosed α β)⟩
  apply Submodule.span_le.mpr
  rintro g ⟨n, rfl⟩
  exact hh n

end JLMS
