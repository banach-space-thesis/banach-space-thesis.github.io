import ThesisCommon.Analysis.BooleanPartialIsometry
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Countable

noncomputable section
open Set Cardinal
namespace ThesisCommon.BooleanPartialIsometry
universe u
variable {A B : Type u} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B]

theorem cardinal_graph_eq_source (p : BooleanPartialIsometry A B) : #p.graph = #p.source := by
  let f : p.graph → p.source := fun z => ⟨z.val.1, z.val.2, z.property⟩
  apply Cardinal.mk_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro z w h
    apply Subtype.ext
    have hx : z.val.1 = w.val.1 := congrArg Subtype.val h
    apply Prod.ext hx
    apply p.right_unique z.property
    simpa only [hx] using w.property
  · intro a
    obtain ⟨b, hb⟩ := a.property
    exact ⟨⟨(a.val,b), hb⟩, rfl⟩

theorem cardinal_target_eq_source (p : BooleanPartialIsometry A B) : #p.target = #p.source :=
  Cardinal.mk_congr p.orderIso.symm.toEquiv

theorem source_chainUnion (c : Set (BooleanPartialIsometry A B)) (hc : c.Nonempty)
    (hchain : IsChain (· ≤ ·) c) :
    ((chainUnion c hc hchain).source : Set A) = ⋃ p : c, (p.val.source : Set A) := by
  ext a
  constructor
  · rintro ⟨b, p, hp, hab⟩
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, b, hab⟩
  · intro ha
    obtain ⟨p, b, hab⟩ := mem_iUnion.mp ha
    exact ⟨b, p.val, p.property, hab⟩

theorem source_chainUnion_finite (c : Set (BooleanPartialIsometry A B)) (hc : c.Nonempty)
    (hchain : IsChain (· ≤ ·) c) (hcf : c.Finite)
    (hp : ∀ p ∈ c, (p.source : Set A).Finite) :
    ((chainUnion c hc hchain).source : Set A).Finite := by
  rw [source_chainUnion]
  letI := hcf.fintype
  exact Set.finite_iUnion fun p => hp p.val p.property

theorem cardinal_source_chainUnion_le (c : Set (BooleanPartialIsometry A B)) (hc : c.Nonempty)
    (hchain : IsChain (· ≤ ·) c) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hcκ : #c ≤ κ) (hp : ∀ p ∈ c, #p.source ≤ κ) :
    #(chainUnion c hc hchain).source ≤ κ := by
  change #((chainUnion c hc hchain).source : Set A) ≤ κ
  rw [source_chainUnion]
  calc
    #(⋃ p : c, (p.val.source : Set A)) ≤ #c * ⨆ p : c, #p.val.source := Cardinal.mk_iUnion_le _
    _ ≤ κ * κ := mul_le_mul' hcκ (ciSup_le' fun p => hp p.val p.property)
    _ = κ := Cardinal.mul_eq_self hκ

end ThesisCommon.BooleanPartialIsometry
