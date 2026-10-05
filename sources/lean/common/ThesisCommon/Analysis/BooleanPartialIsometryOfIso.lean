import ThesisCommon.Analysis.BooleanPartialIsometry

noncomputable section
open Set
namespace ThesisCommon.BooleanPartialIsometry
variable {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B]

def ofOrderIso (S : BooleanSubalgebra A) (T : BooleanSubalgebra B)
    (e : S ≃o T) (he : Isometry e) : BooleanPartialIsometry A B where
  graph :=
    { carrier := range (fun a : S => (a.val, (e a).val))
      bot_mem' := ⟨⊥, by simp only [map_bot, BooleanSubalgebra.val_bot]; rfl⟩
      compl_mem' := by
        rintro z ⟨a,rfl⟩
        exact ⟨aᶜ, by simp only [map_compl', BooleanSubalgebra.val_compl]; rfl⟩
      infClosed' := by
        rintro z ⟨a,rfl⟩ w ⟨b,rfl⟩
        exact ⟨a ⊓ b, by simp⟩
      supClosed' := by
        rintro z ⟨a,rfl⟩ w ⟨b,rfl⟩
        exact ⟨a ⊔ b, by simp⟩ }
  dist_eq := by
    rintro z ⟨a,rfl⟩ w ⟨b,rfl⟩
    exact (he.dist_eq a b).symm

theorem ofOrderIso_source (S : BooleanSubalgebra A) (T : BooleanSubalgebra B)
    (e : S ≃o T) (he : Isometry e) : (ofOrderIso S T e he).source = S := by
  apply BooleanSubalgebra.ext
  intro a
  constructor
  · rintro ⟨b,c,hc⟩
    have h := congrArg Prod.fst hc
    change c.val = a at h
    exact h ▸ c.property
  · intro ha
    exact ⟨(e ⟨a,ha⟩).val, ⟨a,ha⟩, rfl⟩

theorem ofOrderIso_target (S : BooleanSubalgebra A) (T : BooleanSubalgebra B)
    (e : S ≃o T) (he : Isometry e) : (ofOrderIso S T e he).target = T := by
  apply BooleanSubalgebra.ext
  intro b
  constructor
  · rintro ⟨a,c,hc⟩
    have h := congrArg Prod.snd hc
    change (e c).val = b at h
    exact h ▸ (e c).property
  · intro hb
    refine ⟨(e.symm ⟨b,hb⟩).val, e.symm ⟨b,hb⟩, ?_⟩
    simp

theorem le_ofOrderIso_of_extends (p : BooleanPartialIsometry A B)
    (S : BooleanSubalgebra A) (T : BooleanSubalgebra B) (e : S ≃o T) (he : Isometry e)
    (hS : p.source ≤ S)
    (hext : ∀ a : p.source, (e ⟨a.val, hS a.property⟩).val = (p.orderIso a).val) :
    p ≤ ofOrderIso S T e he := by
  intro z hz
  let a : p.source := ⟨z.1, z.2, hz⟩
  refine ⟨⟨z.1, hS a.property⟩, ?_⟩
  apply Prod.ext
  · rfl
  exact (hext a).trans (p.right_unique (p.value_mem a) hz)

end ThesisCommon.BooleanPartialIsometry
