import Mathlib.Order.BooleanSubalgebra
import Mathlib.Tactic

/-! Explicit two-piece normal forms for adjoining one element to an actual
Boolean subalgebra. The parametrization by two base elements is surjective. -/
noncomputable section
open Set
namespace ThesisCommon
variable {A : Type*} [BooleanAlgebra A]

def booleanPatch (a s t : A) : A := (s ⊓ a) ⊔ (t ⊓ aᶜ)

theorem booleanPatch_inf (a s t : A) : booleanPatch a s t ⊓ a = s ⊓ a := by
  simp [booleanPatch, inf_sup_right, inf_assoc]

theorem booleanPatch_inf_compl (a s t : A) : booleanPatch a s t ⊓ aᶜ = t ⊓ aᶜ := by
  simp [booleanPatch, inf_sup_right, inf_assoc]

theorem booleanPatch_same (a s : A) : booleanPatch a s s = s := by
  simp [booleanPatch, ← inf_sup_left]

theorem booleanPatch_sup (a s t u v : A) :
    booleanPatch a s t ⊔ booleanPatch a u v = booleanPatch a (s ⊔ u) (t ⊔ v) := by
  simp only [booleanPatch, inf_sup_right]
  ac_rfl

theorem booleanPatch_inf_patch (a s t u v : A) :
    booleanPatch a s t ⊓ booleanPatch a u v = booleanPatch a (s ⊓ u) (t ⊓ v) := by
  have hz (r q : A) : a ⊓ (r ⊓ (q ⊓ aᶜ)) = ⊥ := by
    calc
      _ = (r ⊓ q) ⊓ (a ⊓ aᶜ) := by ac_rfl
      _ = ⊥ := by simp
  simp [booleanPatch, inf_sup_left, inf_sup_right, inf_assoc, inf_left_comm, inf_comm] <;>
    simp [hz]

theorem booleanPatch_bot (a : A) : booleanPatch a ⊥ ⊥ = ⊥ := by simp [booleanPatch]

theorem booleanPatch_top (a : A) : booleanPatch a ⊤ ⊤ = ⊤ := by simp [booleanPatch]

theorem booleanPatch_compl (a s t : A) :
    (booleanPatch a s t)ᶜ = booleanPatch a sᶜ tᶜ := by
  have hi : IsCompl (booleanPatch a s t) (booleanPatch a sᶜ tᶜ) := by
    constructor
    · rw [disjoint_iff, booleanPatch_inf_patch]
      simp [booleanPatch_bot]
    · rw [codisjoint_iff, booleanPatch_sup]
      simp [booleanPatch_top]
  exact hi.compl_eq

theorem booleanPatch_le_iff (a s t u v : A) :
    booleanPatch a s t ≤ booleanPatch a u v ↔
      s ⊓ a ≤ u ⊓ a ∧ t ⊓ aᶜ ≤ v ⊓ aᶜ := by
  constructor
  · intro h
    exact ⟨by simpa only [booleanPatch_inf] using inf_le_inf_right a h,
      by simpa only [booleanPatch_inf_compl] using inf_le_inf_right aᶜ h⟩
  · rintro ⟨h, h'⟩
    exact sup_le_sup h h'

def booleanAdjoinOne (S : BooleanSubalgebra A) (a : A) : BooleanSubalgebra A :=
  BooleanSubalgebra.closure ((S : Set A) ∪ {a})

theorem booleanAdjoinOne_base (S : BooleanSubalgebra A) (a : A) : S ≤ booleanAdjoinOne S a :=
  fun _ hx => BooleanSubalgebra.subset_closure (Or.inl hx)

theorem booleanAdjoinOne_generator (S : BooleanSubalgebra A) (a : A) : a ∈ booleanAdjoinOne S a :=
  BooleanSubalgebra.subset_closure (Or.inr (mem_singleton a))

theorem booleanPatch_mem_adjoin (S : BooleanSubalgebra A) (a : A) (s t : S) :
    booleanPatch a s.val t.val ∈ booleanAdjoinOne S a :=
  BooleanSubalgebra.sup_mem
    (BooleanSubalgebra.inf_mem (booleanAdjoinOne_base S a s.property) (booleanAdjoinOne_generator S a))
    (BooleanSubalgebra.inf_mem (booleanAdjoinOne_base S a t.property)
      (BooleanSubalgebra.compl_mem (booleanAdjoinOne_generator S a)))

theorem mem_booleanAdjoinOne_iff (S : BooleanSubalgebra A) (a x : A) :
    x ∈ booleanAdjoinOne S a ↔ ∃ s t : S, x = booleanPatch a s.val t.val := by
  let N : BooleanSubalgebra A :=
    { carrier := {x | ∃ s t : S, x = booleanPatch a s.val t.val}
      bot_mem' := ⟨⊥, ⊥, (booleanPatch_bot a).symm⟩
      supClosed' := by
        rintro x ⟨s,t,rfl⟩ y ⟨u,v,rfl⟩
        exact ⟨s ⊔ u, t ⊔ v, booleanPatch_sup a s t u v⟩
      infClosed' := by
        rintro x ⟨s,t,rfl⟩ y ⟨u,v,rfl⟩
        exact ⟨s ⊓ u, t ⊓ v, booleanPatch_inf_patch a s t u v⟩
      compl_mem' := by
        rintro x ⟨s,t,rfl⟩
        exact ⟨sᶜ,tᶜ,booleanPatch_compl a s t⟩ }
  constructor
  · intro hx
    have hle : booleanAdjoinOne S a ≤ N := BooleanSubalgebra.closure_le.mpr (by
      rintro y (hy | hy)
      · exact ⟨⟨y,hy⟩,⟨y,hy⟩,(booleanPatch_same a y).symm⟩
      · rcases mem_singleton_iff.mp hy with rfl
        exact ⟨⊤,⊥,by simp [booleanPatch]⟩)
    exact hle hx
  · rintro ⟨s,t,rfl⟩
    exact booleanPatch_mem_adjoin S a s t

def booleanAdjoinOnePairMap (S : BooleanSubalgebra A) (a : A) : S × S → booleanAdjoinOne S a :=
  fun st => ⟨booleanPatch a st.1.val st.2.val, booleanPatch_mem_adjoin S a st.1 st.2⟩

theorem booleanAdjoinOnePairMap_surjective (S : BooleanSubalgebra A) (a : A) :
    Function.Surjective (booleanAdjoinOnePairMap S a) := by
  intro x
  obtain ⟨s,t,h⟩ := (mem_booleanAdjoinOne_iff S a x.val).mp x.property
  exact ⟨(s,t), Subtype.ext h.symm⟩

end ThesisCommon
