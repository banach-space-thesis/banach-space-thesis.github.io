import NonCalkinAlgebra.FiniteBlockComposition

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement

universe u
variable {C D E : Type u} {P : C → Type u} {Q : D → Type u} {R : E → Type u}

/-- Identity refinement, with exactly one copy of the original block. -/
def identity (P : C → Type u) : Refinement P P where
  Copies _ := PUnit
  color c _ := c
  rows c :=
    { toFun := Sigma.snd
      invFun := fun x => ⟨PUnit.unit, x⟩
      left_inv := fun ⟨⟨⟩, _⟩ => rfl
      right_inv := fun _ => rfl }

instance identityCopies (c : C) : Fintype ((identity P).Copies c) :=
  inferInstanceAs (Fintype PUnit)

theorem identity_hom [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)] :
    (identity P).hom = StarAlgHom.id ℂ (Blocks P) := by
  apply StarAlgHom.ext
  intro x
  funext c
  ext i j
  exact (identity P).hom_apply_same x c PUnit.unit i j

/-- Copy indices are finite when source blocks have rows and target blocks have finitely many rows. -/
theorem finite_copies (f : Refinement P Q) [∀ c, Nonempty (P c)] (d : D)
    [Finite (Q d)] : Finite (f.Copies d) :=
  Finite.of_injective (fun k => f.rows d ⟨k, Classical.choice (inferInstance : Nonempty (P _))⟩)
    (fun _ _ h => congrArg Sigma.fst ((f.rows d).injective h))

/-- A source block has at least one copy somewhere in the target. -/
def Covers (f : Refinement P Q) : Prop :=
  ∀ c, ∃ d k, f.color d k = c

/-- Every target block contains a copy of every source block. -/
def Mixes (f : Refinement P Q) : Prop :=
  ∀ c d, ∃ k, f.color d k = c

theorem identity_covers : Covers (identity P) :=
  fun c => ⟨c, PUnit.unit, rfl⟩

theorem covers_trans {f : Refinement P Q} {g : Refinement Q R} (hf : Covers f)
    (hg : Covers g) : Covers (f.trans g) := by
  intro c
  obtain ⟨d, k, hk⟩ := hf c
  obtain ⟨e, l, rfl⟩ := hg d
  exact ⟨e, ⟨l, k⟩, hk⟩

theorem mixes_of_covers_of_mixes {f : Refinement P Q} {g : Refinement Q R} (hf : Covers f)
    (hg : Mixes g) : Mixes (f.trans g) := by
  intro c e
  obtain ⟨d, k, hk⟩ := hf c
  obtain ⟨l, rfl⟩ := hg d e
  exact ⟨⟨l, k⟩, hk⟩

theorem mixes_of_mixes_of_nonempty {f : Refinement P Q} {g : Refinement Q R} (hf : Mixes f)
    (hg : ∀ e, Nonempty (g.Copies e)) : Mixes (f.trans g) := by
  intro c e
  obtain ⟨l⟩ := hg e
  obtain ⟨k, hk⟩ := hf c (g.color e l)
  exact ⟨⟨l, k⟩, hk⟩

end NonCalkinAlgebra.FiniteBlockRefinement
