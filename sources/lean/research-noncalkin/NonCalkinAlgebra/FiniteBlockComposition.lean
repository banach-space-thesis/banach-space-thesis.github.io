import NonCalkinAlgebra.FiniteBlockRefinement

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.Refinement
open NonCalkinAlgebra.FiniteBlockRefinement

universe u
variable {C D E : Type u} {P : C → Type u} {Q : D → Type u} {R : E → Type u}

/-- A copy in a composite refinement records the two successive copy choices. -/
def trans (f : Refinement P Q) (g : Refinement Q R) : Refinement P R where
  Copies e := Σ l : g.Copies e, f.Copies (g.color e l)
  color e k := f.color (g.color e k.1) k.2
  rows e := (Equiv.sigmaAssoc _).trans
    ((Equiv.sigmaCongrRight (fun l => f.rows (g.color e l))).trans (g.rows e))

instance (f : Refinement P Q) (g : Refinement Q R)
    [∀ d, Fintype (f.Copies d)] [∀ e, Fintype (g.Copies e)] (e : E) :
    Fintype ((f.trans g).Copies e) :=
  inferInstanceAs (Fintype (Σ l : g.Copies e, f.Copies (g.color e l)))

@[simp] theorem then_rows (f : Refinement P Q) (g : Refinement Q R)
    (e : E) (l : g.Copies e) (k : f.Copies (g.color e l))
    (i : P (f.color (g.color e l) k)) :
    (f.trans g).rows e ⟨⟨l, k⟩, i⟩ = g.rows e ⟨l, f.rows (g.color e l) ⟨k, i⟩⟩ :=
  rfl

section
variable [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
variable [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
variable [∀ e, Fintype (R e)] [∀ e, DecidableEq (R e)]

theorem then_hom (f : Refinement P Q) (g : Refinement Q R)
    [∀ d, Fintype (f.Copies d)] [∀ e, Fintype (g.Copies e)] :
    (f.trans g).hom = g.hom.comp f.hom := by
  apply StarAlgHom.ext
  intro x
  funext e
  apply Matrix.ext
  intro a b
  obtain ⟨⟨⟨l, k⟩, i⟩, rfl⟩ := ((f.trans g).rows e).surjective a
  obtain ⟨⟨⟨l', k'⟩, j⟩, rfl⟩ := ((f.trans g).rows e).surjective b
  change (f.trans g).hom x e ((f.trans g).rows e ⟨⟨l, k⟩, i⟩)
      ((f.trans g).rows e ⟨⟨l', k'⟩, j⟩) =
    g.hom (f.hom x) e (g.rows e ⟨l, f.rows (g.color e l) ⟨k, i⟩⟩)
      (g.rows e ⟨l', f.rows (g.color e l') ⟨k', j⟩⟩)
  by_cases h : l = l'
  · subst l'
    rw [g.hom_apply_same]
    by_cases hk : k = k'
    · subst k'
      exact ((f.trans g).hom_apply_same x e ⟨l, k⟩ i j).trans
        (f.hom_apply_same x (g.color e l) k i j).symm
    · have hpair : (⟨l, k⟩ : (f.trans g).Copies e) ≠ ⟨l, k'⟩ :=
        fun hp => hk (eq_of_heq (Sigma.mk.inj_iff.mp hp).2)
      rw [(f.trans g).hom_apply_ne x e hpair, f.hom_apply_ne x (g.color e l) hk]
  · have hpair : (⟨l, k⟩ : (f.trans g).Copies e) ≠ ⟨l', k'⟩ :=
      fun hp => h (congrArg Sigma.fst hp)
    rw [(f.trans g).hom_apply_ne x e hpair, g.hom_apply_ne _ e h]

end
end NonCalkinAlgebra.FiniteBlockRefinement.Refinement
