import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Compatibility lemmas for the actual pinned fundamental groupoid. These
are quotient operations of continuous paths and their genuine homotopies. -/

noncomputable section

attribute [local instance] Path.Homotopic.setoid

namespace Path.Homotopic.Quotient

variable {X : Type*} [TopologicalSpace X] {a b c d : X}

def mk (p : Path a b) : Path.Homotopic.Quotient a b := Quotient.mk' p
def trans (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) :
    Path.Homotopic.Quotient a c := p.comp q
def refl (a : X) : Path.Homotopic.Quotient a a := mk (Path.refl a)
def symm (p : Path.Homotopic.Quotient a b) : Path.Homotopic.Quotient b a :=
  @CategoryTheory.Groupoid.inv (FundamentalGroupoid X) _ ⟨a⟩ ⟨b⟩ p

theorem eq {p q : Path a b} : mk p = mk q ↔ p.Homotopic q := _root_.Quotient.eq
@[simp] theorem mk_trans (p : Path a b) (q : Path b c) :
    mk (p.trans q) = trans (mk p) (mk q) := rfl
@[simp] theorem mk_symm (p : Path a b) : mk p.symm = symm (mk p) := rfl
@[simp] theorem mk_refl (a : X) : mk (Path.refl a) = refl a := rfl
theorem trans_assoc (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) (r : Path.Homotopic.Quotient c d) :
    trans (trans p q) r = trans p (trans q r) :=
  @CategoryTheory.Category.assoc (FundamentalGroupoid X) _ ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩ p q r
@[simp] theorem refl_trans (p : Path.Homotopic.Quotient a b) : trans (refl a) p = p :=
  @CategoryTheory.Category.id_comp (FundamentalGroupoid X) _ ⟨a⟩ ⟨b⟩ p
@[simp] theorem trans_refl (p : Path.Homotopic.Quotient a b) : trans p (refl b) = p :=
  @CategoryTheory.Category.comp_id (FundamentalGroupoid X) _ ⟨a⟩ ⟨b⟩ p
@[simp] theorem symm_trans (p : Path.Homotopic.Quotient a b) : trans (symm p) p = refl b :=
  @CategoryTheory.Groupoid.inv_comp (FundamentalGroupoid X) _ ⟨a⟩ ⟨b⟩ p
@[simp] theorem trans_symm (p : Path.Homotopic.Quotient a b) : trans p (symm p) = refl a :=
  @CategoryTheory.Groupoid.comp_inv (FundamentalGroupoid X) _ ⟨a⟩ ⟨b⟩ p

end Path.Homotopic.Quotient

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b a' b' c c' : X}

theorem cast_symm (p : Path a b) (ha : a' = a) (hb : b' = b) :
    p.symm.cast hb ha = (p.cast ha hb).symm := (p.symm_cast ha hb).symm
theorem cast_trans (p : Path a b) (q : Path b c)
    (ha : a' = a) (hb : b' = b) (hc : c' = c) :
    (p.trans q).cast ha hc = (p.cast ha hb).trans (q.cast hb hc) :=
  (p.trans_cast q ha hb hc).symm

theorem Homotopic.pathCast {p q : Path a b} (h : p.Homotopic q)
    (ha : a' = a) (hb : b' = b) : (p.cast ha hb).Homotopic (q.cast ha hb) := h

end Path
