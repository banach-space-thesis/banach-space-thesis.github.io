import NonCalkinAlgebra.FiniteBlockIdentity
import NonCalkinAlgebra.ProductBlockRefinement

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
universe u
variable {C D E : Type u} {P : C → Type u} {Q : D → Type u} {R : E → Type u}

/-- A matrix entry specified by a block and a pair of row indices. -/
abbrev Cell (P : C → Type u) := Σ c : C, P c × P c

namespace Refinement

open Classical in
private def readRows (f : Refinement P Q) (d : D)
    (a b : Σ k : f.Copies d, P (f.color d k)) : Option (Cell P) :=
  if h : a.1 = b.1 then
    some ⟨f.color d a.1, a.2, cast (congrArg (P ∘ f.color d) h.symm) b.2⟩
  else none

/-- An output entry is either copied from one input entry or set to zero. -/
def read (f : Refinement P Q) (x : Cell Q) : Option (Cell P) :=
  f.readRows x.1 ((f.rows x.1).symm x.2.1) ((f.rows x.1).symm x.2.2)

@[simp] theorem read_same (f : Refinement P Q) (d : D) (k : f.Copies d)
    (x y : P (f.color d k)) :
    f.read ⟨d, f.rows d ⟨k, x⟩, f.rows d ⟨k, y⟩⟩ = some ⟨f.color d k, x, y⟩ := by
  unfold read
  dsimp only
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp [readRows]

theorem read_ne (f : Refinement P Q) (d : D) {k l : f.Copies d}
    (h : k ≠ l) (x : P (f.color d k)) (y : P (f.color d l)) :
    f.read ⟨d, f.rows d ⟨k, x⟩, f.rows d ⟨l, y⟩⟩ = none := by
  simp [read, readRows, h]

@[simp] theorem read_identity (x : Cell P) : (identity P).read x = some x := by
  obtain ⟨c, a, b⟩ := x
  exact (identity P).read_same c PUnit.unit a b

theorem read_trans (f : Refinement P Q) (g : Refinement Q R) (x : Cell R) :
    (f.trans g).read x = (g.read x).bind f.read := by
  obtain ⟨e, a, b⟩ := x
  obtain ⟨⟨⟨l, k⟩, i⟩, rfl⟩ := ((f.trans g).rows e).surjective a
  obtain ⟨⟨⟨l', k'⟩, j⟩, rfl⟩ := ((f.trans g).rows e).surjective b
  by_cases h : l = l'
  · subst l'
    simp only [then_rows, read_same, Option.bind_some]
    by_cases hk : k = k'
    · subst k'
      exact ((f.trans g).read_same e ⟨l, k⟩ i j).trans
        (f.read_same (g.color e l) k i j).symm
    · have hpair : (⟨l, k⟩ : (f.trans g).Copies e) ≠ ⟨l, k'⟩ :=
        fun hp => hk (eq_of_heq (Sigma.mk.inj_iff.mp hp).2)
      exact ((f.trans g).read_ne e hpair i j).trans
        (f.read_ne (g.color e l) hk i j).symm
  · have hpair : (⟨l, k⟩ : (f.trans g).Copies e) ≠ ⟨l', k'⟩ :=
      fun hp => h (congrArg Sigma.fst hp)
    rw [(f.trans g).read_ne e hpair, then_rows, then_rows, g.read_ne e h]
    rfl

theorem hom_entry [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
    (f : Refinement P Q) [∀ d, Fintype (f.Copies d)] (a : Blocks P) (x : Cell Q) :
    f.hom a x.1 x.2.1 x.2.2 =
      ((f.read x).map fun y => a y.1 y.2.1 y.2.2).getD 0 := by
  obtain ⟨d, i, j⟩ := x
  obtain ⟨⟨k, i⟩, rfl⟩ := (f.rows d).surjective i
  obtain ⟨⟨l, j⟩, rfl⟩ := (f.rows d).surjective j
  by_cases h : k = l
  · subst l
    rw [read_same, hom_apply_same]
    rfl
  · rw [f.read_ne d h, f.hom_apply_ne a d h]
    rfl


section Product
variable {ι : Type u} {C D E : ι → Type u}
  {P : ∀ i, C i → Type u} {Q : ∀ i, D i → Type u} {R : ∀ i, E i → Type u}

/-- The coordinates of a matrix cell of a product of blocks. -/
def cellCoordinates :
    Cell (fun c : ∀ i, C i => ∀ i, P i (c i)) ≃ (∀ i, Cell (P i)) where
  toFun x i := ⟨x.1 i, x.2.1 i, x.2.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2.1, fun i => (x i).2.2⟩
  left_inv := by rintro ⟨c, a, b⟩; rfl
  right_inv := by intro x; funext i; rfl

theorem read_pi_iff (f : ∀ i, Refinement (P i) (Q i))
    (x : Cell (fun d : ∀ i, D i => ∀ i, Q i (d i)))
    (y : Cell (fun c : ∀ i, C i => ∀ i, P i (c i))) :
    (pi f).read x = some y ↔
      ∀ i, (f i).read (cellCoordinates x i) = some (cellCoordinates y i) := by
  obtain ⟨d, a, b⟩ := x
  obtain ⟨⟨k, a⟩, rfl⟩ := ((pi f).rows d).surjective a
  obtain ⟨⟨l, b⟩, rfl⟩ := ((pi f).rows d).surjective b
  by_cases h : k = l
  · subst l
    rw [(pi f).read_same]
    constructor
    · intro hy i
      have hy' := Option.some.inj hy
      subst y
      exact (f i).read_same (d i) (k i) (a i) (b i)
    · intro hy
      congr 1
      apply cellCoordinates.injective
      funext i
      have hi := (f i).read_same (d i) (k i) (a i) (b i)
      exact Option.some.inj (hi.symm.trans (hy i))
  · rw [(pi f).read_ne d h]
    constructor
    · intro hnone
      cases hnone
    · intro hy
      exfalso
      apply h
      funext i
      by_contra hne
      have hi := (f i).read_ne (d i) hne (a i) (b i)
      have := hi.symm.trans (hy i)
      cases this

theorem read_pi_comp (f : ∀ i, Refinement (P i) (Q i))
    (g : ∀ i, Refinement (Q i) (R i)) (h : ∀ i, Refinement (P i) (R i))
    (hlocal : ∀ i x, (h i).read x = ((g i).read x).bind (f i).read)
    (x : Cell (fun e : ∀ i, E i => ∀ i, R i (e i))) :
    (pi h).read x = ((pi g).read x).bind (pi f).read := by
  have hsome (y : Cell (fun c : ∀ i, C i => ∀ i, P i (c i))) :
      (pi h).read x = some y ↔ ((pi g).read x).bind (pi f).read = some y := by
    rw [read_pi_iff, Option.bind_eq_some_iff]
    simp_rw [hlocal, Option.bind_eq_some_iff]
    constructor
    · intro hy
      choose z hgz hfz using hy
      refine ⟨cellCoordinates.symm z, (read_pi_iff _ _ _).2 ?_,
        (read_pi_iff _ _ _).2 ?_⟩
      · intro i
        simpa only [Equiv.apply_symm_apply] using hgz i
      · intro i
        simpa only [Equiv.apply_symm_apply] using hfz i
    · rintro ⟨z, hg, hf⟩ i
      exact ⟨cellCoordinates z i, (read_pi_iff _ _ _).1 hg i,
        (read_pi_iff _ _ _).1 hf i⟩
  cases ha : (pi h).read x with
  | some y => exact ((hsome y).mp ha).symm
  | none =>
    cases hb : ((pi g).read x).bind (pi f).read with
    | none => rfl
    | some y =>
      have hnone := (hsome y).mpr hb
      rw [ha] at hnone
      cases hnone

end Product

end Refinement
end NonCalkinAlgebra.FiniteBlockRefinement
