import NonCalkinAlgebra.RootedBlockDiagram
import Mathlib.Data.Finsupp.Order
import Mathlib.Order.DirectedInverseSystem

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement
universe u
variable {ι : Type u} (D : ι → RootedBlockDiagram.{u})

abbrev Level (ι : Type u) := ι →₀ ℕ
abbrev TensorColor (a : Level ι) := ∀ i, (D i).Color (a i)
abbrev TensorRow (a : Level ι) (c : TensorColor D a) := ∀ i, (D i).Row (a i) (c i)

instance tensorColorFinite (a : Level ι) : Finite (TensorColor D a) :=
  finite_pi_of_finite_active a.support (fun i hi => by
    rw [Finsupp.notMem_support_iff.mp hi]
    infer_instance)

instance tensorRowFinite (a : Level ι) (c : TensorColor D a) : Finite (TensorRow D a c) :=
  finite_pi_of_finite_active a.support (fun i hi => by
    have hroot (n : ℕ) (hn : n = 0) (d : (D i).Color n) : Subsingleton ((D i).Row n d) := by
      subst n
      infer_instance
    exact hroot (a i) (Finsupp.notMem_support_iff.mp hi) (c i))

instance tensorColorFintype (a : Level ι) : Fintype (TensorColor D a) :=
  Fintype.ofFinite _

instance tensorRowFintype (a : Level ι) (c : TensorColor D a) : Fintype (TensorRow D a c) :=
  Fintype.ofFinite _

instance tensorRowDecidableEq (a : Level ι) (c : TensorColor D a) :
    DecidableEq (TensorRow D a c) :=
  Classical.decEq _

instance tensorColorNonempty (a : Level ι) : Nonempty (TensorColor D a) :=
  ⟨fun i => Classical.choice inferInstance⟩

instance tensorRowNonempty (a : Level ι) (c : TensorColor D a) : Nonempty (TensorRow D a c) :=
  ⟨fun i => Classical.choice inferInstance⟩

def tensorRefinement (a b : Level ι) (h : a ≤ b) :
    Refinement (TensorRow D a) (TensorRow D b) :=
  Refinement.pi fun i => (D i).path (a i) (b i) (h i)

instance tensorCopiesFintype (a b : Level ι) (h : a ≤ b) (d : TensorColor D b) :
    Fintype ((tensorRefinement D a b h).Copies d) := by
  letI := finite_copies (tensorRefinement D a b h) d
  exact Fintype.ofFinite _

theorem tensorRefinement_covers (a b : Level ι) (h : a ≤ b) :
    Covers (tensorRefinement D a b h) := by
  intro c
  have hpoint i := (D i).path_covers (a i) (b i) (h i) (c i)
  choose d k hk using hpoint
  exact ⟨d, k, funext hk⟩

def tensorConnecting (a b : Level ι) (h : a ≤ b) :
    Blocks (TensorRow D a) →⋆ₐ[ℂ] Blocks (TensorRow D b) :=
  (tensorRefinement D a b h).hom

theorem tensorConnecting_injective (a b : Level ι) (h : a ≤ b) :
    Function.Injective (tensorConnecting D a b h) :=
  (tensorRefinement D a b h).hom_injective (tensorRefinement_covers D a b h)

instance tensorDirectedSystem :
    DirectedSystem (fun a : Level ι => Blocks (TensorRow D a)) (tensorConnecting D · · ·) where
  map_self := by
    intro a x
    funext c
    apply Matrix.ext
    intro i j
    have hread : (tensorRefinement D a a le_rfl).read ⟨c, i, j⟩ = some ⟨c, i, j⟩ := by
      apply (Refinement.read_pi_iff _ _ _).2
      intro k
      rw [path_self, Refinement.read_identity]
    change (tensorRefinement D a a le_rfl).hom x c i j = x c i j
    exact ((tensorRefinement D a a le_rfl).hom_entry x ⟨c, i, j⟩).trans
      (by rw [hread]; rfl)
  map_map := by
    intro c b a hab hbc x
    funext d
    apply Matrix.ext
    intro i j
    let f := tensorRefinement D a b hab
    let g := tensorRefinement D b c hbc
    let h := tensorRefinement D a c (hab.trans hbc)
    let z : Cell (TensorRow D c) := ⟨d, i, j⟩
    have hread : h.read z = (g.read z).bind f.read :=
      Refinement.read_pi_comp _ _ _ (fun k => (D k).path_read_comp (hab k) (hbc k)) z
    change g.hom (f.hom x) z.1 z.2.1 z.2.2 = h.hom x z.1 z.2.1 z.2.2
    rw [g.hom_entry, h.hom_entry, hread]
    cases hz : g.read z with
    | none => rfl
    | some y => exact f.hom_entry x y

theorem tensorRefinement_eventually_mixes
    (hD : ∀ i, (D i).EventuallyMixes) (a : Level ι) :
    ∃ b, ∃ h : a ≤ b, Mixes (tensorRefinement D a b h) := by
  classical
  have hlocal i := hD i (a i)
  choose n hn hmix using hlocal
  let b : Level ι := Finsupp.onFinset a.support
    (fun i => if i ∈ a.support then n i else 0) (by
      intro i hi
      by_contra hnmem
      simp [hnmem] at hi)
  have hab : a ≤ b := by
    intro i
    change a i ≤ if i ∈ a.support then n i else 0
    by_cases hi : i ∈ a.support
    · simpa only [if_pos hi] using hn i
    · rw [if_neg hi, Finsupp.notMem_support_iff.mp hi]
  have hpoint (i : ι) : Mixes ((D i).path (a i) (b i) (hab i)) := by
    have transfer (k l k' l' : ℕ) (hk : k = k') (hl : l = l')
        (h₁ : k ≤ l) (h₂ : k' ≤ l') :
        Mixes ((D i).path k l h₁) ↔ Mixes ((D i).path k' l' h₂) := by
      subst k'
      subst l'
      rfl
    by_cases hi : i ∈ a.support
    · have hb : b i = n i := if_pos hi
      exact (transfer _ _ _ _ rfl hb (hab i) (hn i)).2 (hmix i)
    · have ha : a i = 0 := Finsupp.notMem_support_iff.mp hi
      have hb : b i = 0 := if_neg hi
      apply (transfer _ _ _ _ ha hb (hab i) le_rfl).2
      rw [path_self]
      intro c d
      exact ⟨PUnit.unit, Subsingleton.elim _ _⟩
  refine ⟨b, hab, ?_⟩
  intro c d
  have hcopy i := hpoint i (c i) (d i)
  choose k hk using hcopy
  exact ⟨k, funext hk⟩

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
