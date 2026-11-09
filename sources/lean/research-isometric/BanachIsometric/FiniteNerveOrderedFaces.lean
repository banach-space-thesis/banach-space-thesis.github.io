import BanachIsometric.FiniteNervePolyhedron
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! The ordered simplicial set of an actual finite face complex. Its
monotone vertex tuples include degeneracies; strict tuples are exactly the
ordinary ordered faces used by the bounded chain complex built next.
No comparison with singular topology is asserted here. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open CategoryTheory Simplicial Opposite

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def OrderedSimplex (K : Complex ι) (n : ℕ) :=
  {v : Fin (n + 1) →o ι // Finset.univ.image v ∈ K.faces}

instance (K : Complex ι) (n : ℕ) : Finite (OrderedSimplex K n) := by
  apply Finite.of_injective (fun v : OrderedSimplex K n => (v.val : Fin (n + 1) → ι))
  intro v w h
  apply Subtype.ext
  ext i
  exact congrFun h i

instance (K : Complex ι) (n : ℕ) : Fintype (OrderedSimplex K n) := Fintype.ofFinite _

def pullbackOrderedSimplex (K : Complex ι) {a b : SimplexCategory}
    (θ : a ⟶ b) (v : OrderedSimplex K b.len) : OrderedSimplex K a.len := by
  refine ⟨v.val.comp θ.toOrderHom, K.downward _ v.property _ ?_ ?_⟩
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨θ.toOrderHom j, Finset.mem_univ _, rfl⟩
  · exact ⟨v.val (θ.toOrderHom 0), Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem pullbackOrderedSimplex_apply (K : Complex ι) {a b : SimplexCategory}
    (θ : a ⟶ b) (v : OrderedSimplex K b.len) (j : Fin (a.len + 1)) :
    (pullbackOrderedSimplex K θ v).val j = v.val (θ.toOrderHom j) := rfl

def orderedFace (K : Complex ι) {n : ℕ} (i : Fin (n + 2))
    (v : OrderedSimplex K (n + 1)) : OrderedSimplex K n :=
  pullbackOrderedSimplex K (SimplexCategory.δ i) v

@[simp] theorem orderedFace_apply (K : Complex ι) {n : ℕ} (i : Fin (n + 2))
    (v : OrderedSimplex K (n + 1)) (j : Fin (n + 1)) :
    (orderedFace K i v).val j = v.val (i.succAbove j) := rfl

theorem orderedFace_strictMono (K : Complex ι) {n : ℕ} (i : Fin (n + 2))
    (v : OrderedSimplex K (n + 1)) (hv : StrictMono v.val) :
    StrictMono (orderedFace K i v).val :=
  hv.comp (Fin.succAboveOrderEmb i).strictMono

def StrictOrderedSimplex (K : Complex ι) (n : ℕ) :=
  {v : OrderedSimplex K n // StrictMono v.val}

instance (K : Complex ι) (n : ℕ) : Finite (StrictOrderedSimplex K n) :=
  Finite.of_injective (fun v : StrictOrderedSimplex K n => v.val) (fun _ _ h => Subtype.ext h)

instance (K : Complex ι) (n : ℕ) : Fintype (StrictOrderedSimplex K n) :=
  Fintype.ofFinite _

def strictOrderedFace (K : Complex ι) {n : ℕ} (i : Fin (n + 2))
    (v : StrictOrderedSimplex K (n + 1)) : StrictOrderedSimplex K n :=
  ⟨orderedFace K i v.val, orderedFace_strictMono K i v.val v.property⟩

theorem isEmpty_strictOrderedSimplex (K : Complex ι) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    IsEmpty (StrictOrderedSimplex K n) := by
  refine ⟨fun v => ?_⟩
  have hcard := Fintype.card_le_of_injective _ v.property.injective
  simp only [Fintype.card_fin] at hcard
  omega

end BanachIsometric.FiniteNerve
