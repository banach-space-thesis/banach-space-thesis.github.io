import NonCalkinAlgebra.ProductAFAlgebra
import NonCalkinAlgebra.DiagramTraceLaw

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement

universe u
variable {ι : Type u} (D : ι → RootedBlockDiagram.{u})

private def evalAtEquiv (T : ι → Type u) [∀ j, Nonempty (T j)] (i : ι)
    (h : ∀ j ≠ i, Subsingleton (T j)) : (∀ j, T j) ≃ T i := by
  classical
  refine
    { toFun := fun x => x i
      invFun := fun x j => if hj : j = i then hj.symm ▸ x else Classical.choice inferInstance
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · letI := h j hj
      exact Subsingleton.elim _ _
  · intro x
    simp

def coordinateColorEquiv (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0) :
    TensorColor D a ≃ (D i).Color (a i) :=
  evalAtEquiv _ i fun j hj => by rw [h j hj]; infer_instance

def coordinateRowEquiv (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0)
    (c : TensorColor D a) : TensorRow D a c ≃ (D i).Row (a i) (c i) :=
  evalAtEquiv _ i fun j hj => by
    have hroot (n : ℕ) (hn : n = 0) (d : (D j).Color n) :
        Subsingleton ((D j).Row n d) := by subst n; infer_instance
    exact hroot (a j) (h j hj) (c j)

def coordinateRefinement (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0) :
    Refinement ((D i).Row (a i)) (TensorRow D a) where
  Copies _ := PUnit
  color c _ := c i
  rows c := ((identity ((D i).Row (a i))).rows (c i)).trans (coordinateRowEquiv D a i h c).symm

instance coordinateCopiesFintype (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0)
    (c : TensorColor D a) : Fintype ((coordinateRefinement D a i h).Copies c) :=
  inferInstanceAs (Fintype PUnit)

theorem coordinateRefinement_read (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0)
    (x : Cell (TensorRow D a)) :
    (coordinateRefinement D a i h).read x = some (Refinement.cellCoordinates x i) := by
  obtain ⟨c, x, y⟩ := x
  let f := coordinateRefinement D a i h
  let e := coordinateRowEquiv D a i h c
  have hx : f.rows c ⟨PUnit.unit, x i⟩ = x := e.symm_apply_apply x
  have hy : f.rows c ⟨PUnit.unit, y i⟩ = y := e.symm_apply_apply y
  change f.read ⟨c, x, y⟩ = some ⟨c i, x i, y i⟩
  have hr := f.read_same c PUnit.unit (x i) (y i)
  rw [hx, hy] at hr
  exact hr

private theorem rootPath_read (B : RootedBlockDiagram.{u}) (a b : ℕ)
    (ha : a = 0) (hb : b = 0) (hab : a ≤ b) (x : Cell (B.Row b)) (y : Cell (B.Row a)) :
    (B.path a b hab).read x = some y := by
  subst a
  subst b
  rw [path_self, Refinement.read_identity]
  obtain ⟨c, x, x'⟩ := x
  obtain ⟨d, y, y'⟩ := y
  have hd : d = c := Subsingleton.elim _ _
  subst d
  rw [Subsingleton.elim x y, Subsingleton.elim x' y']

theorem coordinateRefinement_compatible (a b : Level ι) (hab : a ≤ b)
    (i : ι) (ha : ∀ j ≠ i, a j = 0) (hb : ∀ j ≠ i, b j = 0)
    (x : Cell (TensorRow D b)) :
    ((tensorRefinement D a b hab).read x).bind (coordinateRefinement D a i ha).read =
      ((coordinateRefinement D b i hb).read x).bind ((D i).path (a i) (b i) (hab i)).read := by
  rw [coordinateRefinement_read, Option.bind_some]
  let f j := (D j).path (a j) (b j) (hab j)
  cases hx : (tensorRefinement D a b hab).read x with
  | some y =>
    rw [Option.bind_some, coordinateRefinement_read]
    exact ((Refinement.read_pi_iff f x y).1 hx i).symm
  | none =>
    change none = (f i).read (Refinement.cellCoordinates x i)
    cases hy : (f i).read (Refinement.cellCoordinates x i) with
    | none => rfl
    | some yi =>
      let ys (j : ι) : Cell ((D j).Row (a j)) := by
        classical
        exact if hj : j = i then hj.symm ▸ yi else
          ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance⟩
      let y : Cell (TensorRow D a) := Refinement.cellCoordinates.symm ys
      have hpi : (tensorRefinement D a b hab).read x = some y := by
        apply (Refinement.read_pi_iff f x y).2
        intro j
        change (f j).read _ = some (Refinement.cellCoordinates (Refinement.cellCoordinates.symm ys) j)
        rw [Equiv.apply_symm_apply]
        by_cases hj : j = i
        · subst j
          simpa [ys] using hy
        · exact rootPath_read (D j) (a j) (b j) (ha j hj) (hb j hj) (hab j) _ _
      rw [hx] at hpi
      cases hpi


instance localRowFintype (B : RootedBlockDiagram.{u}) (n : ℕ) (c : B.Color n) :
    Fintype (B.Row n c) := Fintype.ofFinite _

instance localRowDecidableEq (B : RootedBlockDiagram.{u}) (n : ℕ) (c : B.Color n) :
    DecidableEq (B.Row n c) := Classical.decEq _

instance localStepCopiesFintype (B : RootedBlockDiagram.{u}) (n : ℕ) (d : B.Color (n+1)) :
    Fintype ((B.step n).Copies d) := by
  letI := finite_copies (B.step n) d
  exact Fintype.ofFinite _

def coordinateMap (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0) :
    Blocks ((D i).Row (a i)) →⋆ₐ[ℂ] TensorStage D a :=
  (coordinateRefinement D a i h).hom

theorem coordinateMap_entry (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0)
    (x : Blocks ((D i).Row (a i))) (c : TensorColor D a) (r s : TensorRow D a c) :
    coordinateMap D a i h x c r s = x (c i) (r i) (s i) := by
  exact ((coordinateRefinement D a i h).hom_entry x ⟨c, r, s⟩).trans
    (by rw [coordinateRefinement_read]; rfl)

theorem coordinateMap_compatible (a b : Level ι) (hab : a ≤ b) (i : ι)
    (ha : ∀ j ≠ i, a j = 0) (hb : ∀ j ≠ i, b j = 0)
    (x : Blocks ((D i).Row (a i))) :
    tensorConnecting D a b hab (coordinateMap D a i ha x) =
      coordinateMap D b i hb (((D i).path (a i) (b i) (hab i)).hom x) := by
  funext d
  apply Matrix.ext
  intro r s
  let z : Cell (TensorRow D b) := ⟨d, r, s⟩
  let f := tensorRefinement D a b hab
  let g := (D i).path (a i) (b i) (hab i)
  change f.hom (coordinateMap D a i ha x) d r s = _
  rw [coordinateMap_entry]
  have hc := coordinateRefinement_compatible D a b hab i ha hb z
  rw [coordinateRefinement_read, Option.bind_some] at hc
  change f.hom (coordinateMap D a i ha x) z.1 z.2.1 z.2.2 =
    g.hom x (Refinement.cellCoordinates z i).1
      (Refinement.cellCoordinates z i).2.1 (Refinement.cellCoordinates z i).2.2
  rw [f.hom_entry, g.hom_entry, ← hc]
  cases hr : f.read z with
  | none => rfl
  | some y =>
    rw [Option.bind_some, coordinateRefinement_read]
    exact coordinateMap_entry D a i ha x y.1 y.2.1 y.2.2

open NonCalkinAlgebra.NormedStarDirectLimit
open scoped NonCalkinAlgebra.NormedStarCompletion Matrix.Norms.L2Operator

def coordinateInclusion (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0) :
    Blocks ((D i).Row (a i)) →⋆ₐ[ℂ] TensorLimit D :=
  (completedEmbedding (tensorConnecting D) a).comp (coordinateMap D a i h)

theorem coordinateInclusion_compatible (a b : Level ι) (hab : a ≤ b) (i : ι)
    (ha : ∀ j ≠ i, a j = 0) (hb : ∀ j ≠ i, b j = 0)
    (x : Blocks ((D i).Row (a i))) :
    coordinateInclusion D b i hb (((D i).path (a i) (b i) (hab i)).hom x) =
      coordinateInclusion D a i ha x := by
  change completedEmbedding (tensorConnecting D) b (coordinateMap D b i hb _) =
    completedEmbedding (tensorConnecting D) a (coordinateMap D a i ha x)
  rw [← coordinateMap_compatible D a b hab i ha hb x, completedEmbedding_map]

def coordinateInclusionAt (a : Level ι) (i : ι) (h : ∀ j ≠ i, a j = 0)
    (n : ℕ) (hn : a i = n) : Blocks ((D i).Row n) →⋆ₐ[ℂ] TensorLimit D :=
  hn ▸ coordinateInclusion D a i h

theorem coordinateInclusionAt_compatible (a b : Level ι) (hab : a ≤ b) (i : ι)
    (ha : ∀ j ≠ i, a j = 0) (hb : ∀ j ≠ i, b j = 0)
    (n m : ℕ) (hn : a i = n) (hm : b i = m) (hnm : n ≤ m) (x : Blocks ((D i).Row n)) :
    coordinateInclusionAt D b i hb m hm (((D i).path n m hnm).hom x) =
      coordinateInclusionAt D a i ha n hn x := by
  subst n
  subst m
  exact coordinateInclusion_compatible D a b hab i ha hb x

def levelAt (i : ι) (n : ℕ) : Level ι := Finsupp.single i n

@[simp] theorem levelAt_self (i : ι) (n : ℕ) : levelAt i n i = n :=
  Finsupp.single_eq_same

theorem levelAt_other (i j : ι) (n : ℕ) (h : j ≠ i) : levelAt i n j = 0 :=
  Finsupp.single_eq_of_ne h

theorem levelAt_le (i : ι) {n m : ℕ} (h : n ≤ m) : levelAt i n ≤ levelAt i m := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [levelAt_self] using h
  · rw [levelAt_other _ _ _ hj, levelAt_other _ _ _ hj]

def coordinateEmbedding (i : ι) (n : ℕ) :
    Blocks ((D i).Row n) →⋆ₐ[ℂ] TensorLimit D :=
  coordinateInclusionAt D (levelAt i n) i (fun j hj => levelAt_other i j n hj) n (levelAt_self i n)

theorem coordinateEmbedding_path (i : ι) (n m : ℕ) (h : n ≤ m)
    (x : Blocks ((D i).Row n)) :
    coordinateEmbedding D i m (((D i).path n m h).hom x) = coordinateEmbedding D i n x :=
  coordinateInclusionAt_compatible D _ _ (levelAt_le i h) i _ _ n m _ _ h x

theorem coordinateEmbedding_step (i : ι) (n : ℕ) (x : Blocks ((D i).Row n)) :
    coordinateEmbedding D i (n+1) (((D i).step n).hom x) = coordinateEmbedding D i n x := by
  have hstep : ((D i).path n (n+1) (Nat.le_succ n)).hom = ((D i).step n).hom := by
    apply StarAlgHom.ext
    intro y
    funext c
    apply Matrix.ext
    intro r s
    let z : Cell ((D i).Row (n+1)) := ⟨c, r, s⟩
    change ((D i).path n (n+1) (Nat.le_succ n)).hom y z.1 z.2.1 z.2.2 =
      ((D i).step n).hom y z.1 z.2.1 z.2.2
    rw [Refinement.hom_entry, Refinement.hom_entry]
    have hread : ((D i).path n (n+1) (Nat.le_succ n)).read z = ((D i).step n).read z := by
      rw [(D i).path_succ n n le_rfl, (D i).path_self, Refinement.read_trans]
      cases ((D i).step n).read z <;> simp
    rw [hread]
  rw [← hstep]
  exact coordinateEmbedding_path D i n (n+1) (Nat.le_succ n) x

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
