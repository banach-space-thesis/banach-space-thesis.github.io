import NonCalkinAlgebra.ProductCoordinateEmbedding
import NonCalkinAlgebra.ProductAFDensity
import NonCalkinAlgebra.FiniteBlockTraceCoefficients
import NonCalkinAlgebra.TraceMatrixNorm

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement NonCalkinAlgebra.NormedStarDirectLimit
open scoped Matrix.Norms.L2Operator NonCalkinAlgebra.NormedStarCompletion

universe u
variable {ι : Type u} (D : ι → RootedBlockDiagram.{u})

private def localCell (i : ι) (a : Level ι) (n : ℕ) (h : a i = n)
    (x : Cell (TensorRow D a)) : Cell ((D i).Row n) :=
  h ▸ Refinement.cellCoordinates x i

private def coordinateImageAt (a b : Level ι) (hab : a ≤ b) (i : ι)
    (ha : ∀ j ≠ i, a j = 0) (n : ℕ) (hn : a i = n)
    (x : Blocks ((D i).Row n)) : TensorStage D b :=
  tensorConnecting D a b hab ((hn ▸ coordinateMap D a i ha) x)

private theorem completed_coordinateImageAt (a b : Level ι) (hab : a ≤ b) (i : ι)
    (ha : ∀ j ≠ i, a j = 0) (n : ℕ) (hn : a i = n) (x : Blocks ((D i).Row n)) :
    completedEmbedding (tensorConnecting D) b (coordinateImageAt D a b hab i ha n hn x) =
      coordinateInclusionAt D a i ha n hn x := by
  subst n
  exact completedEmbedding_map (tensorConnecting D) hab (coordinateMap D a i ha x)

private theorem path_read_at_same_level (B : RootedBlockDiagram.{u}) (a b : ℕ)
    (hab : a ≤ b) (h : b = a) (x : Cell (B.Row b)) :
    (B.path a b hab).read x = some (h ▸ x) := by
  subst b
  rw [path_self, Refinement.read_identity]

/-- A coordinate which keeps its depth retains its diagonal entries when other
coordinates are activated. -/
private theorem coordinateImageAt_diagonal (a b : Level ι) (hab : a ≤ b) (i : ι)
    (ha : ∀ j ≠ i, a j = 0) (n : ℕ) (hna : a i = n) (hnb : b i = n)
    (x : Blocks ((D i).Row n)) (c : TensorColor D b) (r : TensorRow D b c) :
    let z := localCell D i b n hnb ⟨c, r, r⟩
    coordinateImageAt D a b hab i ha n hna x c r r = x z.1 z.2.1 z.2.2 := by
  subst n
  let f := tensorRefinement D a b hab
  obtain ⟨⟨k, r'⟩, hr⟩ := (f.rows c).surjective r
  let y : Cell (TensorRow D a) := ⟨f.color c k, r', r'⟩
  have hread : f.read ⟨c, r, r⟩ = some y := by
    rw [← hr]
    exact f.read_same c k r' r'
  have hi := (Refinement.read_pi_iff _ _ y).1 hread i
  have hrow : Refinement.cellCoordinates y i = localCell D i b (a i) hnb ⟨c, r, r⟩ :=
    (Option.some.inj ((path_read_at_same_level (D i) (a i) (b i) (hab i) hnb _).symm.trans hi)).symm
  change f.hom (coordinateMap D a i ha x) c r r = _
  rw [f.hom_entry (coordinateMap D a i ha x) ⟨c, r, r⟩, hread]
  change coordinateMap D a i ha x y.1 y.2.1 y.2.2 = _
  rw [coordinateMap_entry]
  exact congrArg (fun z : Cell ((D i).Row (a i)) => x z.1 z.2.1 z.2.2) hrow

private def testRows (i j : ι) (b : Level ι) (hbi : b i = 1) (hbj : b j = 1)
    (x : Σ c : (D i).Color 1, (D i).Row 1 c)
    (y : Σ c : (D j).Color 1, (D j).Row 1 c)
    (k : ι) : Σ c : (D k).Color (b k), (D k).Row (b k) c := by
  classical
  refine if hk : k = i then hk.symm ▸ (hbi.symm ▸ x) else
    if hk' : k = j then hk'.symm ▸ (hbj.symm ▸ y) else ?_
  let c : (D k).Color (b k) := Classical.choice inferInstance
  exact ⟨c, Classical.choice inferInstance⟩

private def asDiagonal {C : Type u} {P : C → Type u} (x : Σ c, P c) : Cell P :=
  ⟨x.1, x.2, x.2⟩

private theorem diagonal_roundtrip (B : RootedBlockDiagram.{u}) (n m : ℕ) (h : n = m)
    (x : Σ c : B.Color m, B.Row m c) :
    (h ▸ asDiagonal (h.symm ▸ x) : Cell (B.Row m)) = asDiagonal x := by
  subst m
  rfl

/-- Rank-one projections in distinct coordinates are uniformly separated
when the tested blocks in those coordinates have two distinct rows. -/
theorem coordinate_projections_separated {J : Type u} (e : J ↪ ι)
    (c : ∀ i, (D (e i)).Color 1) (r s : ∀ i, (D (e i)).Row 1 (c i))
    (hrs : ∀ i, r i ≠ s i) :
    ∀ i j, i ≠ j →
      1 ≤ ‖coordinateEmbedding D (e i) 1 (rankOne _ (c i) (r i)) -
        coordinateEmbedding D (e j) 1 (rankOne _ (c j) (r j))‖ := by
  classical
  intro i j hij
  have hn : e i ≠ e j := fun h => hij (e.injective h)
  let a := levelAt (e i) 1
  let a' := levelAt (e j) 1
  let b := a ⊔ a'
  have hbi : b (e i) = 1 := by
    change max (a (e i)) (a' (e i)) = 1
    rw [levelAt_self, levelAt_other _ _ _ hn]
    decide
  have hbj : b (e j) = 1 := by
    change max (a (e j)) (a' (e j)) = 1
    rw [levelAt_other _ _ _ hn.symm, levelAt_self]
    decide
  let x := rankOne ((D (e i)).Row 1) (c i) (r i)
  let y := rankOne ((D (e j)).Row 1) (c j) (r j)
  let hx := fun k hk => levelAt_other (e i) k 1 hk
  let hy := fun k hk => levelAt_other (e j) k 1 hk
  let X := coordinateImageAt D a b le_sup_left (e i) hx 1 (levelAt_self (e i) 1) x
  let Y := coordinateImageAt D a' b le_sup_right (e j) hy 1 (levelAt_self (e j) 1) y
  let rows := testRows D (e i) (e j) b hbi hbj ⟨c i, r i⟩ ⟨c j, s j⟩
  let d : TensorColor D b := fun k => (rows k).1
  let u : TensorRow D b d := fun k => (rows k).2
  have hri : rows (e i) = hbi.symm ▸ (⟨c i, r i⟩ : Σ c : (D (e i)).Color 1, (D (e i)).Row 1 c) := by
    unfold rows testRows
    rw [dif_pos rfl]
  have hrj : rows (e j) = hbj.symm ▸ (⟨c j, s j⟩ : Σ c : (D (e j)).Color 1, (D (e j)).Row 1 c) := by
    unfold rows testRows
    rw [dif_neg hn.symm, dif_pos rfl]
  have hxi : X d u u = 1 := by
    change coordinateImageAt D a b le_sup_left (e i) hx 1 (levelAt_self (e i) 1) x d u u = 1
    rw [coordinateImageAt_diagonal D a b le_sup_left (e i) hx 1 (levelAt_self (e i) 1) hbi x d u]
    have hh : localCell D (e i) b 1 hbi ⟨d, u, u⟩ = ⟨c i, r i, r i⟩ := by
      change (hbi ▸ asDiagonal (rows (e i))) = _
      rw [hri]
      exact diagonal_roundtrip (D (e i)) (b (e i)) 1 hbi _
    rw [hh]
    simp [x, rankOne]
  have hyj : Y d u u = 0 := by
    change coordinateImageAt D a' b le_sup_right (e j) hy 1 (levelAt_self (e j) 1) y d u u = 0
    rw [coordinateImageAt_diagonal D a' b le_sup_right (e j) hy 1 (levelAt_self (e j) 1) hbj y d u]
    have hh : localCell D (e j) b 1 hbj ⟨d, u, u⟩ = ⟨c j, s j, s j⟩ := by
      change (hbj ▸ asDiagonal (rows (e j))) = _
      rw [hrj]
      exact diagonal_roundtrip (D (e j)) (b (e j)) 1 hbj _
    rw [hh]
    simp [y, rankOne, Matrix.single, hrs j]
  have hX := completed_coordinateImageAt D a b le_sup_left (e i) hx 1 (levelAt_self (e i) 1) x
  have hY := completed_coordinateImageAt D a' b le_sup_right (e j) hy 1 (levelAt_self (e j) 1) y
  change 1 ≤ ‖coordinateInclusionAt D a (e i) hx 1 (levelAt_self (e i) 1) x -
    coordinateInclusionAt D a' (e j) hy 1 (levelAt_self (e j) 1) y‖
  rw [← hX, ← hY, ← map_sub, completedEmbedding_norm]
  have hv : ((X - Y) d) u u = 1 := by
    change X d u u - Y d u u = 1
    rw [hxi, hyj, sub_zero]
  have he := (TraceWeightRefinement.matrix_entry_norm_le ((X-Y) d) u u).trans
    (norm_le_pi_norm (X-Y) d)
  rwa [hv, norm_one] at he

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
