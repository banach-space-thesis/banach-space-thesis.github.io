import BanachIsometric.RawSingularChains

/-! Actual Alexander--Whitney interval, front and back simplex embeddings.
All maps act on the literal real standard simplices by barycentric
pushforward. The face identities are proved on their genuine vertex maps. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped Topology

def intervalVertex (s d n : ℕ) (h : s + d ≤ n) : Fin (d + 1) → Fin (n + 1) :=
  fun i => ⟨s + i.val, by omega⟩

theorem intervalVertex_strictMono (s d n : ℕ) (h : s + d ≤ n) :
    StrictMono (intervalVertex s d n h) := by
  intro i j hij
  change s + i.val < s + j.val
  exact Nat.add_lt_add_left hij s

def intervalEmbedding (s d n : ℕ) (h : s + d ≤ n) : Fin (d + 1) ↪o Fin (n + 1) where
  toFun := intervalVertex s d n h
  inj' := (intervalVertex_strictMono s d n h).injective
  map_rel_iff' := by
    intro i j
    change s + i.val ≤ s + j.val ↔ i.val ≤ j.val
    omega

def intervalSimplex (s d n : ℕ) (h : s + d ≤ n) : C(Simplex d, Simplex n) :=
  simplexMap (intervalVertex s d n h)

def frontSimplex (d n : ℕ) (h : d ≤ n) : C(Simplex d, Simplex n) :=
  intervalSimplex 0 d n (by omega)

def backSimplex (s d n : ℕ) (h : s + d = n) : C(Simplex d, Simplex n) :=
  intervalSimplex s d n h.le

def intervalFaceIndex {s d n : ℕ} (h : s + d ≤ n) (i : Fin (d + 2)) : Fin (n + 2) :=
  ⟨s + i.val, by omega⟩

theorem intervalVertex_face {s d n : ℕ} (h : s + d ≤ n) (i : Fin (d + 2)) :
    intervalVertex s (d + 1) (n + 1) (by omega) ∘ i.succAbove =
      (intervalFaceIndex h i).succAbove ∘ intervalVertex s d n h := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, intervalVertex, intervalFaceIndex, Fin.succAbove,
    Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
  split_ifs <;> simp_all <;> omega

theorem intervalSimplex_face {s d n : ℕ} (h : s + d ≤ n) (i : Fin (d + 2)) :
    (intervalSimplex s (d + 1) (n + 1) (by omega)).comp (face i) =
      (face (intervalFaceIndex h i)).comp (intervalSimplex s d n h) := by
  change (simplexMap _).comp (simplexMap _) = (simplexMap _).comp (simplexMap _)
  rw [simplexMap_comp, simplexMap_comp, intervalVertex_face h i]

theorem face_intervalSimplex_before {s d n : ℕ} (h : s + d ≤ n)
    (i : Fin (n + 2)) (hi : i.val ≤ s) :
    (face i).comp (intervalSimplex s d n h) =
      intervalSimplex (s + 1) d (n + 1) (by omega) := by
  change (simplexMap _).comp (simplexMap _) = simplexMap _
  rw [simplexMap_comp]
  congr 1
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, intervalVertex, Fin.succAbove,
    Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
  split_ifs <;> simp_all <;> omega

theorem face_intervalSimplex_after {s d n : ℕ} (h : s + d ≤ n)
    (i : Fin (n + 2)) (hi : s + d < i.val) :
    (face i).comp (intervalSimplex s d n h) = intervalSimplex s d (n + 1) (by omega) := by
  change (simplexMap _).comp (simplexMap _) = simplexMap _
  rw [simplexMap_comp]
  congr 1
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, intervalVertex, Fin.succAbove,
    Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
  split_ifs <;> simp_all
  omega

theorem intervalSimplex_face_zero {s d n : ℕ} (h : s + (d + 1) ≤ n) :
    (intervalSimplex s (d + 1) n h).comp (face (0 : Fin (d + 2))) =
      intervalSimplex (s + 1) d n (by omega) := by
  change (simplexMap _).comp (simplexMap _) = simplexMap _
  rw [simplexMap_comp]
  congr 1
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, intervalVertex, Fin.succAbove, Fin.val_zero,
    Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
  split_ifs <;> simp_all
  omega

theorem intervalSimplex_face_last {s d n : ℕ} (h : s + (d + 1) ≤ n) :
    (intervalSimplex s (d + 1) n h).comp (face (Fin.last (d + 1))) =
      intervalSimplex s d n (by omega) := by
  change (simplexMap _).comp (simplexMap _) = simplexMap _
  rw [simplexMap_comp]
  congr 1
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, intervalVertex, Fin.succAbove, Fin.val_last,
    Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
  split_ifs <;> simp_all

theorem intervalSimplex_comp {a d n b e : ℕ} (h : a + d ≤ n) (h' : b + e ≤ d) :
    (intervalSimplex a d n h).comp (intervalSimplex b e d h') =
      intervalSimplex (a + b) e n (by omega) := by
  change (simplexMap _).comp (simplexMap _) = simplexMap _
  rw [simplexMap_comp]
  congr 1
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, intervalVertex]
  omega

end BanachIsometric.SingularAW
