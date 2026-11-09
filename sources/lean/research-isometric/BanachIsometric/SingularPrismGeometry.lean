import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic

/-! Actual affine simplex-prism geometry for singular-chain homotopy.
All spaces are literal standard topological simplices. The maps are defined
by barycentric pushforward and are continuous; no homological invariance or
prism identity is assumed. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology unitInterval

abbrev Simplex (n : ℕ) := stdSimplex ℝ (Fin (n + 1))

def simplexMap {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) : C(Simplex a, Simplex b) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

theorem simplexMap_comp {a b c : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (g : Fin (b + 1) → Fin (c + 1)) :
    (simplexMap g).comp (simplexMap f) = simplexMap (g ∘ f) := by
  apply ContinuousMap.ext
  intro x
  exact stdSimplex.map_comp_apply f g x

@[simp] theorem simplexMap_id (n : ℕ) : simplexMap (id : Fin (n + 1) → Fin (n + 1)) =
    ContinuousMap.id (Simplex n) := by
  apply ContinuousMap.ext
  intro x
  exact stdSimplex.map_id_apply x

def face {n : ℕ} (j : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) := simplexMap j.succAbove

def upper {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) : Fin 2 :=
  if (i : ℕ) < (j : ℕ) then 1 else 0

def simplexTime : C(Simplex 1, unitInterval) where
  toFun w := ⟨w 1, stdSimplex.zero_le w 1, stdSimplex.le_one w 1⟩
  continuous_toFun := ((continuous_apply 1).comp continuous_subtype_val).subtype_mk _

def prism {n : ℕ} (i : Fin (n + 1)) : C(Simplex (n + 1), unitInterval × Simplex n) :=
  (simplexTime.comp (simplexMap (upper i))).prodMk (simplexMap i.predAbove)

theorem upper_face_before {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : j ≤ i.castSucc) : upper i.succ ∘ j.castSucc.succAbove = upper i := by
  have h' : (j : ℕ) ≤ (i : ℕ) := h
  funext k
  simp only [Function.comp_apply, upper, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem merge_face_before {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : j ≤ i.castSucc) : i.succ.predAbove ∘ j.castSucc.succAbove = j.succAbove ∘ i.predAbove := by
  have h' : (j : ℕ) ≤ (i : ℕ) := h
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ, Fin.dite_val, Fin.ite_val, Fin.coe_pred, Fin.coe_castPred]
  split_ifs <;> simp_all <;> omega

theorem upper_face_after {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : i.castSucc < j) : upper i.castSucc ∘ j.succ.succAbove = upper i := by
  have h' : (i : ℕ) < (j : ℕ) := h
  funext k
  simp only [Function.comp_apply, upper, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem merge_face_after {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : i.castSucc < j) : i.castSucc.predAbove ∘ j.succ.succAbove = j.succAbove ∘ i.predAbove := by
  have h' : (i : ℕ) < (j : ℕ) := h
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ, Fin.dite_val, Fin.ite_val, Fin.coe_pred, Fin.coe_castPred]
  split_ifs <;> simp_all <;> omega

theorem upper_middle {n : ℕ} (i : Fin (n + 1)) :
    upper i.castSucc ∘ i.succ.castSucc.succAbove =
      upper i.succ ∘ i.succ.castSucc.succAbove := by
  funext k
  simp only [Function.comp_apply, upper, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem merge_middle {n : ℕ} (i : Fin (n + 1)) :
    i.castSucc.predAbove ∘ i.succ.castSucc.succAbove =
      i.succ.predAbove ∘ i.succ.castSucc.succAbove := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ, Fin.dite_val, Fin.ite_val, Fin.coe_pred, Fin.coe_castPred]
  split_ifs <;> simp_all <;> omega

end BanachIsometric.SingularPrism
