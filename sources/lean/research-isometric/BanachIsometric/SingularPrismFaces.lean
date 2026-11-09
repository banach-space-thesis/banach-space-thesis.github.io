import BanachIsometric.SingularPrismGeometry

/-! Literal boundary identifications of the actual affine prism maps. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology unitInterval

def cylinderFace {n : ℕ} (j : Fin (n + 2)) :
    C(unitInterval × Simplex n, unitInterval × Simplex (n + 1)) :=
  (ContinuousMap.id unitInterval).prodMap (face j)

theorem prism_face_before {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : j ≤ i.castSucc) :
    (prism i.succ).comp (face j.castSucc) = (cylinderFace j).comp (prism i) := by
  apply ContinuousMap.ext
  intro w
  apply Prod.ext
  · apply Subtype.ext
    change (stdSimplex.map (upper i.succ) (stdSimplex.map j.castSucc.succAbove w)) 1 =
      (stdSimplex.map (upper i) w) 1
    rw [stdSimplex.map_comp_apply, upper_face_before i j h]
  · change stdSimplex.map i.succ.predAbove (stdSimplex.map j.castSucc.succAbove w) =
      stdSimplex.map j.succAbove (stdSimplex.map i.predAbove w)
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, merge_face_before i j h]

theorem prism_face_after {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : i.castSucc < j) :
    (prism i.castSucc).comp (face j.succ) = (cylinderFace j).comp (prism i) := by
  apply ContinuousMap.ext
  intro w
  apply Prod.ext
  · apply Subtype.ext
    change (stdSimplex.map (upper i.castSucc) (stdSimplex.map j.succ.succAbove w)) 1 =
      (stdSimplex.map (upper i) w) 1
    rw [stdSimplex.map_comp_apply, upper_face_after i j h]
  · change stdSimplex.map i.castSucc.predAbove (stdSimplex.map j.succ.succAbove w) =
      stdSimplex.map j.succAbove (stdSimplex.map i.predAbove w)
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, merge_face_after i j h]

theorem prism_face_middle {n : ℕ} (i : Fin (n + 1)) :
    (prism i.castSucc).comp (face i.succ.castSucc) =
      (prism i.succ).comp (face i.succ.castSucc) := by
  apply ContinuousMap.ext
  intro w
  apply Prod.ext
  · apply Subtype.ext
    change (stdSimplex.map (upper i.castSucc) (stdSimplex.map i.succ.castSucc.succAbove w)) 1 =
      (stdSimplex.map (upper i.succ) (stdSimplex.map i.succ.castSucc.succAbove w)) 1
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, upper_middle]
  · change stdSimplex.map i.castSucc.predAbove (stdSimplex.map i.succ.castSucc.succAbove w) =
      stdSimplex.map i.succ.predAbove (stdSimplex.map i.succ.castSucc.succAbove w)
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, merge_middle]

theorem upper_zero_face_zero (n : ℕ) :
    upper (0 : Fin (n + 1)) ∘ (0 : Fin (n + 2)).succAbove = fun _ => (1 : Fin 2) := by
  funext k
  simp [upper]

theorem merge_zero_face_zero (n : ℕ) :
    (0 : Fin (n + 1)).predAbove ∘ (0 : Fin (n + 2)).succAbove = id := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ, Fin.dite_val, Fin.ite_val, Fin.coe_pred, Fin.coe_castPred]
  split_ifs <;> simp_all

theorem upper_last_face_last (n : ℕ) :
    upper (Fin.last n) ∘ (Fin.last (n + 1)).succAbove = fun _ => (0 : Fin 2) := by
  funext k
  simp only [Function.comp_apply, upper, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_last]
  (split_ifs <;> simp_all)
  omega

theorem merge_last_face_last (n : ℕ) :
    (Fin.last n).predAbove ∘ (Fin.last (n + 1)).succAbove = id := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val,
    Fin.coe_castSucc, Fin.val_succ, Fin.dite_val, Fin.ite_val, Fin.coe_pred, Fin.coe_castPred,
    Fin.val_last]
  (split_ifs <;> simp_all)
  omega

theorem simplexTime_map_one (n : ℕ) (w : Simplex n) :
    simplexTime (stdSimplex.map (fun _ : Fin (n + 1) => (1 : Fin 2)) w) = 1 := by
  apply Subtype.ext
  change FunOnFinite.linearMap ℝ ℝ (fun _ : Fin (n + 1) => (1 : Fin 2)) (w : Fin (n + 1) → ℝ) 1 = 1
  rw [FunOnFinite.linearMap_apply_apply]
  simp

theorem simplexTime_map_zero (n : ℕ) (w : Simplex n) :
    simplexTime (stdSimplex.map (fun _ : Fin (n + 1) => (0 : Fin 2)) w) = 0 := by
  apply Subtype.ext
  change FunOnFinite.linearMap ℝ ℝ (fun _ : Fin (n + 1) => (0 : Fin 2)) (w : Fin (n + 1) → ℝ) 1 = 0
  rw [FunOnFinite.linearMap_apply_apply]
  norm_num

theorem prism_face_top (n : ℕ) :
    (prism (0 : Fin (n + 1))).comp (face (0 : Fin (n + 2))) =
      (ContinuousMap.const (Simplex n) (1 : unitInterval)).prodMk (ContinuousMap.id (Simplex n)) := by
  apply ContinuousMap.ext
  intro w
  apply Prod.ext
  · change simplexTime (stdSimplex.map (upper (0 : Fin (n + 1)))
      (stdSimplex.map (0 : Fin (n + 2)).succAbove w)) = 1
    rw [stdSimplex.map_comp_apply, upper_zero_face_zero, simplexTime_map_one]
  · change stdSimplex.map (0 : Fin (n + 1)).predAbove
      (stdSimplex.map (0 : Fin (n + 2)).succAbove w) = w
    rw [stdSimplex.map_comp_apply, merge_zero_face_zero, stdSimplex.map_id_apply]

theorem prism_face_bottom (n : ℕ) :
    (prism (Fin.last n)).comp (face (Fin.last (n + 1))) =
      (ContinuousMap.const (Simplex n) (0 : unitInterval)).prodMk (ContinuousMap.id (Simplex n)) := by
  apply ContinuousMap.ext
  intro w
  apply Prod.ext
  · change simplexTime (stdSimplex.map (upper (Fin.last n))
      (stdSimplex.map (Fin.last (n + 1)).succAbove w)) = 0
    rw [stdSimplex.map_comp_apply, upper_last_face_last, simplexTime_map_zero]
  · change stdSimplex.map (Fin.last n).predAbove
      (stdSimplex.map (Fin.last (n + 1)).succAbove w) = w
    rw [stdSimplex.map_comp_apply, merge_last_face_last, stdSimplex.map_id_apply]

end BanachIsometric.SingularPrism
