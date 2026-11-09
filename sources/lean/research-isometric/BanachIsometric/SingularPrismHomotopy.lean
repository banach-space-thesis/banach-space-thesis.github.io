import BanachIsometric.SingularPrismFaces

/-! An actual continuous topological homotopy supplies actual singular prism
simplices with all boundary identifications proved. These are the geometric
identities used by the chain homotopy construction, not homological premises.
-/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

abbrev SingularSimplex (X : Type*) [TopologicalSpace X] (n : ℕ) := C(Simplex n, X)

def homotopyPrism (H : f₀.Homotopy f₁) {n : ℕ} (i : Fin (n + 1))
    (simplex : SingularSimplex X n) : SingularSimplex Y (n + 1) :=
  (H.toContinuousMap.comp ((ContinuousMap.id unitInterval).prodMap simplex)).comp (prism i)

theorem homotopyPrism_face_before (H : f₀.Homotopy f₁) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc)
    (simplex : SingularSimplex X (n + 1)) :
    (homotopyPrism H i.succ simplex).comp (face j.castSucc) =
      homotopyPrism H i (simplex.comp (face j)) := by
  apply ContinuousMap.ext
  intro w
  exact congrArg (fun z : unitInterval × Simplex (n + 1) => H (z.1, simplex z.2))
    (DFunLike.congr_fun (prism_face_before i j h) w)

theorem homotopyPrism_face_after (H : f₀.Homotopy f₁) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j)
    (simplex : SingularSimplex X (n + 1)) :
    (homotopyPrism H i.castSucc simplex).comp (face j.succ) =
      homotopyPrism H i (simplex.comp (face j)) := by
  apply ContinuousMap.ext
  intro w
  exact congrArg (fun z : unitInterval × Simplex (n + 1) => H (z.1, simplex z.2))
    (DFunLike.congr_fun (prism_face_after i j h) w)

theorem homotopyPrism_face_middle (H : f₀.Homotopy f₁) {n : ℕ}
    (i : Fin (n + 1)) (simplex : SingularSimplex X (n + 1)) :
    (homotopyPrism H i.castSucc simplex).comp (face i.succ.castSucc) =
      (homotopyPrism H i.succ simplex).comp (face i.succ.castSucc) := by
  apply ContinuousMap.ext
  intro w
  exact congrArg (fun z : unitInterval × Simplex (n + 1) => H (z.1, simplex z.2))
    (DFunLike.congr_fun (prism_face_middle i) w)

theorem homotopyPrism_face_top (H : f₀.Homotopy f₁) (n : ℕ)
    (simplex : SingularSimplex X n) :
    (homotopyPrism H (0 : Fin (n + 1)) simplex).comp (face (0 : Fin (n + 2))) = f₁.comp simplex := by
  apply ContinuousMap.ext
  intro w
  have h := congrArg (fun z : unitInterval × Simplex n => H (z.1, simplex z.2))
    (DFunLike.congr_fun (prism_face_top n) w)
  exact h.trans (H.apply_one (simplex w))

theorem homotopyPrism_face_bottom (H : f₀.Homotopy f₁) (n : ℕ)
    (simplex : SingularSimplex X n) :
    (homotopyPrism H (Fin.last n) simplex).comp (face (Fin.last (n + 1))) = f₀.comp simplex := by
  apply ContinuousMap.ext
  intro w
  have h := congrArg (fun z : unitInterval × Simplex n => H (z.1, simplex z.2))
    (DFunLike.congr_fun (prism_face_bottom n) w)
  exact h.trans (H.apply_zero (simplex w))

end BanachIsometric.SingularPrism
