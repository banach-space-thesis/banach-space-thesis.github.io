import BanachIsometric.SignedSimplexFacetRay

/-! A derivative in radius-and-tail coordinates is block triangular when
the tail map is independent of the radius. Its determinant is the radial
derivative times the determinant of the actual tail derivative. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Matrix

def signedRayJoin (n : ℕ) (a : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (b : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (Fin.cons a fun i =>
    (ContinuousLinearMap.proj i).comp b)

@[simp] theorem signedRayJoin_apply_zero (n : ℕ) (a : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (b : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin (n + 1) → ℝ) :
    signedRayJoin n a b x 0 = a x := rfl

@[simp] theorem signedRayJoin_apply_succ (n : ℕ) (a : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (b : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    signedRayJoin n a b x i.succ = b x i := rfl

theorem signedRayJoin_det (n : ℕ) (a : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (signedRayJoin n a (B.comp (signedTailLinear n).toContinuousLinearMap)).det =
      a (Pi.single (0 : Fin (n + 1)) 1) * B.det := by
  let A := signedRayJoin n a (B.comp (signedTailLinear n).toContinuousLinearMap)
  change A.toLinearMap.det = a _ * B.toLinearMap.det
  rw [← LinearMap.det_toMatrix' A.toLinearMap, ← LinearMap.det_toMatrix' B.toLinearMap]
  let M := LinearMap.toMatrix' A.toLinearMap
  have hzero (i : Fin n) : M i.succ 0 = 0 := by
    change A (Pi.single (0 : Fin (n + 1)) 1) i.succ = 0
    simp [A, signedTailLinear_single_zero]
  have hhead : M 0 0 = a (Pi.single (0 : Fin (n + 1)) 1) := rfl
  have hminor : M.submatrix Fin.succ Fin.succ = LinearMap.toMatrix' B.toLinearMap := by
    ext i j
    change A (Pi.single j.succ 1) i.succ = B (Pi.single j 1) i
    simp [A, signedTailLinear_single_succ]
  change M.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hzero, hhead, hminor]

theorem HasFDerivAt.signedRayJoin {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {g : (Fin (n + 1) → ℝ) → (Fin n → ℝ)} {x : Fin (n + 1) → ℝ}
    {a : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {b : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hf : HasFDerivAt f a x) (hg : HasFDerivAt g b x) :
    HasFDerivAt (fun z => Fin.cons (f z) (g z)) (signedRayJoin n a b) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa using ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hg)

end BanachIsometric.SingularPrism
