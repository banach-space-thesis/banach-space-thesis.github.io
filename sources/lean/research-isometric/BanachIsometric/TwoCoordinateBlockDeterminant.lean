import BanachIsometric.PiolaIdentity

/-! Actual determinant of a first-two-coordinate block with scalar tail,
proved by conjugating with an explicit linear coordinate splitting. -/

namespace BanachIsometric

open scoped Matrix

noncomputable section

def prefixTwoCoordinateEquiv (n : ℕ) : PiolaSpace (n + 2) ≃ₗ[ℝ] PiolaSpace 2 × PiolaSpace n where
  toFun z := (![z 0, z (0 : Fin (n + 1)).succ], fun j => z j.succ.succ)
  invFun p := Fin.cons (p.1 0) (Fin.cons (p.1 1) p.2)
  left_inv z := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' x y := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

def prefixTwoBlockLinear (n : ℕ) (a b c d k : ℝ) : PiolaSpace (n + 2) →ₗ[ℝ] PiolaSpace (n + 2) where
  toFun z := Fin.cons (a * z 0 + b * z (0 : Fin (n + 1)).succ)
    (Fin.cons (c * z 0 + d * z (0 : Fin (n + 1)).succ) (fun j => k * z j.succ.succ))
  map_add' x y := by
    funext i
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero, Pi.add_apply]; ring
    | succ i =>
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_succ, Fin.cons_zero, Pi.add_apply]; ring
      | succ i => simp only [Fin.cons_succ, Pi.add_apply]; ring
  map_smul' r x := by
    funext i
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    | succ i =>
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_succ, Fin.cons_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
      | succ i => simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem prefixTwoCoordinate_conj_block (n : ℕ) (a b c d k : ℝ) :
    (prefixTwoCoordinateEquiv n).conj (prefixTwoBlockLinear n a b c d k) =
      (Matrix.toLin' (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ)).prodMap
        (k • (LinearMap.id : PiolaSpace n →ₗ[ℝ] PiolaSpace n)) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [prefixTwoCoordinateEquiv, prefixTwoBlockLinear, LinearEquiv.conj_apply,
        Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
  · funext j
    simp [prefixTwoCoordinateEquiv, prefixTwoBlockLinear, LinearEquiv.conj_apply]

theorem det_prefixTwoBlockLinear (n : ℕ) (a b c d k : ℝ) :
    (prefixTwoBlockLinear n a b c d k).det = (a * d - b * c) * k ^ n := by
  have h := LinearMap.det_conj (prefixTwoBlockLinear n a b c d k) (prefixTwoCoordinateEquiv n)
  change ((prefixTwoCoordinateEquiv n).conj (prefixTwoBlockLinear n a b c d k)).det = _ at h
  rw [prefixTwoCoordinate_conj_block, LinearMap.det_prodMap, LinearMap.det_toLin',
    LinearMap.det_smul, LinearMap.det_id, mul_one, Matrix.det_fin_two] at h
  simpa only [PiolaSpace, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h.symm

end

end BanachIsometric
