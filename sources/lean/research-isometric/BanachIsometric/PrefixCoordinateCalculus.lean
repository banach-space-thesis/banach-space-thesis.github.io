import BanachIsometric.PiolaIdentity

/-! # Actual coordinate-prefix calculus and its block determinant -/

namespace BanachIsometric

open scoped Topology

noncomputable section

def prefixCoordinateEquiv (n : ℕ) : PiolaSpace (n + 1) ≃ₗ[ℝ] ℝ × PiolaSpace n where
  toFun z := (z 0, fun i => z i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv z := by funext i; induction i using Fin.cases <;> rfl
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def prefixBlockLinear {n : ℕ} (L : PiolaSpace n →ₗ[ℝ] PiolaSpace n) :
    PiolaSpace (n + 1) →ₗ[ℝ] PiolaSpace (n + 1) where
  toFun z := Fin.cons (z 0) (L (fun i => z i.succ))
  map_add' x y := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      change L ((fun i => x i.succ) + (fun i => y i.succ)) j =
        (L (fun i => x i.succ) + L (fun i => y i.succ)) j
      rw [map_add]
  map_smul' a x := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      change L (a • (fun i => x i.succ)) j = (a • L (fun i => x i.succ)) j
      rw [map_smul]

theorem det_prefixBlockLinear {n : ℕ} (L : PiolaSpace n →ₗ[ℝ] PiolaSpace n) :
    (prefixBlockLinear L).det = L.det := by
  have hconj : (prefixCoordinateEquiv n).conj (prefixBlockLinear L) = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap L := by
    ext p i <;> rfl
  have hd := LinearMap.det_conj (prefixBlockLinear L) (prefixCoordinateEquiv n)
  change ((prefixCoordinateEquiv n).conj (prefixBlockLinear L)).det = _ at hd
  rw [hconj, LinearMap.det_prodMap, LinearMap.det_id, one_mul] at hd
  exact hd.symm

def prefixBlockCLM {n : ℕ} (L : PiolaSpace n →L[ℝ] PiolaSpace n) :
    PiolaSpace (n + 1) →L[ℝ] PiolaSpace (n + 1) :=
  (prefixBlockLinear L.toLinearMap).toContinuousLinearMap

@[simp] theorem prefixBlockCLM_apply {n : ℕ} (L : PiolaSpace n →L[ℝ] PiolaSpace n)
    (z : PiolaSpace (n + 1)) : prefixBlockCLM L z = Fin.cons (z 0) (L (fun i => z i.succ)) := rfl

theorem det_prefixBlockCLM {n : ℕ} (L : PiolaSpace n →L[ℝ] PiolaSpace n) :
    (prefixBlockCLM L).det = L.det := det_prefixBlockLinear L.toLinearMap

def prefixTail (n : ℕ) : PiolaSpace (n + 1) →L[ℝ] PiolaSpace n :=
  ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj i.succ)

def prefixMap {n : ℕ} (Q : PiolaSpace n → PiolaSpace n) (z : PiolaSpace (n + 1)) :
    PiolaSpace (n + 1) := Fin.cons (z 0) (Q (prefixTail n z))

theorem hasFDerivAt_prefixMap {n : ℕ} {Q : PiolaSpace n → PiolaSpace n}
    {D : PiolaSpace n →L[ℝ] PiolaSpace n} {x : PiolaSpace n}
    (hQ : HasFDerivAt Q D x) (ρ : ℝ) :
    HasFDerivAt (prefixMap Q) (prefixBlockCLM D) (Fin.cons ρ x) := by
  have hx : prefixTail n (Fin.cons ρ x) = x := rfl
  have hcomp : HasFDerivAt (fun z => Q (prefixTail n z)) (D.comp (prefixTail n)) (Fin.cons ρ x) := by
    exact (hx ▸ hQ).comp _ (prefixTail n).hasFDerivAt
  apply hasFDerivAt_pi''
  intro i
  induction i using Fin.cases with
  | zero =>
      have hD : (ContinuousLinearMap.proj (0 : Fin (n + 1))).comp (prefixBlockCLM D) =
          (ContinuousLinearMap.proj 0 : PiolaSpace (n + 1) →L[ℝ] ℝ) := by ext v; rfl
      simpa only [prefixMap, Fin.cons_zero, hD] using
        (ContinuousLinearMap.proj (0 : Fin (n + 1)) : PiolaSpace (n + 1) →L[ℝ] ℝ).hasFDerivAt
  | succ j =>
      have hD : (ContinuousLinearMap.proj j.succ).comp (prefixBlockCLM D) =
          (ContinuousLinearMap.proj j).comp (D.comp (prefixTail n)) := by ext v; rfl
      simpa only [prefixMap, Fin.cons_succ, hD] using
        (ContinuousLinearMap.proj j : PiolaSpace n →L[ℝ] ℝ).hasFDerivAt.comp _ hcomp

theorem contDiffAt_prefixMap {n : ℕ} {Q : PiolaSpace n → PiolaSpace n} {x : PiolaSpace n}
    {k : WithTop ℕ∞} (hQ : ContDiffAt ℝ k Q x) (ρ : ℝ) :
    ContDiffAt ℝ k (prefixMap Q) (Fin.cons ρ x) := by
  have hc : ContDiff ℝ k (fun p : ℝ × PiolaSpace n => (Fin.cons p.1 p.2 : PiolaSpace (n + 1))) := by
    apply contDiff_pi.mpr
    intro i
    induction i using Fin.cases with
    | zero => exact contDiff_fst
    | succ j => exact (ContinuousLinearMap.proj j : PiolaSpace n →L[ℝ] ℝ).contDiff.comp contDiff_snd
  exact hc.contDiffAt.comp (Fin.cons ρ x : PiolaSpace (n + 1))
    ((ContinuousLinearMap.proj (0 : Fin (n + 1)) : PiolaSpace (n + 1) →L[ℝ] ℝ).contDiff.contDiffAt.prodMk
      (hQ.comp _ (prefixTail n).contDiff.contDiffAt))

end
end BanachIsometric
