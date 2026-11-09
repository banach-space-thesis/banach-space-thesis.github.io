import BanachIsometric.PiolaHomotopyIntegral
import BanachIsometric.PiolaBoxFrontier

/-!
# Smooth straight-line homotopy invariance of signed Jacobian integrals

The boundary condition is imposed on the compact union of all coordinate faces
of the spatial box. It is used only to remove the actual lateral cofactor flux.
-/

namespace BanachIsometric

open MeasureTheory Set

def piolaAffineHomotopy {n : ℕ} (f₀ f₁ : PiolaSpace n → PiolaSpace n)
    (z : PiolaSpace (n + 1)) : PiolaSpace n :=
  (1 - z (Fin.last n)) • f₀ (Fin.init z) + z (Fin.last n) • f₁ (Fin.init z)

theorem contDiff_piolaAffineHomotopy {n : ℕ} {f₀ f₁ : PiolaSpace n → PiolaSpace n}
    (hf₀ : ContDiff ℝ 2 f₀) (hf₁ : ContDiff ℝ 2 f₁) :
    ContDiff ℝ 2 (piolaAffineHomotopy f₀ f₁) := by
  have ht : ContDiff ℝ 2 (fun z : PiolaSpace (n + 1) => z (Fin.last n)) :=
    (ContinuousLinearMap.proj (Fin.last n) : PiolaSpace (n + 1) →L[ℝ] ℝ).contDiff
  exact ((contDiff_const.sub ht).smul
    (hf₀.comp (piolaInitLinear n).contDiff)).add
    (ht.smul (hf₁.comp (piolaInitLinear n).contDiff))

@[simp] theorem piolaTimeSlice_affine_zero {n : ℕ}
    (f₀ f₁ : PiolaSpace n → PiolaSpace n) :
    piolaTimeSlice (piolaAffineHomotopy f₀ f₁) 0 = f₀ := by
  funext x
  simp [piolaTimeSlice, piolaAffineHomotopy]

@[simp] theorem piolaTimeSlice_affine_one {n : ℕ}
    (f₀ f₁ : PiolaSpace n → PiolaSpace n) :
    piolaTimeSlice (piolaAffineHomotopy f₀ f₁) 1 = f₁ := by
  funext x
  simp [piolaTimeSlice, piolaAffineHomotopy]

theorem integral_signedJacobian_affine_eq {n : ℕ}
    {f₀ f₁ : PiolaSpace n → PiolaSpace n}
    (hf₀ : ContDiff ℝ 2 f₀) (hf₁ : ContDiff ℝ 2 f₁)
    {ψ : PiolaSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (a b : PiolaSpace n) (hab : a ≤ b)
    (hboundary : ∀ x ∈ piolaBoxBoundary a b, ∀ t : unitInterval,
      ψ ((1 - (t : ℝ)) • f₀ x + (t : ℝ) • f₁ x) = 0) :
    (∫ x in Icc a b, (fderiv ℝ f₀ x).det * ψ (f₀ x)) =
      ∫ x in Icc a b, (fderiv ℝ f₁ x).det * ψ (f₁ x) := by
  let A : PiolaSpace (n + 1) := Fin.snoc a 0
  let B : PiolaSpace (n + 1) := Fin.snoc b 1
  have hAB : A ≤ B := snoc_zero_le_snoc_one hab
  have hlat : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      ∀ z ∈ piolaBoxFace A B i,
        ψ (piolaAffineHomotopy f₀ f₁ (i.insertNth (B i) z)) = 0 ∧
          ψ (piolaAffineHomotopy f₀ f₁ (i.insertNth (A i) z)) = 0 := by
    intro i hi z hz
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    have hside (c : ℝ) (hc : c = A j.castSucc ∨ c = B j.castSucc) :
        ψ (piolaAffineHomotopy f₀ f₁ (j.castSucc.insertNth c z)) = 0 := by
      have hcle : c ∈ Icc (A j.castSucc) (B j.castSucc) := by
        rcases hc with rfl | rfl
        · exact ⟨le_rfl, hAB j.castSucc⟩
        · exact ⟨hAB j.castSucc, le_rfl⟩
      let w : PiolaSpace (n + 1) := j.castSucc.insertNth c z
      have hw : w ∈ Icc A B :=
        Fin.insertNth_mem_Icc.mpr ⟨hcle, hz⟩
      have hx : Fin.init w ∈ piolaBoxBoundary a b := by
        apply mem_piolaBoxBoundary_iff.mpr
        refine ⟨init_mem_Icc_of_mem_snoc_box hw, j, ?_⟩
        simpa only [w, Fin.init_def, Fin.insertNth_apply_same, A, B, Fin.snoc_castSucc] using hc
      let t : unitInterval := ⟨w (Fin.last n),
        last_mem_unitInterval_of_mem_snoc_box hw⟩
      exact hboundary _ hx t
    exact ⟨hside (B j.castSucc) (Or.inr rfl), hside (A j.castSucc) (Or.inl rfl)⟩
  have h := integral_signedJacobian_piolaTimeSlice_eq
    (contDiff_piolaAffineHomotopy hf₀ hf₁) hψ A B hAB hlat
  simpa only [A, B, Fin.init_snoc, Fin.snoc_last,
    piolaTimeSlice_affine_one, piolaTimeSlice_affine_zero] using h.symm

theorem integral_signedJacobian_affine_eq_of_frontier {n : ℕ}
    {f₀ f₁ : PiolaSpace n → PiolaSpace n}
    (hf₀ : ContDiff ℝ 2 f₀) (hf₁ : ContDiff ℝ 2 f₁)
    {ψ : PiolaSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (a b : PiolaSpace n) (hab : a ≤ b)
    (hboundary : ∀ x ∈ frontier (Icc a b), ∀ t : unitInterval,
      ψ ((1 - (t : ℝ)) • f₀ x + (t : ℝ) • f₁ x) = 0) :
    (∫ x in Icc a b, (fderiv ℝ f₀ x).det * ψ (f₀ x)) =
      ∫ x in Icc a b, (fderiv ℝ f₁ x).det * ψ (f₁ x) := by
  apply integral_signedJacobian_affine_eq hf₀ hf₁ hψ a b hab
  simpa only [piolaBoxBoundary_eq_frontier] using hboundary

end BanachIsometric
