import BanachIsometric.SignedTargetRay
import BanachIsometric.ChartSemiconjugacyDerivative

/-! A positive rescaling of the radial coordinate preserves orientation.
Consequently an actual local ray identity transports the facet determinant
with exactly the alternating sign supplied by the ordered source vertices. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Filter
open scoped Topology

def signedRayTransport (n : ℕ) (a : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (u 0 * a (signedTailLinear n u)) (f (signedTailLinear n u))

theorem signedRayTransport_hasFDerivAt (n : ℕ) {a : (Fin n → ℝ) → ℝ}
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {u : Fin (n + 1) → ℝ}
    {A : (Fin n → ℝ) →L[ℝ] ℝ} {B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (ha : HasFDerivAt a A (signedTailLinear n u)) (hf : HasFDerivAt f B (signedTailLinear n u)) :
    ∃ D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ),
      HasFDerivAt (signedRayTransport n a f) D u ∧
      D.det = a (signedTailLinear n u) * B.det := by
  let Tail := (signedTailLinear n).toContinuousLinearMap
  have ha' := ha.comp u Tail.hasFDerivAt
  have hf' := hf.comp u Tail.hasFDerivAt
  let H := u 0 • (A.comp Tail) + a (signedTailLinear n u) • signedRayHead n
  have hH : HasFDerivAt (fun z => z 0 * a (signedTailLinear n z)) H u :=
    (signedRayHead n).hasFDerivAt.mul ha'
  refine ⟨signedRayJoin n H (B.comp Tail), HasFDerivAt.signedRayJoin hH hf', ?_⟩
  rw [signedRayJoin_det]
  simp [H, Tail, signedTailLinear_single_zero, signedRayHead]

theorem det_of_signedFacetRay_semiconjugacy (n : ℕ) (i : Fin (n + 2))
    {a : (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {u : Fin (n + 1) → ℝ}
    (hr : 0 < u 0) (ha : 0 < a (signedTailLinear n u))
    (hda : DifferentiableAt ℝ a (signedTailLinear n u))
    (hdf : DifferentiableAt ℝ f (signedTailLinear n u))
    (he : ∀ᶠ z in 𝓝 u,
      F (signedFacetRay n i z) = signedTargetRay n (signedRayTransport n a f z)) :
    DifferentiableAt ℝ F (signedFacetRay n i u) ∧
    ∃ c : ℝ, 0 < c ∧ (fderiv ℝ F (signedFacetRay n i u)).det =
      Int.negOnePow (i.val : ℤ) • (c * (fderiv ℝ f (signedTailLinear n u)).det) := by
  let A := signedFacetRayDerivative n i u
  have hA : A.det ≠ 0 := by
    dsimp only [A]
    rw [signedFacetRayDerivative_det]
    rcases Int.units_eq_one_or (Int.negOnePow (i.val : ℤ)) with h | h <;>
      simp [h, (signedFacetCenter_pos n).ne', hr.ne']
  let e := (A.toLinearMap.equivOfDetNeZero hA).toContinuousLinearEquiv
  have heA : (e : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) = A := by
    ext z j
    rfl
  have hS : HasStrictFDerivAt (signedFacetRay n i)
      (e : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) u := by
    rw [heA]
    exact signedFacetRay_hasStrictFDerivAt n i u
  obtain ⟨D, hD, hdetD⟩ := signedRayTransport_hasFDerivAt n hda.hasFDerivAt hdf.hasFDerivAt
  let B := signedTargetRayDerivative n (signedRayTransport n a f u)
  have hB : HasFDerivAt (signedTargetRay n) B (signedRayTransport n a f u) :=
    signedTargetRay_hasFDerivAt n _
  have hBpos : 0 < B.det := by
    rw [signedTargetRayDerivative_det]
    exact pow_pos (mul_pos hr ha) _
  refine ⟨(hasFDerivAt_of_chart_semiconjugacy (A := e) hS hB hD he).differentiableAt,
    B.det * a (signedTailLinear n u) / (signedFacetCenter n * (u 0) ^ n),
    div_pos (mul_pos hBpos ha) (mul_pos (signedFacetCenter_pos n) (pow_pos hr _)), ?_⟩
  rw [det_fderiv_eq_of_chart_semiconjugacy (A := e) hS hB hD he, heA, hdetD,
    signedFacetRayDerivative_det]
  have hc : signedFacetCenter n ≠ 0 := (signedFacetCenter_pos n).ne'
  rcases Int.units_eq_one_or (Int.negOnePow (i.val : ℤ)) with h | h <;>
    simp [h] <;> field_simp [hc, hr.ne']

end BanachIsometric.SingularPrism
