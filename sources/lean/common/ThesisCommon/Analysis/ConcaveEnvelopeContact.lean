import ThesisCommon.Analysis.RegularizedProfileBarriers

/-! A contact criterion for the concrete concave envelope. A concave
majorant that touches the original function pins down the envelope value.
The localized version separates central-interval and exterior barriers,
as in the tangent argument for Gowers--Maurey's interpolation gaps. -/
noncomputable section
namespace ThesisCommon

theorem positiveConcaveEnvelope_eq_of_contact {H T : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x)
    (hT : ConcaveOn ℝ (Set.Ici 0) T) (hHT : ∀ x, 0 ≤ x → H x ≤ T x)
    {x : ℝ} (hx : 0 ≤ x) (heq : T x = H x) :
    positiveConcaveEnvelope H x = H x :=
  le_antisymm ((positiveConcaveEnvelope_le_of_concave hH0 hT hHT hx).trans_eq heq)
    (le_positiveConcaveEnvelope hH0 hH1 hx)

theorem positiveConcaveEnvelope_eq_of_local_barriers {H F U T : ℝ → ℝ} {I : Set ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x)
    (hT : ConcaveOn ℝ (Set.Ici 0) T)
    (hHU : ∀ x, 0 ≤ x → H x ≤ U x)
    (hHF : ∀ x, 0 ≤ x → x ∈ I → H x = F x)
    (hFT : ∀ x, 0 ≤ x → x ∈ I → F x ≤ T x)
    (hUT : ∀ x, 0 ≤ x → x ∉ I → U x ≤ T x)
    {x : ℝ} (hx : 0 ≤ x) (hxI : x ∈ I) (heq : T x = F x) :
    positiveConcaveEnvelope H x = F x := by
  have hHT : ∀ t, 0 ≤ t → H t ≤ T t := by
    intro t ht
    by_cases htI : t ∈ I
    · rw [hHF t ht htI]
      exact hFT t ht htI
    · exact (hHU t ht).trans (hUT t ht htI)
  rw [positiveConcaveEnvelope_eq_of_contact hH0 hH1 hT hHT hx
    (heq.trans (hHF x hx hxI).symm)]
  exact hHF x hx hxI

theorem submultiplicativeHull_eq_of_factorization_bound {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) {x : ℝ} (hx : 1 ≤ x)
    (hcost : ∀ l : List ℝ, (∀ t ∈ l, 1 ≤ t) → x ≤ l.prod → φ x ≤ (l.map φ).prod) :
    submultiplicativeHull φ x = φ x := by
  apply le_antisymm (submultiplicativeHull_le hφ hx)
  apply le_csInf (factorizationCosts_nonempty φ x)
  rintro a ⟨l, hl, hxl, rfl⟩
  exact hcost l hl hxl

end ThesisCommon
