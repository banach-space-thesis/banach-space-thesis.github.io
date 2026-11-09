import BanachIsometric.CanonicalHemisphereConeFibers
import BanachIsometric.CanonicalHemisphereCoverage
import BanachIsometric.SignedConeInteriorCoordinates

/-! An actual interior facet hit is a singleton cone fiber and its signed
count is the alternating sign of its vertex, with the signed pole factor. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {p : V → ℝ}

theorem canonicalHemisphereConedFacet_count_zero_of_missed_direction
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1))
    (v pole : sphere (0 : V) 1) (hSide : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1)
    (q : sphere (0 : V) 1) (hq : ∀ b, (canonicalHemisphereFacet v pole n hdim i b).val ≠ q) :
    signedSimplexCount (n + 3) (canonicalHemisphereConedFacet hp hcont v pole n hdim i)
      (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)) = 0 := by
  let F := canonicalHemisphereConedExtension hp hcont v pole n hdim i
  let y := canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)
  change (signedFiberCount F (fderiv ℝ F) (signedSimplexDomain (n + 3)) y : ℝ) = 0
  rw [signedFiberCount_eq_zero_of_not_mem_image, Int.cast_zero]
  rintro ⟨x, hx, hFx⟩
  obtain ⟨b, hb, _⟩ := (canonicalHemisphereConedExtension_hit_iff hp hcont hSphere
    v pole hSide n hdim i r hr hr₁ q x).mp ⟨hx, hFx⟩
  exact hq b hb

theorem canonicalHemisphereConedFacet_count_of_interior_direction
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1))
    (v pole : sphere (0 : V) 1) (hSide : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hPole : pole.val = ε • v.val)
    (i : Fin (n + 3)) (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (q : sphere (0 : V) 1)
    (b : Simplex (n + 2)) (hb : (canonicalHemisphereFacet v pole n hdim i b).val = q) (hbPos : ∀ j, 0 < b j)
    (hDiff : DifferentiableAt ℝ (canonicalHemisphereConedExtension hp hcont v pole n hdim i) (r • b.val)) :
    signedSimplexCount (n + 3) (canonicalHemisphereConedFacet hp hcont v pole n hdim i)
      (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)) = ε * (-1 : ℝ) ^ (i : ℕ) := by
  let F := canonicalHemisphereConedExtension hp hcont v pole n hdim i
  let y := canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)
  let x₀ : Fin (n + 3) → ℝ := r • b.val
  have hUniq := (canonicalHemisphereFacet_unique_of_interior v pole hSide n hdim i b hbPos).2
  have hset : {x : Fin (n + 3) → ℝ | x ∈ signedSimplexDomain (n + 3) ∧ F x = y} = {x₀} := by
    ext x
    rw [mem_singleton_iff]
    change x ∈ signedSimplexDomain (n + 3) ∧ canonicalHemisphereConedExtension hp hcont v pole n hdim i x =
      canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val) ↔ x = x₀
    rw [canonicalHemisphereConedExtension_hit_iff hp hcont hSphere v pole hSide n hdim i r hr hr₁.le q x]
    constructor
    · rintro ⟨b', hb', hx⟩
      have h := hUniq (i, b') (Subtype.ext (hb'.trans hb.symm))
      have hEq : b' = b := congrArg Prod.snd h
      rw [hEq] at hx
      exact hx
    · intro hx
      exact ⟨b, hb, hx⟩
  let u : Fin (n + 3) → ℝ := Fin.cons r (signedSimplexDrop (n + 2) b)
  have hu : signedConeSourceChart (n + 2) u = x₀ := by
    rw [signedConeSourceChart_apply]
    change r • signedSimplexBarycentric (n + 2) (signedSimplexDrop (n + 2) b) = _
    rw [signedSimplexBarycentric_drop]
  have huBase : signedTailLinear (n + 2) u ∈ interior (signedSimplexDomain (n + 2)) :=
    signedSimplexDrop_mem_interior_of_positive (n + 2) b hbPos
  have hDiff' : DifferentiableAt ℝ F (signedConeSourceChart (n + 2) u) := by rw [hu]; exact hDiff
  have hε' : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  obtain ⟨c, hc, hdet⟩ := canonicalHemisphereCone_fderiv_det hp hcont v pole hSide n hdim ε hε' hPole i
    (F := F) (u := u) hr hr₁ huBase hDiff' (canonicalHemisphereConedExtension_apply hp hcont hSphere v pole hSide n hdim i)
  rw [hu] at hdet
  have hfin : {x : Fin (n + 3) → ℝ | x ∈ signedSimplexDomain (n + 3) ∧ F x = y}.Finite :=
    hset.symm ▸ finite_singleton x₀
  change (signedFiberCount F (fderiv ℝ F) (signedSimplexDomain (n + 3)) y : ℝ) = _
  rw [← signedFiberSum_eq_coe_signedFiberCount _ _ _ _ hfin]
  change (∑' z : {x : Fin (n + 3) → ℝ | x ∈ signedSimplexDomain (n + 3) ∧ F x = y},
      jacobianOrientation (fderiv ℝ F) z.val) = _
  rw [hset, tsum_singleton, ← Int.cast_negOnePow_natCast ℝ i.val]
  rcases hε with rfl | rfl <;> rcases Int.units_eq_one_or (Int.negOnePow (i.val : ℤ)) with hs | hs <;>
    simp [jacobianOrientation, hdet, hs, hc]

end BanachIsometric.SingularPrism
