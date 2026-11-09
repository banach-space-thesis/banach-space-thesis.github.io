import BanachIsometric.CanonicalHemisphereFacetCount

/-! Every nonzero interior direction with interior preimages has exactly one
oriented cone hit. The two hemispheres contribute the same signed count
after the minus sign in the actual sphere cycle. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric MeasureTheory NormedSpace
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {p : V → ℝ}

private theorem canonicalHemisphere_oriented_count_of_regular_direction
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1))
    (v pole : sphere (0 : V) 1) (hSide : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hPole : pole.val = ε • v.val)
    (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (q : closedHemisphere pole)
    (hreg : ∀ i x, x ∈ signedSimplexDomain (n + 3) → canonicalHemisphereConedExtension hp hcont v pole n hdim i x =
      canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val.val) →
        x ∈ interior (signedSimplexDomain (n + 3)) ∧
        DifferentiableAt ℝ (canonicalHemisphereConedExtension hp hcont v pole n hdim i) x) :
    (∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) * signedSimplexCount (n + 3)
      (canonicalHemisphereConedFacet hp hcont v pole n hdim i) (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val.val))) = ε ∧
    ∀ i : Fin (n + 3), signedSimplexCount (n + 3) (canonicalHemisphereConedFacet hp hcont v (-pole) n hdim i)
      (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val.val)) = 0 := by
  obtain ⟨i, b, hb⟩ := canonicalHemisphereFacet_cover v pole hSide n hdim q
  have hbHit : (canonicalHemisphereFacet v pole n hdim i b).val = q.val := congrArg Subtype.val hb
  let x := r • b.val
  have hx := (canonicalHemisphereConedExtension_hit_iff hp hcont hSphere v pole hSide n hdim i r hr hr₁.le q.val x).mpr ⟨b, hbHit, rfl⟩
  obtain ⟨hxInt, hxDiff⟩ := hreg i x hx.1 hx.2
  have hbPos (j : Fin (n + 3)) : 0 < b j := by
    have h := signedSimplexBarycentric_pos_of_interior (n + 3) hxInt j.succ
    change 0 < r * b j at h
    exact pos_of_mul_pos_right h hr.le
  obtain ⟨hHeight, hUniq⟩ := canonicalHemisphereFacet_unique_of_interior v pole hSide n hdim i b hbPos
  rw [hb] at hHeight
  constructor
  · rw [Finset.sum_eq_single i]
    · rw [canonicalHemisphereConedFacet_count_of_interior_direction hp hcont hSphere
        v pole hSide n hdim ε hε hPole i r hr hr₁ q.val b hbHit hbPos hxDiff]
      calc
        _ = ε * (((-1 : ℝ) * (-1)) ^ (i : ℕ)) := by rw [mul_pow]; ring
        _ = ε := by norm_num
    · intro j _ hji
      rw [canonicalHemisphereConedFacet_count_zero_of_missed_direction hp hcont hSphere v pole hSide n hdim j r hr hr₁.le q.val, mul_zero]
      intro a ha
      have h := hUniq (j, a) (Subtype.ext (ha.trans hbHit.symm))
      exact hji (congrArg Prod.fst h)
    · intro h
      exact (h (Finset.mem_univ i)).elim
  · intro j
    have hOpp : -pole = v ∨ -pole = -v := by
      rcases hSide with h | h
      · rw [h]
        exact Or.inr rfl
      · rw [h, neg_neg]
        exact Or.inl rfl
    apply canonicalHemisphereConedFacet_count_zero_of_missed_direction hp hcont hSphere v (-pole) hOpp n hdim j r hr hr₁.le q.val
    intro a ha
    have hNon := (canonicalHemisphereFacet v (-pole) n hdim j a).property
    change 0 ≤ inner ℝ (-pole.val) (canonicalHemisphereFacet v (-pole) n hdim j a).val.val at hNon
    rw [ha, inner_neg_left] at hNon
    linarith

def canonicalHemisphereCoordinateProjection (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : C(sphere (0 : V) 1, Fin (n + 3) → ℝ) :=
  ⟨fun x => canonicalHemisphereChartCoordinates v n hdim (radialGaugeMap p x.val),
    (canonicalHemisphereChartCoordinates v n hdim).continuous.comp
      ((radialGaugeHomeomorph hp hcont).continuous.comp continuous_subtype_val)⟩

def canonicalGaugeSuspensionConedChain (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : RawRationalChains (Fin (n + 3) → ℝ) (n + 3) :=
  rawLipschitzCone (n + 2) (rawChainMap (canonicalHemisphereCoordinateProjection hp hcont v n hdim)
    (n + 2) (canonicalSuspensionCycle v n hdim).val)

theorem canonicalGaugeSuspensionConedChain_count_eq_sum
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (y : Fin (n + 3) → ℝ) :
    rawSignedSimplexCount (n + 3) (canonicalGaugeSuspensionConedChain hp hcont v n hdim) y =
      (∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) * signedSimplexCount (n + 3)
        (canonicalHemisphereConedFacet hp hcont v v n hdim i) y) -
      ∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) * signedSimplexCount (n + 3)
        (canonicalHemisphereConedFacet hp hcont v (-v) n hdim i) y := by
  have h (pole : sphere (0 : V) 1) (i : Fin (n + 3)) :
      (canonicalHemisphereCoordinateProjection hp hcont v n hdim).comp (canonicalSphereHemisphereFacet v pole n hdim i) =
        canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i := rfl
  have hCoeff (k : ℕ) (f : (Fin (n + 3) → ℝ) → ℝ) :
      ((-1 : ℤ) ^ k • f) y = (-1 : ℝ) ^ k * f y := by
    change (-1 : ℤ) ^ k • f y = _
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  simp only [canonicalGaugeSuspensionConedChain, canonicalSuspensionCycle_val_eq_sum, map_sub, map_sum, map_zsmul,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, h, rawLipschitzCone_single,
    rawSignedSimplexCount_single, one_smul, Pi.sub_apply, Finset.sum_apply, hCoeff, canonicalHemisphereConedFacet]

theorem canonicalGaugeSuspensionConedChain_count_one_of_regular_direction
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1)) (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (q : sphere (0 : V) 1)
    (hreg : ∀ pole : sphere (0 : V) 1, pole = v ∨ pole = -v → ∀ i x,
      x ∈ signedSimplexDomain (n + 3) → canonicalHemisphereConedExtension hp hcont v pole n hdim i x =
      canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val) →
        x ∈ interior (signedSimplexDomain (n + 3)) ∧
        DifferentiableAt ℝ (canonicalHemisphereConedExtension hp hcont v pole n hdim i) x) :
    rawSignedSimplexCount (n + 3) (canonicalGaugeSuspensionConedChain hp hcont v n hdim)
      (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)) = 1 := by
  rw [canonicalGaugeSuspensionConedChain_count_eq_sum]
  by_cases h : 0 ≤ inner ℝ v.val q.val
  · let qN : closedHemisphere v := ⟨q, h⟩
    obtain ⟨hN, hS⟩ := canonicalHemisphere_oriented_count_of_regular_direction hp hcont hSphere v v (Or.inl rfl) n hdim
      1 (Or.inl rfl) (by rw [one_smul]) r hr hr₁ qN (hreg v (Or.inl rfl))
    change (∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) * signedSimplexCount (n + 3)
      (canonicalHemisphereConedFacet hp hcont v v n hdim i) (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val))) = 1 at hN
    rw [hN]
    simp only [show ∀ i : Fin (n + 3), signedSimplexCount (n + 3) (canonicalHemisphereConedFacet hp hcont v (-v) n hdim i)
      (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)) = 0 from hS, mul_zero, Finset.sum_const_zero, sub_zero]
  · have h' : 0 ≤ inner ℝ (-v).val q.val := by
      change 0 ≤ inner ℝ (-v.val) q.val
      rw [inner_neg_left]
      linarith [lt_of_not_ge h]
    let qS : closedHemisphere (-v) := ⟨q, h'⟩
    obtain ⟨hS, hN⟩ := canonicalHemisphere_oriented_count_of_regular_direction hp hcont hSphere v (-v) (Or.inr rfl) n hdim
      (-1) (Or.inr rfl) (by change -v.val = (-1 : ℝ) • v.val; rw [neg_one_smul]) r hr hr₁ qS (hreg (-v) (Or.inr rfl))
    change (∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) * signedSimplexCount (n + 3)
      (canonicalHemisphereConedFacet hp hcont v (-v) n hdim i) (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val))) = -1 at hS
    rw [hS]
    have hN' (i : Fin (n + 3)) : signedSimplexCount (n + 3) (canonicalHemisphereConedFacet hp hcont v v n hdim i)
        (canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val)) = 0 := by
      simpa only [neg_neg] using hN i
    simp only [hN', mul_zero, Finset.sum_const_zero, sub_neg_eq_add, zero_add]

theorem ae_canonicalGaugeSuspensionConedChain_count_one
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1)) (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (μ : Measure (Fin (n + 3) → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ y ∂μ, 0 < p ((canonicalHemisphereChartCoordinates v n hdim).symm y) →
      p ((canonicalHemisphereChartCoordinates v n hdim).symm y) < 1 →
      rawSignedSimplexCount (n + 3) (canonicalGaugeSuspensionConedChain hp hcont v n hdim) y = 1 := by
  let e := canonicalHemisphereChartCoordinates v n hdim
  have hAE (pole : sphere (0 : V) 1) (hSide : pole = v ∨ pole = -v) :
      ∀ᵐ y ∂μ, ∀ i x, x ∈ signedSimplexDomain (n + 3) → canonicalHemisphereConedExtension hp hcont v pole n hdim i x = y →
        x ∈ interior (signedSimplexDomain (n + 3)) ∧
        DifferentiableAt ℝ (canonicalHemisphereConedExtension hp hcont v pole n hdim i) x := by
    apply ae_all_iff.mpr
    intro i
    have h := signedSimplexExtension_ae_regular_interior (n + 3) μ (canonicalHemisphereConedFacet hp hcont v pole n hdim i)
      (exists_lipschitz_canonicalHemisphereConedFacet hp hcont hSphere v pole hSide n hdim i)
    filter_upwards [h] with y hy x hx hxy
    exact ⟨(hy x hx hxy).1, (hy x hx hxy).2.1⟩
  filter_upwards [hAE v (Or.inl rfl), hAE (-v) (Or.inr rfl)] with y hN hS h₀ h₁
  let r := p (e.symm y)
  have hne : e.symm y ≠ 0 := (hp.eq_zero_iff _).not.mp h₀.ne'
  let q : sphere (0 : V) 1 := ⟨NormedSpace.normalize (e.symm y), mem_sphere_zero_iff_norm.mpr
    (norm_normalize hne)⟩
  have he : e (r • radialGaugeMap p q.val) = y := by
    change e (p (e.symm y) • radialGaugeMap p (NormedSpace.normalize (e.symm y))) = y
    rw [radialGaugeMap_normalize_eq_inv_gauge_smul hp hne, smul_smul,
      mul_inv_cancel₀ h₀.ne', one_smul, e.apply_symm_apply]
  rw [← he]
  apply canonicalGaugeSuspensionConedChain_count_one_of_regular_direction hp hcont hSphere v n hdim r h₀ h₁ q
  intro pole hSide i x hx hxy
  change canonicalHemisphereConedExtension hp hcont v pole n hdim i x = e (r • radialGaugeMap p q.val) at hxy
  rw [he] at hxy
  rcases hSide with h | h
  · subst pole
    exact hN i x hx hxy
  · subst pole
    exact hS i x hx hxy

end BanachIsometric.SingularPrism
