import ThesisCommon.Analysis.PositiveConcaveEnvelope
import Mathlib.Analysis.Convex.Slope

/-! Supermultiplicativity is preserved by the concrete concave envelope.
The proof multiplies positive hypographs by coordinatewise linear maps,
then passes to convex hulls and bounded suprema. -/
noncomputable section
namespace ThesisCommon

def coordinateProductLinear (p : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun q := (p.1 * q.1, p.2 * q.2)
  map_add' q r := by ext <;> simp [mul_add]
  map_smul' a q := by ext <;> simp [mul_left_comm]

theorem positiveHypograph_mul_mem {H : ℝ → ℝ}
    (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → H x * H y ≤ H (x * y))
    {p q : ℝ × ℝ} (hp : p ∈ positiveHypograph H) (hq : q ∈ positiveHypograph H) :
    coordinateProductLinear p q ∈ positiveHypograph H := by
  exact ⟨mul_nonneg hp.1 hq.1, mul_nonneg hp.2.1 hq.2.1,
    (mul_le_mul hp.2.2 hq.2.2 hq.2.1 (hp.2.1.trans hp.2.2)).trans
      (hmul p.1 q.1 hp.1 hq.1)⟩

theorem positiveHypograph_hull_mul_mem {H : ℝ → ℝ}
    (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → H x * H y ≤ H (x * y))
    {p q : ℝ × ℝ} (hp : p ∈ convexHull ℝ (positiveHypograph H))
    (hq : q ∈ convexHull ℝ (positiveHypograph H)) :
    coordinateProductLinear p q ∈ convexHull ℝ (positiveHypograph H) := by
  have hbase : ∀ p ∈ positiveHypograph H, ∀ q ∈ convexHull ℝ (positiveHypograph H),
      coordinateProductLinear p q ∈ convexHull ℝ (positiveHypograph H) := by
    intro p hp
    apply convexHull_min
    · intro q hq
      exact subset_convexHull ℝ _ (positiveHypograph_mul_mem hmul hp hq)
    · exact (convex_convexHull ℝ _).is_linear_preimage (coordinateProductLinear p).isLinear
  have hs : positiveHypograph H ⊆ (coordinateProductLinear q) ⁻¹'
      convexHull ℝ (positiveHypograph H) := by
    intro p hp
    have hh := hbase p hp q hq
    simpa only [coordinateProductLinear, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hh
  have hh := convexHull_min hs
    ((convex_convexHull ℝ _).is_linear_preimage (coordinateProductLinear q).isLinear) hp
  change coordinateProductLinear q p ∈ convexHull ℝ (positiveHypograph H) at hh
  simpa only [coordinateProductLinear, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hh

theorem positiveConcaveEnvelope_mul_le {H : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x)
    (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → H x * H y ≤ H (x * y))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    positiveConcaveEnvelope H x * positiveConcaveEnvelope H y ≤ positiveConcaveEnvelope H (x * y) := by
  have hpair : ∀ u ∈ concaveEnvelopeValues H x, ∀ v ∈ concaveEnvelopeValues H y,
      u * v ≤ positiveConcaveEnvelope H (x * y) := by
    intro u hu v hv
    exact le_csSup (concaveEnvelopeValues_bddAbove hH1 _)
      (positiveHypograph_hull_mul_mem hmul hu hv)
  have hfirst : ∀ u ∈ concaveEnvelopeValues H x,
      u * positiveConcaveEnvelope H y ≤ positiveConcaveEnvelope H (x * y) := by
    intro u hu
    simpa only [add_zero] using affine_csSup_le (concaveEnvelopeValues_nonempty hH0 hy)
      (b := 0) (positiveHypograph_hull_bounds hH1 hu).2.1
      (fun v hv => by simpa only [add_zero] using hpair u hu v hv)
  have hh := affine_csSup_le (concaveEnvelopeValues_nonempty hH0 hx) (b := 0)
    (positiveConcaveEnvelope_nonneg hH0 hH1 hy)
    (fun u hu => by simpa only [add_zero, mul_comm] using hfirst u hu)
  simpa only [add_zero, mul_comm] using hh

theorem concaveOn_Ici_nonneg_monotone {G : ℝ → ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hG0 : ∀ x, 0 ≤ x → 0 ≤ G x) :
    MonotoneOn G (Set.Ici 0) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  by_contra h
  have hdrop : G y < G x := lt_of_not_ge h
  let c := (G x - G y) / (y - x)
  have hc : 0 < c := div_pos (sub_pos.mpr hdrop) (sub_pos.mpr hxy)
  let z := y + (G y + 1) / c
  have hyz : y < z := by
    dsimp [z]
    have := div_pos (show 0 < G y + 1 by linarith [hG0 y hy]) hc
    linarith
  have hz : 0 ≤ z := (show 0 ≤ y from hy).trans hyz.le
  have hs := hG.slope_anti_adjacent hx hz hxy hyz
  have hratio : (G y - G x) / (y - x) = -c := by dsimp [c]; ring
  rw [hratio, div_le_iff₀ (sub_pos.mpr hyz)] at hs
  have heq : c * (z - y) = G y + 1 := by
    dsimp [z]
    field_simp
    ring
  nlinarith [hG0 z hz]

theorem positiveConcaveEnvelope_monotoneOn {H : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x) :
    MonotoneOn (positiveConcaveEnvelope H) (Set.Ici 0) :=
  concaveOn_Ici_nonneg_monotone (positiveConcaveEnvelope_concaveOn hH0 hH1)
    (fun _ hx => positiveConcaveEnvelope_nonneg hH0 hH1 hx)

end ThesisCommon
