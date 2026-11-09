import BanachIsometric.SignedIndexHomotopy
import BanachIsometric.ConeFamilyContinuity
import BanachIsometric.SignedCoordinateTransport

/-!
# Canonical index invariance for actual sphere-cone homotopies

The sphere belongs to the original space, which may be the paper's Euclidean
space. Coordinates are transported by an actual continuous linear
equivalence. Each cone slice is proved globally Lipschitz from the sphere
slice, and continuity and nonvanishing on the source boundary are proved from
the actual cone formula.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

theorem localSignedIndex_coordinate_cone_homotopy
    {P V : Type*} [PseudoMetricSpace P] [CompactSpace P] [PreconnectedSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (H : P → sphere (0 : V) 1 → sphere (0 : V) 1)
    (hH : Continuous (fun z : P × sphere (0 : V) 1 => H z.1 z.2))
    (hLip : ∀ p, ∃ C : ℝ≥0, LipschitzWith C (H p))
    (a b : PiolaSpace n) (hab : a ≤ b)
    (hzero : ∀ x ∈ piolaBoxBoundary a b, x ≠ 0) (p q : P) :
    localSignedIndex (coordinateMapConjugate e (coneExtension (fun u => (H p u : V)))) a b 0 =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun u => (H q u : V)))) a b 0 := by
  let A : P → sphere (0 : V) 1 → V := fun t u => (H t u : V)
  let F : P → PiolaSpace n → PiolaSpace n :=
    fun t => coordinateMapConjugate e (coneExtension (A t))
  have hA : Continuous (fun z : P × sphere (0 : V) 1 => A z.1 z.2) :=
    continuous_subtype_val.comp hH
  have hFLip : ∀ t, ∃ C : ℝ≥0, LipschitzWith C (F t) := by
    intro t
    obtain ⟨C, hC⟩ := hLip t
    have hAC : LipschitzWith (1 * C) (A t) := (LipschitzWith.subtype_val _).comp hC
    obtain ⟨L, hL⟩ := exists_lipschitz_coneExtension hAC
    exact ⟨_, e.lipschitz.comp (hL.comp e.symm.lipschitz)⟩
  have hpre {x : PiolaSpace n} (hx : x ≠ 0) : e.symm x ≠ 0 := by
    intro h
    apply hx
    simpa only [e.apply_symm_apply, map_zero] using congrArg e h
  let inc : P × piolaBoxBoundary a b → P × {x : V // x ≠ 0} :=
    fun z => (z.1, ⟨e.symm z.2.val, hpre (hzero z.2.val z.2.property)⟩)
  have hinc : Continuous inc := continuous_fst.prodMk
    ((e.symm.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have hF : Continuous (fun z : P × piolaBoxBoundary a b => F z.1 z.2) :=
    e.continuous.comp ((continuous_coneExtension_family_punctured A hA).comp hinc)
  have hboundary : ∀ t, (0 : PiolaSpace n) ∉ F t '' piolaBoxBoundary a b := by
    intro t hmem
    obtain ⟨x, hx, heq⟩ := hmem
    have hx' : e.symm x ≠ 0 := hpre (hzero x hx)
    have hnorm : ‖A t (coneDirection (e.symm x) hx')‖ = 1 := by
      simpa only [A, Metric.mem_sphere, dist_zero_right] using
        (H t (coneDirection (e.symm x) hx')).property
    have hunit : A t (coneDirection (e.symm x) hx') ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hnorm
      exact zero_ne_one hnorm
    have hcone : coneExtension (A t) (e.symm x) ≠ 0 := by
      rw [coneExtension_of_ne (A t) _ hx']
      exact smul_ne_zero (norm_ne_zero_iff.mpr hx') hunit
    apply hcone
    apply e.injective
    simpa only [F, coordinateMapConjugate, map_zero] using heq
  exact localSignedIndex_homotopy_eq_of_lipschitz F hFLip a b hab hF 0 hboundary p q

theorem localSignedIndex_coordinate_cone_homotopy_of_zero_mem_interior
    {P V : Type*} [PseudoMetricSpace P] [CompactSpace P] [PreconnectedSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (H : P → sphere (0 : V) 1 → sphere (0 : V) 1)
    (hH : Continuous (fun z : P × sphere (0 : V) 1 => H z.1 z.2))
    (hLip : ∀ p, ∃ C : ℝ≥0, LipschitzWith C (H p))
    (a b : PiolaSpace n) (hab : a ≤ b) (hzero : (0 : PiolaSpace n) ∈ interior (Icc a b))
    (p q : P) :
    localSignedIndex (coordinateMapConjugate e (coneExtension (fun u => (H p u : V)))) a b 0 =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun u => (H q u : V)))) a b 0 := by
  apply localSignedIndex_coordinate_cone_homotopy e H hH hLip a b hab _ p q
  intro x hx heq
  subst x
  rw [piolaBoxBoundary_eq_frontier, frontier] at hx
  exact hx.2 hzero

end BanachIsometric
