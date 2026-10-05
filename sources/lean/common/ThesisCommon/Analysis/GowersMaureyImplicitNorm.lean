import ThesisCommon.Analysis.GowersMaureyNormTests
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints

/-! The exact Gowers--Maurey implicit norm as a least fixed point. The
four constructors are, respectively, the c₀ norm, the lower-f estimate,
interval restrictions of special functionals, and the tail spreads.
The fixed point is taken among seminorms bounded by finite ℓ1 mass;
its coordinate lower bounds subsequently prove definiteness.
-/
noncomputable section
open scoped BigOperators NNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

inductive NormTest (D : ConstructionData 𝕜) (p : Seminorm 𝕜 (C00 𝕜)) :
    Seminorm 𝕜 (C00 𝕜) → Prop
  | coordinate (n : ℕ) : NormTest D p (coordinateSeminorm n)
  | average (T : IntervalTest) : NormTest D p (intervalAverage p T)
  | special {k : ℕ} (hk : k ∈ D.specialSizes) (g : Fin k → C00 𝕜)
      (hg : SpecialSequence D p g) (E : Interval) :
      NormTest D p ((evaluationSeminorm (specialFunctional g)).comp (restrict E))
  | spread (m n : ℕ) : NormTest D p (p.comp (GowersMaurey.spread m n))

def testSet (D : ConstructionData 𝕜) (p : Seminorm 𝕜 (C00 𝕜)) :
    Set (Seminorm 𝕜 (C00 𝕜)) := {q | NormTest D p q}

theorem testSet_nonempty (D : ConstructionData 𝕜) (p : Seminorm 𝕜 (C00 𝕜)) :
    (testSet D p).Nonempty := ⟨_, NormTest.coordinate 0⟩

theorem normTest_le_mass (D : ConstructionData 𝕜) {p : Seminorm 𝕜 (C00 𝕜)}
    (hp : p ≤ mass) {q : Seminorm 𝕜 (C00 𝕜)} (hq : NormTest D p q) : q ≤ mass := by
  cases hq with
  | coordinate n => exact coordinateSeminorm_le_mass n
  | average T => exact intervalAverage_le_mass p hp T
  | special hk g hg E => exact specialEvaluation_le_mass D p hk hg E
  | spread m n => exact (Seminorm.comp_mono _ hp).trans (mass_spread_le m n)

theorem testSet_bddAbove (D : ConstructionData 𝕜) {p : Seminorm 𝕜 (C00 𝕜)}
    (hp : p ≤ mass) : BddAbove (testSet D p) :=
  ⟨mass, fun _ hq => normTest_le_mass D hp hq⟩

theorem normTest_mono (D : ConstructionData 𝕜) {p q : Seminorm 𝕜 (C00 𝕜)}
    (hpq : p ≤ q) {r : Seminorm 𝕜 (C00 𝕜)} (hr : NormTest D p r) :
    ∃ s, NormTest D q s ∧ r ≤ s := by
  cases hr with
  | coordinate n => exact ⟨_, NormTest.coordinate n, le_rfl⟩
  | average T => exact ⟨_, NormTest.average T, intervalAverage_mono T hpq⟩
  | special hk g hg E =>
    exact ⟨_, NormTest.special hk g (specialSequence_mono D hpq hg) E, le_rfl⟩
  | spread m n => exact ⟨_, NormTest.spread m n, Seminorm.comp_mono _ hpq⟩

instance zero_le_mass : Fact ((0 : Seminorm 𝕜 (C00 𝕜)) ≤ mass) := ⟨bot_le⟩

abbrev BoundedSeminorm (𝕜 : Type*) [RCLike 𝕜] : Type _ :=
  Set.Icc (0 : Seminorm 𝕜 (C00 𝕜)) mass

def normOperator (D : ConstructionData 𝕜) : BoundedSeminorm 𝕜 →o BoundedSeminorm 𝕜 where
  toFun p := ⟨sSup (testSet D p.val), bot_le,
    csSup_le (testSet_nonempty D p.val) (fun _ hq => normTest_le_mass D p.property.2 hq)⟩
  monotone' := by
    intro p q hpq
    change sSup (testSet D p.val) ≤ sSup (testSet D q.val)
    apply csSup_le (testSet_nonempty D p.val)
    intro r hr
    obtain ⟨s, hs, hrs⟩ := normTest_mono D hpq hr
    exact hrs.trans (le_csSup (testSet_bddAbove D q.property.2) hs)

/-- The actual least seminorm satisfying all four implicit norming rules. -/
def implicitNorm (D : ConstructionData 𝕜) : Seminorm 𝕜 (C00 𝕜) :=
  (OrderHom.lfp (α := BoundedSeminorm 𝕜) (normOperator D)).val

theorem implicitNorm_le_mass (D : ConstructionData 𝕜) : implicitNorm D ≤ mass :=
  (OrderHom.lfp (α := BoundedSeminorm 𝕜) (normOperator D)).property.2

theorem implicitNorm_fixed (D : ConstructionData 𝕜) :
    implicitNorm D = sSup (testSet D (implicitNorm D)) := by
  have h := OrderHom.map_lfp (α := BoundedSeminorm 𝕜) (normOperator D)
  exact (congrArg (fun p : BoundedSeminorm 𝕜 => p.val) h).symm

/-- The source's supremum formula, over its four explicitly defined classes of tests. -/
theorem implicitNorm_eq_iSup_tests (D : ConstructionData 𝕜) (x : C00 𝕜) :
    implicitNorm D x = ⨆ q : testSet D (implicitNorm D), q.val x := by
  conv_lhs => rw [implicitNorm_fixed D]
  exact Seminorm.sSup_apply (testSet_bddAbove D (implicitNorm_le_mass D))

theorem test_le_implicitNorm (D : ConstructionData 𝕜) {q : Seminorm 𝕜 (C00 𝕜)}
    (hq : NormTest D (implicitNorm D) q) : q ≤ implicitNorm D := by
  rw [implicitNorm_fixed D]
  exact le_csSup (testSet_bddAbove D (implicitNorm_le_mass D)) hq

theorem coordinate_le_implicitNorm (D : ConstructionData 𝕜) (x : C00 𝕜) (n : ℕ) :
    ‖x n‖ ≤ implicitNorm D x := test_le_implicitNorm D (NormTest.coordinate n) x

theorem implicitNorm_single (D : ConstructionData 𝕜) (n : ℕ) (c : 𝕜) :
    implicitNorm D (Finsupp.single n c) = ‖c‖ := by
  apply le_antisymm
  · exact (implicitNorm_le_mass D _).trans_eq (mass_single n c)
  · simpa using coordinate_le_implicitNorm D (Finsupp.single n c) n

theorem implicitNorm_eq_zero (D : ConstructionData 𝕜) {x : C00 𝕜}
    (hx : implicitNorm D x = 0) : x = 0 := by
  ext n
  apply norm_eq_zero.mp
  exact le_antisymm ((coordinate_le_implicitNorm D x n).trans_eq hx) (norm_nonneg _)

theorem implicitNorm_minimal (D : ConstructionData 𝕜) (p : Seminorm 𝕜 (C00 𝕜))
    (hp : p ≤ mass) (hclosed : ∀ q, NormTest D p q → q ≤ p) : implicitNorm D ≤ p := by
  exact OrderHom.lfp_le (α := BoundedSeminorm 𝕜) (normOperator D) (a := ⟨p, bot_le, hp⟩)
    (csSup_le (testSet_nonempty D p) hclosed)

theorem implicitNorm_spread_le (D : ConstructionData 𝕜) (m n : ℕ) (x : C00 𝕜) :
    implicitNorm D (spread m n x) ≤ implicitNorm D x :=
  test_le_implicitNorm D (NormTest.spread m n) x

theorem implicitNorm_intervalAverage_le (D : ConstructionData 𝕜)
    (T : IntervalTest) (x : C00 𝕜) :
    (logarithmicWeight T.count)⁻¹ * ∑ i, implicitNorm D (restrict (T.interval i) x)
      ≤ implicitNorm D x := by
  rw [← intervalAverage_apply]
  exact test_le_implicitNorm D (NormTest.average T) x

end ThesisCommon.GowersMaurey
