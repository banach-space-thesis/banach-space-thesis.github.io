import PL1.ConstantNoiseTrace
import PL1.EnfloStarbirdProjection
import Mathlib.Analysis.RCLike.Extend

/-! # The real trace obstruction underlying the scalar construction

A scalar vanishing-trace operator also has vanishing trace after restricting scalars.
The proof extends the two real factor maps and takes real parts of the dyadic traces.
This is an operator statement and requires no classification of complex L1 spaces.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace PL1.ComplementedLattice

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {K : Type*} [RCLike K]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  [NormedSpace ℝ E] [IsScalarTower ℝ K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedSpace ℝ F] [IsScalarTower ℝ K F]

/-- Scalar-linear part of a real-linear operator. Its normalization is chosen to
recover real-valued inputs without a factor of two. -/
def scalarLinearPart (A : E →L[ℝ] F) : E →L[K] F :=
  let f : E → F := fun x => A x - (RCLike.I : K) • A ((RCLike.I : K) • x)
  have hadd (x y) : f (x + y) = f x + f y := by
    simp only [f, smul_add, map_add]
    abel
  have hreal (c : ℝ) (x : E) : f ((c : K) • x) = (c : K) • f x := by
    simp only [f, ← RCLike.real_smul_eq_coe_smul, map_smul, smul_sub,
      smul_comm (RCLike.I : K) c]
  have hI (x : E) : f ((RCLike.I : K) • x) = (RCLike.I : K) • f x := by
    obtain h | h := @RCLike.I_mul_I_ax K _
    · simp [f, h]
    · simp [f, smul_sub, smul_smul, h, add_comm]
  { toFun := f
    map_add' := hadd
    map_smul' := fun c x => by
      rw [← RCLike.re_add_im c]
      simp only [RingHom.id_apply, add_smul, ← smul_smul, hadd, hreal, hI]
    cont := by dsimp [f]; fun_prop }

@[simp] theorem scalarLinearPart_apply (A : E →L[ℝ] F) (x : E) :
    scalarLinearPart (K := K) A x = A x - (RCLike.I : K) • A ((RCLike.I : K) • x) := rfl

variable (K)

def intervalOfReal : IntervalL1 ℝ →L[ℝ] IntervalL1 K :=
  (@RCLike.ofRealCLM K _).compLpL 1 intervalMeasure

def intervalRe : IntervalL1 K →L[ℝ] IntervalL1 ℝ :=
  (@RCLike.reCLM K _).compLpL 1 intervalMeasure

theorem coeFn_intervalOfReal (f : IntervalL1 ℝ) :
    intervalOfReal K f =ᵐ[intervalMeasure] fun x => (f x : K) :=
  (@RCLike.ofRealCLM K _).coeFn_compLpL f

theorem coeFn_intervalRe (f : IntervalL1 K) :
    intervalRe K f =ᵐ[intervalMeasure] fun x => RCLike.re (f x) :=
  (@RCLike.reCLM K _).coeFn_compLpL f

@[simp] theorem intervalRe_ofReal (f : IntervalL1 ℝ) :
    intervalRe K (intervalOfReal K f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_intervalRe K (intervalOfReal K f), coeFn_intervalOfReal K f]
    with x hr hf
  simp [hr, hf]

@[simp] theorem intervalRe_I_ofReal (f : IntervalL1 ℝ) :
    intervalRe K ((RCLike.I : K) • intervalOfReal K f) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_intervalRe K ((RCLike.I : K) • intervalOfReal K f),
    Lp.coeFn_smul (RCLike.I : K) (intervalOfReal K f), coeFn_intervalOfReal K f,
    Lp.coeFn_zero ℝ 1 intervalMeasure] with x hr hs hf hz
  rw [hr, hs]
  change RCLike.re ((RCLike.I : K) * intervalOfReal K f x) = _
  rw [hf]
  simpa using hz.symm

theorem intervalOfReal_indicator (n i : ℕ) :
    intervalOfReal K (indicatorConstLp 1 (DyadicTrace.measurableSet_cell n i)
      (measure_ne_top intervalMeasure _) (1 : ℝ)) =
      indicatorConstLp 1 (DyadicTrace.measurableSet_cell n i)
        (measure_ne_top intervalMeasure _) (1 : K) := by
  apply Lp.ext
  filter_upwards [coeFn_intervalOfReal K (indicatorConstLp 1
    (DyadicTrace.measurableSet_cell n i) (measure_ne_top intervalMeasure _) (1 : ℝ)),
    indicatorConstLp_coeFn (p := 1) (hs := DyadicTrace.measurableSet_cell n i)
      (hμs := measure_ne_top intervalMeasure _) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 1) (hs := DyadicTrace.measurableSet_cell n i)
      (hμs := measure_ne_top intervalMeasure _) (c := (1 : K))] with x hc hr hk
  rw [hc, hr, hk]
  by_cases hx : x ∈ DyadicTrace.cell n i <;> simp [hx]

variable {K}

def extendRealInput (B : IntervalL1 ℝ →L[ℝ] E) : IntervalL1 K →L[K] E :=
  scalarLinearPart (B.comp (intervalRe K))

def extendRealOutput (A : F →L[ℝ] IntervalL1 ℝ) : F →L[K] IntervalL1 K :=
  scalarLinearPart ((intervalOfReal K).comp A)

@[simp] theorem extendRealInput_ofReal (B : IntervalL1 ℝ →L[ℝ] E)
    (f : IntervalL1 ℝ) : extendRealInput B (intervalOfReal K f) = B f := by
  simp [extendRealInput]

@[simp] theorem intervalRe_extendRealOutput (A : F →L[ℝ] IntervalL1 ℝ) (x : F) :
    intervalRe K (extendRealOutput A x) = A x := by
  simp [extendRealOutput]

theorem trace_real_part (R : IntervalL1 K →L[K] IntervalL1 K) (n : ℕ) :
    DyadicTrace.trace n ((intervalRe K).comp
      ((R.restrictScalars ℝ).comp (intervalOfReal K))) = RCLike.re (DyadicTrace.trace n R) := by
  rw [DyadicTrace.trace_eq, DyadicTrace.trace_eq, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    intervalOfReal_indicator]
  rw [← integral_re]
  · exact integral_congr_ae (ae_restrict_of_ae (coeFn_intervalRe K _))
  · exact (L1.integrable_coeFn _).integrableOn

/-- Scalar vanishing trace descends to the underlying real operator. -/
theorem hasVanishingDyadicTrace_restrictScalars (S : E →L[K] F)
    (hS : HasVanishingDyadicTrace S) : HasVanishingDyadicTrace (S.restrictScalars ℝ) := by
  intro A B
  have h := ((@RCLike.reCLM K _).continuous.tendsto 0).comp
    (hS (extendRealOutput A) (extendRealInput B))
  have he : (intervalRe K).comp
      ((((extendRealOutput A).comp (S.comp (extendRealInput B))).restrictScalars ℝ).comp
        (intervalOfReal K)) = A.comp ((S.restrictScalars ℝ).comp B) := by
    ext f
    simp
  rw [map_zero] at h
  change Tendsto (fun n => RCLike.re (DyadicTrace.trace n
    ((extendRealOutput A).comp (S.comp (extendRealInput B))))) atTop (𝓝 0) at h
  simpa only [← trace_real_part, he] using h

theorem constant_intervalProjection_real_hasVanishingDyadicTrace (K : Type*) [RCLike K] :
    HasVanishingDyadicTrace ((Noise.intervalProjection K Noise.constantRates).restrictScalars ℝ) :=
  hasVanishingDyadicTrace_restrictScalars _
    (Noise.constant_intervalProjection_hasVanishingDyadicTrace K)

#print axioms hasVanishingDyadicTrace_restrictScalars

end PL1.ComplementedLattice
