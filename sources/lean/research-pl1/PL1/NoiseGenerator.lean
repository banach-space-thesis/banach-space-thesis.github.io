import PL1.ResolventAlmostInvariant
import PL1.ResolventGeneratorGraph
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The genuine infinitesimal generator of the product-noise semigroup

The generator is defined by the right norm derivative of the actual Haar L1
semigroup. Uniform bounds on resolvent difference quotients and the dense
Walsh family identify its domain with the concrete resolvent graph.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace PL1.Noise
open Walsh

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- The actual right difference quotient of the noise semigroup. -/
def generatorQuotient (u : ℝ≥0) : Lp K 1 haar →L[K] Lp K 1 haar :=
  (u : ℝ)⁻¹ • (noiseL1 K rates u - ContinuousLinearMap.id K (Lp K 1 haar))

@[simp] theorem generatorQuotient_apply (u : ℝ≥0) (f : Lp K 1 haar) :
    generatorQuotient K rates u f = (u : ℝ)⁻¹ • (noiseL1 K rates u f - f) := rfl

/-- `g` is the positive generator applied to `f`, so the semigroup derivative equals `-g`. -/
def IsGeneratorPair (f g : Lp K 1 haar) : Prop :=
  Tendsto (fun u : ℝ≥0 => generatorQuotient K rates u f) (𝓝[>] 0) (𝓝 (-g))

/-- Resolvent-regularized difference quotients, with the unit resolvent used in the graph. -/
def regularizedQuotient (u : ℝ≥0) : Lp K 1 haar →L[K] Lp K 1 haar :=
  (u : ℝ)⁻¹ • ((noiseL1 K rates u).comp (resolventL1 K rates (dyadicTime 0)) -
    resolventL1 K rates (dyadicTime 0))

theorem regularizedQuotient_apply (u : ℝ≥0) (f : Lp K 1 haar) :
    regularizedQuotient K rates u f =
      generatorQuotient K rates u (resolventL1 K rates (dyadicTime 0) f) := rfl

/-- The operator family is uniformly bounded even at the zero endpoint. -/
theorem norm_regularizedQuotient_le (u : ℝ≥0) : ‖regularizedQuotient K rates u‖ ≤ 2 := by
  by_cases hu : u = 0
  · simp [regularizedQuotient, hu]
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (pos_iff_ne_zero.mpr hu)
  rw [regularizedQuotient, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr u.coe_nonneg)]
  apply (mul_le_mul_of_nonneg_left (norm_noise_comp_resolvent_sub_le_time K rates (dyadicTime 0) u)
    (inv_nonneg.mpr u.coe_nonneg)).trans_eq
  simp only [dyadicTime, pow_zero, Subtype.coe_mk, div_one]
  field_simp

private theorem tendsto_exp_quotient (lam : ℝ) :
    Tendsto (fun u : ℝ≥0 => (u : ℝ)⁻¹ * (Real.exp (-(u : ℝ) * lam) - 1))
      (𝓝[>] 0) (𝓝 (-lam)) := by
  have hd : HasDerivAt (fun u : ℝ => Real.exp (-u * lam)) (-lam) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg.mul_const lam).exp) using 1 <;> simp
  have ht := hd.tendsto_slope_zero_right
  have hcoe : Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    exact (NNReal.map_coe_nhdsGT 0).le
  simpa only [Function.comp_def, zero_add, neg_zero, zero_mul, Real.exp_zero,
    smul_eq_mul] using ht.comp hcoe

/-- The right norm derivative of the unit-resolvent orbit on the dense Walsh family. -/
theorem tendsto_regularizedQuotient_character (F : Finset ℕ) :
    Tendsto (fun u : ℝ≥0 => regularizedQuotient K rates u (scalarCharacterLp K 1 F))
      (𝓝[>] 0) (𝓝 ((resolventL1 K rates (dyadicTime 0) - ContinuousLinearMap.id K (Lp K 1 haar))
        (scalarCharacterLp K 1 F))) := by
  let lam := rateSum rates F
  have hden : 1 + lam ≠ 0 := ne_of_gt (by dsimp [lam]; linarith [rateSum_nonneg rates F])
  have ht := (tendsto_exp_quotient lam).mul_const ((1 + lam)⁻¹)
  have hscalar : -lam * (1 + lam)⁻¹ = (1 + lam)⁻¹ - 1 := by field_simp; ring
  rw [hscalar] at ht
  have hc := ((RCLike.continuous_ofReal : Continuous (fun x : ℝ => (x : K))).tendsto _).comp ht
  have hv := hc.smul_const (scalarCharacterLp K 1 F)
  convert hv using 1
  · funext u
    simp only [Function.comp_def, regularizedQuotient, smul_apply, sub_apply, ContinuousLinearMap.comp_apply,
      resolventL1_scalarCharacter, map_smul, noiseL1_character, dyadicTime, pow_zero,
      one_mul, RCLike.real_smul_eq_coe_smul (K := K), smul_smul,
      ← sub_smul, RCLike.ofReal_mul, RCLike.ofReal_sub, RCLike.ofReal_one]
    congr 1
    dsimp [lam]
    ring
  · simp only [sub_apply, ContinuousLinearMap.id_apply, resolventL1_scalarCharacter,
      dyadicTime, pow_zero, one_mul, RCLike.ofReal_sub, RCLike.ofReal_one,
      sub_smul, one_smul, lam]

/-- Every resolvent image has the actual right norm derivative given by its resolvent equation. -/
theorem tendsto_generatorQuotient_resolvent (f : Lp K 1 haar) :
    Tendsto (fun u : ℝ≥0 => generatorQuotient K rates u (resolventL1 K rates (dyadicTime 0) f))
      (𝓝[>] 0) (𝓝 (resolventL1 K rates (dyadicTime 0) f - f)) := by
  exact tendsto_apply_of_dense_span (scalarCharacterLp K 1)
    (dense_span_scalarCharacterLp K 1 (by norm_num)) (regularizedQuotient K rates)
    (resolventL1 K rates (dyadicTime 0) - ContinuousLinearMap.id K (Lp K 1 haar)) (𝓝[>] 0)
    2 (norm_regularizedQuotient_le K rates) (tendsto_regularizedQuotient_character K rates) f

#print axioms tendsto_generatorQuotient_resolvent
end PL1.Noise

namespace PL1.Noise
open Walsh
variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- Resolvents commute with the genuine difference quotients, including the zero endpoint. -/
theorem resolvent_generatorQuotient (t : PositiveTime) (u : ℝ≥0) (f : Lp K 1 haar) :
    resolventL1 K rates t (generatorQuotient K rates u f) =
      generatorQuotient K rates u (resolventL1 K rates t f) := by
  simp only [generatorQuotient_apply, RCLike.real_smul_eq_coe_smul (K := K), map_smul, map_sub]
  congr 2
  exact (DFunLike.congr_fun (noiseL1_resolvent_commute K rates u t) f).symm

/-- The right norm derivative and the concrete resolvent graph give exactly the same pairs. -/
theorem isGeneratorPair_iff_resolvent (f g : Lp K 1 haar) :
    IsGeneratorPair K rates f g ↔ resolventL1 K rates (dyadicTime 0) (f + g) = f := by
  constructor
  · intro hg
    have ht := ((resolventL1 K rates (dyadicTime 0)).continuous.tendsto (-g)).comp hg
    have ht' : Tendsto (fun u : ℝ≥0 => generatorQuotient K rates u
        (resolventL1 K rates (dyadicTime 0) f)) (𝓝[>] 0)
        (𝓝 (-resolventL1 K rates (dyadicTime 0) g)) := by
      simpa only [Function.comp_def, resolvent_generatorQuotient, map_neg] using ht
    have he := tendsto_nhds_unique (tendsto_generatorQuotient_resolvent K rates f) ht'
    rw [map_add]
    apply sub_eq_zero.mp
    calc
      _ = (resolventL1 K rates (dyadicTime 0) f - f) +
          resolventL1 K rates (dyadicTime 0) g := by abel
      _ = 0 := by rw [he, neg_add_cancel]
  · intro he
    have ht := tendsto_generatorQuotient_resolvent K rates (f + g)
    simpa only [IsGeneratorPair, he, sub_add_eq_sub_sub, sub_self, zero_sub] using ht

#print axioms isGeneratorPair_iff_resolvent
end PL1.Noise

namespace PL1.Noise
open Walsh
variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- The concrete graph is exactly the graph of the genuine positive infinitesimal generator. -/
theorem isGeneratorPair_iff_mem_graph (f g : Lp K 1 haar) :
    IsGeneratorPair K rates f g ↔ (f, g) ∈ ResolventGeneratorGraph.graph K rates :=
  isGeneratorPair_iff_resolvent K rates f g

/-- Positive-time resolvents map every L1 function into the genuine generator domain. -/
theorem isGeneratorPair_resolvent (t : PositiveTime) (f : Lp K 1 haar) :
    IsGeneratorPair K rates (resolventL1 K rates t f)
      ((((t : ℝ)⁻¹ : ℝ) : K) • (f - resolventL1 K rates t f)) :=
  (isGeneratorPair_iff_mem_graph K rates _ _).mpr
    (ResolventGeneratorGraph.resolvent_pair_mem K rates t f)

/-- The generator's value is unique; no choice of derivative is built into the graph. -/
theorem IsGeneratorPair.unique {f g h : Lp K 1 haar}
    (hg : IsGeneratorPair K rates f g) (hh : IsGeneratorPair K rates f h) : g = h :=
  ResolventGeneratorGraph.snd_unique K rates
    ((isGeneratorPair_iff_mem_graph K rates f g).mp hg)
    ((isGeneratorPair_iff_mem_graph K rates f h).mp hh)

/-- The generator domain is precisely the range of the actual unit resolvent. -/
theorem exists_generatorPair_iff_range (f : Lp K 1 haar) :
    (∃ g, IsGeneratorPair K rates f g) ↔ f ∈ (resolventL1 K rates (dyadicTime 0)).range := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨f + g, (isGeneratorPair_iff_resolvent K rates f g).mp hg⟩
  · rintro ⟨x, hx⟩
    refine ⟨x - f, (isGeneratorPair_iff_resolvent K rates f (x - f)).mpr ?_⟩
    rw [add_sub_cancel]
    exact hx

#print axioms isGeneratorPair_iff_mem_graph
#print axioms isGeneratorPair_resolvent
end PL1.Noise

namespace PL1.Noise
open Walsh
variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- The genuine generator has dense domain in the original Haar L1 space. -/
theorem dense_generator_domain :
    Dense {f : Lp K 1 haar | ∃ g, IsGeneratorPair K rates f g} := by
  intro f
  apply isClosed_closure.mem_of_tendsto (dyadic_resolvent_strong K rates f)
  exact Eventually.of_forall (fun n => subset_closure
    ⟨_, isGeneratorPair_resolvent K rates (dyadicTime n) f⟩)

/-- The graph of the genuine generator is closed in the original product norm. -/
theorem isClosed_generator_graph :
    IsClosed {z : Lp K 1 haar × Lp K 1 haar | IsGeneratorPair K rates z.1 z.2} := by
  simp only [isGeneratorPair_iff_resolvent]
  exact isClosed_eq ((resolventL1 K rates (dyadicTime 0)).continuous.comp
    (continuous_fst.add continuous_snd)) continuous_fst

/-- The generator is the positive diagonal Walsh multiplier asserted in the manuscript. -/
theorem isGeneratorPair_character (F : Finset ℕ) :
    IsGeneratorPair K rates (scalarCharacterLp K 1 F)
      ((rateSum rates F : K) • scalarCharacterLp K 1 F) := by
  apply (isGeneratorPair_iff_resolvent K rates _ _).mpr
  have he : scalarCharacterLp K 1 F + (rateSum rates F : K) • scalarCharacterLp K 1 F =
      ((1 + rateSum rates F : ℝ) : K) • scalarCharacterLp K 1 F := by
    simp only [RCLike.ofReal_add, RCLike.ofReal_one, add_smul, one_smul]
  rw [he, map_smul, resolventL1_scalarCharacter, smul_smul]
  have hn : 1 + rateSum rates F ≠ 0 := ne_of_gt (by linarith [rateSum_nonneg rates F])
  simp only [dyadicTime, pow_zero, one_mul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hn,
    RCLike.ofReal_one, one_smul]

#print axioms dense_generator_domain
#print axioms isClosed_generator_graph
#print axioms isGeneratorPair_character
end PL1.Noise
