import PL1.NoiseGenerator
import PL1.KFunctional
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The genuine generator domain with its complete graph sum norm

The domain is a closed subspace of `WithLp 1 (Y × Y)`, so its inherited norm
is exactly `‖f‖ + ‖Af‖`. The original base norm, resolvent graph and K-functional
are unchanged. The coordinate maps supply the continuous inclusion and the
generator as an operator on this graph-norm domain.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.GeneratorGraphBanach
open Noise Walsh

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

abbrev Ambient := WithLp 1 (Lp K 1 haar × Lp K 1 haar)

def submodule : Submodule K (Ambient K) :=
  (ResolventGeneratorGraph.graph K rates).comap
    (WithLp.prodContinuousLinearEquiv 1 K (Lp K 1 haar) (Lp K 1 haar)).toLinearMap

abbrev Domain := submodule K rates

theorem isClosed_submodule : IsClosed (submodule K rates : Set (Ambient K)) := by
  change IsClosed {z : Ambient K |
    resolventL1 K rates (dyadicTime 0) (z.fst + z.snd) = z.fst}
  exact isClosed_eq ((resolventL1 K rates (dyadicTime 0)).continuous.comp
    ((WithLp.fstL 1 K (Lp K 1 haar) (Lp K 1 haar)).continuous.add
      (WithLp.sndL 1 K (Lp K 1 haar) (Lp K 1 haar)).continuous))
    (WithLp.fstL 1 K (Lp K 1 haar) (Lp K 1 haar)).continuous

instance : CompleteSpace (Domain K rates) :=
  (isClosed_submodule K rates).isComplete.completeSpace_coe

def inclusion : Domain K rates →L[K] Lp K 1 haar :=
  (WithLp.fstL 1 K (Lp K 1 haar) (Lp K 1 haar)).comp (submodule K rates).subtypeL

def generator : Domain K rates →L[K] Lp K 1 haar :=
  (WithLp.sndL 1 K (Lp K 1 haar) (Lp K 1 haar)).comp (submodule K rates).subtypeL

@[simp] theorem inclusion_apply (z : Domain K rates) :
    inclusion K rates z = (z : Ambient K).fst := rfl

@[simp] theorem generator_apply (z : Domain K rates) :
    generator K rates z = (z : Ambient K).snd := rfl

/-- The norm is exactly the manuscript's graph sum norm. -/
theorem norm_eq (z : Domain K rates) :
    ‖z‖ = ‖inclusion K rates z‖ + ‖generator K rates z‖ :=
  WithLp.prod_norm_eq_of_L1 (z : Ambient K)

theorem norm_inclusion_le (z : Domain K rates) : ‖inclusion K rates z‖ ≤ ‖z‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem norm_generator_le (z : Domain K rates) : ‖generator K rates z‖ ≤ ‖z‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (norm_nonneg _)

theorem norm_inclusion_le_one : ‖inclusion K rates‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z => by simpa only [one_mul] using norm_inclusion_le K rates z)

theorem norm_generator_le_one : ‖generator K rates‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z => by simpa only [one_mul] using norm_generator_le K rates z)

theorem isGeneratorPair (z : Domain K rates) :
    Noise.IsGeneratorPair K rates (inclusion K rates z) (generator K rates z) :=
  (Noise.isGeneratorPair_iff_mem_graph K rates _ _).mpr z.property

theorem inclusion_injective : Function.Injective (inclusion K rates) := by
  intro z w hzw
  have hs : generator K rates z = generator K rates w :=
    Noise.IsGeneratorPair.unique K rates (isGeneratorPair K rates z)
      (by rw [hzw]; exact isGeneratorPair K rates w)
  apply Subtype.ext
  apply WithLp.ofLp_injective 1
  exact Prod.ext hzw hs

def ofPair (f g : Lp K 1 haar) (hfg : Noise.IsGeneratorPair K rates f g) : Domain K rates :=
  ⟨WithLp.toLp 1 (f, g), (Noise.isGeneratorPair_iff_mem_graph K rates f g).mp hfg⟩

@[simp] theorem inclusion_ofPair (f g : Lp K 1 haar)
    (hfg : Noise.IsGeneratorPair K rates f g) :
    inclusion K rates (ofPair K rates f g hfg) = f := rfl

@[simp] theorem generator_ofPair (f g : Lp K 1 haar)
    (hfg : Noise.IsGeneratorPair K rates f g) :
    generator K rates (ofPair K rates f g hfg) = g := rfl

theorem norm_ofPair (f g : Lp K 1 haar) (hfg : Noise.IsGeneratorPair K rates f g) :
    ‖ofPair K rates f g hfg‖ = ‖f‖ + ‖g‖ := norm_eq K rates _

theorem mem_range_inclusion_iff (f : Lp K 1 haar) :
    f ∈ (inclusion K rates).range ↔ ∃ g, Noise.IsGeneratorPair K rates f g := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨generator K rates z, isGeneratorPair K rates z⟩
  · rintro ⟨g, hfg⟩
    exact ⟨ofPair K rates f g hfg, rfl⟩

theorem denseRange_inclusion : DenseRange (inclusion K rates) := by
  have he : Set.range (inclusion K rates) =
      {f : Lp K 1 haar | ∃ g, Noise.IsGeneratorPair K rates f g} := by
    ext f
    exact mem_range_inclusion_iff K rates f
  rw [DenseRange, he]
  exact Noise.dense_generator_domain K rates

/-- The existing K-functional is the standard infimum for the continuous
inclusion of this genuine complete graph-norm domain. -/
theorem kFunctional_eq (t : ℝ) (f : Lp K 1 haar) :
    KFunctional.value K rates t f =
      sInf (Set.range (fun z : Domain K rates => ‖f - inclusion K rates z‖ + t * ‖z‖)) := by
  unfold KFunctional.value
  congr 1
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    let w := ofPair K rates z.val.1 z.val.2
      ((Noise.isGeneratorPair_iff_mem_graph K rates _ _).mpr z.property)
    refine ⟨w, ?_⟩
    change ‖f - inclusion K rates w‖ + t * ‖w‖ = _
    rw [norm_eq]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨⟨(inclusion K rates z, generator K rates z),
      (Noise.isGeneratorPair_iff_mem_graph K rates _ _).mp (isGeneratorPair K rates z)⟩, ?_⟩
    change ‖f - inclusion K rates z‖ + t *
      (‖inclusion K rates z‖ + ‖generator K rates z‖) = _
    rw [← norm_eq]

end PL1.GeneratorGraphBanach
