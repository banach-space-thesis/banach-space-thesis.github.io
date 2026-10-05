import ThesisCommon.Analysis.MeasureAlgebra
import ThesisCommon.Analysis.SuperlevelLimits

/-! Preservation of superlevel sets of almost-everywhere limits by a genuine
measure-algebra isomorphism. This is the corrected countable-limit step in
PEMS Lemma 4.3; it does not assume a point map between the measure spaces. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace ThesisCommon
namespace MeasureAlgebra
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def superlevel (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (c : ℝ) :
    MeasureAlgebra μ := mk μ {x | c < f x} (measurableSet_lt measurable_const hf)

def closedSuperlevel (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (c : ℝ) :
    MeasureAlgebra μ := mk μ {x | c ≤ f x} (measurableSet_le measurable_const hf)

/-- Recover the non-strict threshold used in the paper's truncated kernels
from countably many strict thresholds, without discarding level sets. -/
theorem closedSuperlevel_eq_iInter (f : X → ℝ) (hf : Measurable f) (c : ℝ) :
    closedSuperlevel μ f hf c = iInter (fun q : {q : ℚ // (q : ℝ) < c} =>
      superlevel μ f hf q) := by
  simp only [closedSuperlevel, superlevel, iInter_mk]
  apply (mk_eq_mk _ _).mpr
  apply Filter.Eventually.of_forall
  intro x
  apply propext
  change (c ≤ f x) ↔ x ∈ ⋂ q : {q : ℚ // (q : ℝ) < c}, {x | (q : ℝ) < f x}
  simp only [mem_iInter, mem_setOf_eq]
  constructor
  · intro h q
    exact q.property.trans_le h
  · intro h
    by_contra hc
    obtain ⟨q, hfq, hqc⟩ := exists_rat_btwn (lt_of_not_ge hc)
    exact (lt_asymm hfq (h ⟨q, hqc⟩))

theorem superlevel_of_ae_tendsto (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (g : X → ℝ) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) (c : ℝ) :
    superlevel μ g hg c =
      iUnion (fun q : {q : ℚ // c < (q : ℝ)} =>
        iUnion (fun N : ℕ => iInter (fun n : {n : ℕ // N ≤ n} =>
          superlevel μ (f n) (hf n) q))) := by
  simp only [superlevel, iInter_mk, iUnion_mk]
  apply (mk_eq_mk _ _).mpr
  filter_upwards [hlim] with x hx
  apply propext
  change (c < g x) ↔ x ∈ (⋃ q : {q : ℚ // c < (q : ℝ)},
    ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n}, {x | (q : ℝ) < f n x})
  simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
  rw [lt_limit_iff_exists_rat_eventually hx]
  simp only [eventually_atTop]
  constructor
  · rintro ⟨q, hcq, N, hN⟩
    exact ⟨⟨q, hcq⟩, N, fun n => hN n n.property⟩
  · rintro ⟨q, N, hN⟩
    exact ⟨q, q.property, N, fun n hn => hN ⟨n, hn⟩⟩

end MeasureAlgebra

namespace MeasureAlgebraIso
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- Rational superlevel transport for the approximants passes to every real
superlevel of their ae limits. Countability keeps null sets under control. -/
theorem map_superlevel_of_ae_tendsto (Φ : MeasureAlgebraIso μ ν)
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (g : ℕ → Y → ℝ) (hg : ∀ n, Measurable (g n))
    (f₀ : X → ℝ) (hf₀ : Measurable f₀) (g₀ : Y → ℝ) (hg₀ : Measurable g₀)
    (hflim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hglim : ∀ᵐ y ∂ν, Tendsto (fun n => g n y) atTop (𝓝 (g₀ y)))
    (htransport : ∀ n (q : ℚ),
      Φ.toEquiv (MeasureAlgebra.superlevel μ (f n) (hf n) q) =
        MeasureAlgebra.superlevel ν (g n) (hg n) q) (c : ℝ) :
    Φ.toEquiv (MeasureAlgebra.superlevel μ f₀ hf₀ c) =
      MeasureAlgebra.superlevel ν g₀ hg₀ c := by
  rw [MeasureAlgebra.superlevel_of_ae_tendsto f hf f₀ hf₀ hflim,
    MeasureAlgebra.superlevel_of_ae_tendsto g hg g₀ hg₀ hglim]
  simp only [Φ.map_iUnion, Φ.map_iInter, htransport]

/-- Non-strict superlevels of the limits are preserved too. In particular,
the equality-at-threshold convention for truncated kernels is retained. -/
theorem map_closedSuperlevel_of_ae_tendsto (Φ : MeasureAlgebraIso μ ν)
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (g : ℕ → Y → ℝ) (hg : ∀ n, Measurable (g n))
    (f₀ : X → ℝ) (hf₀ : Measurable f₀) (g₀ : Y → ℝ) (hg₀ : Measurable g₀)
    (hflim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hglim : ∀ᵐ y ∂ν, Tendsto (fun n => g n y) atTop (𝓝 (g₀ y)))
    (htransport : ∀ n (q : ℚ),
      Φ.toEquiv (MeasureAlgebra.superlevel μ (f n) (hf n) q) =
        MeasureAlgebra.superlevel ν (g n) (hg n) q) (c : ℝ) :
    Φ.toEquiv (MeasureAlgebra.closedSuperlevel μ f₀ hf₀ c) =
      MeasureAlgebra.closedSuperlevel ν g₀ hg₀ c := by
  rw [MeasureAlgebra.closedSuperlevel_eq_iInter, MeasureAlgebra.closedSuperlevel_eq_iInter,
    Φ.map_iInter]
  congr 1
  funext q
  exact Φ.map_superlevel_of_ae_tendsto f hf g hg f₀ hf₀ g₀ hg₀ hflim hglim htransport q

end MeasureAlgebraIso
end ThesisCommon
