import Posets.AcceptanceDichotomyBorel
import Posets.AcceptanceDichotomyAmalgamation
import Mathlib.Topology.MetricSpace.Cauchy

/-! Diagonal convergence and the scalar-shift acceptance relation are Borel.
The existential scalar is eliminated using the compact diagonal criterion. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology MeasureTheory
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def CauchyAlongNat (A : Set ℕ) (f : ℕ → 𝕜) : Prop :=
  ∀ i : ℕ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → m ∈ A → n ∈ A →
    dist (f m) (f n) < 1 / ((i : ℝ) + 1)

/-- This formulation also handles finite sets: convergence along their bottom filter is vacuous. -/
theorem exists_tendsto_along_iff_cauchyAlongNat (A : Set ℕ) (f : ℕ → 𝕜) :
    (∃ a : 𝕜, Tendsto f (Along A) (𝓝 a)) ↔ CauchyAlongNat A f := by
  constructor
  · rintro ⟨a, ha⟩ i
    have hpos : 0 < 1 / ((i : ℝ) + 1) / 2 := by positivity
    have he := Metric.tendsto_nhds.mp ha _ hpos
    rw [Along, Nat.cofinite_eq_atTop, eventually_inf_principal, eventually_atTop] at he
    obtain ⟨N, hN⟩ := he
    refine ⟨N, fun m n hm hn hmA hnA => ?_⟩
    have hm' := hN m hm hmA
    have hn' := hN n hn hnA
    have ht := dist_triangle_right (f m) (f n) a
    linarith
  · intro h
    by_cases hA : A.Infinite
    · letI : NeBot (Along A) := hA.cofinite_inf_principal_neBot
      apply cauchy_map_iff_exists_tendsto.mp
      apply Metric.cauchy_iff.mpr
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h i
      refine ⟨f '' (A ∩ Set.Ici N), ?_, ?_⟩
      · change {n | f n ∈ f '' (A ∩ Set.Ici N)} ∈ Along A
        have hn : ∀ᶠ n in Along A, N ≤ n := (eventually_ge_atTop N).filter_mono (by
          rw [Along, Nat.cofinite_eq_atTop]
          exact inf_le_left)
        filter_upwards [hn, eventually_mem_along A] with n hn hnA
        exact ⟨n, ⟨hnA, hn⟩, rfl⟩
      · rintro x ⟨m, ⟨hmA, hm⟩, rfl⟩ y ⟨n, ⟨hnA, hn⟩, rfl⟩
        exact (hN m n hm hn hmA hnA).trans hi
    · have hb : Along A = ⊥ := by
        apply not_neBot.mp
        simpa only [Along, cofinite_inf_principal_neBot_iff] using hA
      exact ⟨0, by rw [hb]; exact tendsto_bot⟩

local instance : MeasurableSpace (ℕ → Bool) := borel (ℕ → Bool)
local instance : BorelSpace (ℕ → Bool) := ⟨rfl⟩
local instance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool)) := borel _
local instance : BorelSpace ((ℕ → Bool) × (ℕ → Bool)) := ⟨rfl⟩

theorem measurableSet_cauchyAlongNat_cantor (f : ℕ → 𝕜) :
    MeasurableSet {p : ℕ → Bool | CauchyAlongNat (cantorSet p) f} := by
  simp only [CauchyAlongNat, Set.setOf_forall, Set.setOf_exists]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iUnion (fun N =>
    MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun n =>
    MeasurableSet.iInter (fun (_ : N ≤ m) => MeasurableSet.iInter (fun (_ : N ≤ n) => ?_))))))
  by_cases h : dist (f m) (f n) < ((i : ℝ) + 1)⁻¹
  · simp [h]
  · have hm : MeasurableSet {p : ℕ → Bool | p m = true} :=
      (isClosed_eq (continuous_apply m) continuous_const).measurableSet
    have hn : MeasurableSet {p : ℕ → Bool | p n = true} :=
      (isClosed_eq (continuous_apply n) continuous_const).measurableSet
    convert (hm.inter hn).compl using 1
    ext p
    simp [cantorSet, h]

theorem measurableSet_exists_tendsto_along_cantor (f : ℕ → 𝕜) :
    MeasurableSet {p : ℕ → Bool | ∃ a : 𝕜, Tendsto f (Along (cantorSet p)) (𝓝 a)} := by
  simpa only [exists_tendsto_along_iff_cauchyAlongNat] using measurableSet_cauchyAlongNat_cantor f

/-- The set of subsets accepting some scalar shift is Borel, despite the uncountable scalar quantifier. -/
theorem measurableSet_exists_scalarShift_cantor (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    MeasurableSet {p : ℕ → Bool | ∃ a : 𝕜,
      AcceptsPair 𝕜 (cantorSet p) (cantorSet p) (M - a • identityMatrix 𝕜)} := by
  simp only [exists_acceptsPair_scalarShift_iff hM]
  exact (measurableSet_self_acceptsPair_cantor (matrixOffDiagonal M)
    (boundedRows_matrixOffDiagonal hM)).inter
      (measurableSet_exists_tendsto_along_cantor (fun k => M k k))

def cantorUnion (p : (ℕ → Bool) × (ℕ → Bool)) : ℕ → Bool := fun n => p.1 n || p.2 n

@[simp] theorem cantorSet_cantorUnion (p : (ℕ → Bool) × (ℕ → Bool)) :
    cantorSet (cantorUnion p) = cantorSet p.1 ∪ cantorSet p.2 := by
  ext n
  simp [cantorSet, cantorUnion]

theorem continuous_cantorUnion : Continuous cantorUnion := by
  change Continuous (fun p : (ℕ → Bool) × (ℕ → Bool) => fun n => p.1 n || p.2 n)
  apply continuous_pi
  intro n
  have h : Continuous (fun q : Bool × Bool => q.1 || q.2) := continuous_of_discreteTopology
  have h₁ : Continuous (fun p : (ℕ → Bool) × (ℕ → Bool) => p.1 n) :=
    (continuous_apply n).comp continuous_fst
  have h₂ : Continuous (fun p : (ℕ → Bool) × (ℕ → Bool) => p.2 n) :=
    (continuous_apply n).comp continuous_snd
  exact h.comp (h₁.prodMk h₂)

/-- The Borel relation used in the acceptance/rejection dichotomy (cited Lemma 34). -/
theorem measurableSet_union_exists_scalarShift_cantor (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) :
    MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | ∃ a : 𝕜,
      AcceptsPair 𝕜 (cantorSet p.1 ∪ cantorSet p.2) (cantorSet p.1 ∪ cantorSet p.2)
        (M - a • identityMatrix 𝕜)} := by
  have h := (measurableSet_exists_scalarShift_cantor M hM).preimage
    (f := cantorUnion) continuous_cantorUnion.measurable
  simpa only [Set.preimage_setOf_eq, cantorSet_cantorUnion] using h

end Posets
