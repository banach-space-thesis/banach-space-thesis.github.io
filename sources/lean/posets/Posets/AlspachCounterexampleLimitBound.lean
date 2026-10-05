import Posets.AlspachCounterexampleLimitFiber
import Posets.AlspachCounterexampleFiniteBound
import ThesisCommon.Analysis.OrdinalCharacteristic

/-! A common Wolfe bound on all components leaves only the distinguished
limit row; one additional level eliminates that singleton. This turns the
finite-stage threshold bounds into a bound strictly below ω². -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology Order ThesisCommon
open scoped OnePoint Ordinal
namespace Posets
namespace AlspachCompactRows
variable {𝕜 : Type*} [RCLike 𝕜] (F : ℕ → AlspachCompactRows 𝕜)

@[simp] theorem limitFiberIndex_nonroot (n : ℕ)
    (j : {j : (F n).Index // j ≠ (F n).rows.index}) :
    limitFiberIndex F n j =
      (OnePoint.some (⟨n, j⟩ : Σ n, {j : (F n).Index // j ≠ (F n).rows.index})) := by
  simp [limitFiberIndex, AlspachPointedRows.limitIndex, j.property, OnePoint.some]

theorem limit_wolfeMeasures_subset_root {ε : ℝ} (ξ : Ordinal)
    (hF : ∀ n, wolfeFamily (F n).pointAtomicModel ε (range (F n).weakRows) ξ = ∅) :
    wolfeMeasures (limit F).pointAtomicModel ε (range (limit F).weakRows) ξ ⊆
      {(limit F).weakRows ∞} := by
  rintro μ ⟨⟨μ, U⟩, hU, rfl⟩
  obtain ⟨z, rfl⟩ := (wolfeFamily_subset_base (limit F).pointAtomicModel ε _ ξ hU).1
  cases z using OnePoint.rec with
  | infty => exact mem_singleton _
  | coe z =>
    rcases z with ⟨n, j⟩
    let V : Set (limit F).Index := range
      (fun j : {j : (F n).Index // j ≠ (F n).rows.index} =>
        (OnePoint.some (⟨n, j⟩ : Σ n, {j : (F n).Index // j ≠ (F n).rows.index})))
    have hV : IsOpen V :=
      ((OnePoint.isOpenEmbedding_coe
        (X := Σ n, {j : (F n).Index // j ≠ (F n).rows.index})).comp
        (IsOpenEmbedding.sigmaMk (i := n))).isOpen_range
    have hl := alspach_wolfe_localize_parameter (limit F).pointAtomicModel ε
      (limit F).weakRows (limit F).weakRows_isClosedEmbedding.isEmbedding univ V hV
      ((OnePoint.some (⟨n, j⟩ : Σ n, {j : (F n).Index // j ≠ (F n).rows.index})))
      (show _ ∈ V from ⟨j, rfl⟩) U ξ (by simpa only [image_univ] using hU)
    have hs : (limit F).weakRows '' (univ ∩ V) ⊆
        range (fun j => (limit F).weakRows (limitFiberIndex F n j)) := by
      rintro μ ⟨z, ⟨_, ⟨j, rfl⟩⟩, rfl⟩
      exact ⟨j, congrArg (limit F).weakRows (limitFiberIndex_nonroot F n j)⟩
    have hf := wolfeFamily_mono (limit F).pointAtomicModel le_rfl hs ξ hl
    have hf' : ((limit F).weakRows (limitFiberIndex F n j), U) ∈
        wolfeFamily (limit F).pointAtomicModel ε
          (range (fun j => (limit F).weakRows (limitFiberIndex F n j))) ξ := by
      convert hf using 1
      exact congrArg (fun z => ((limit F).weakRows z, U)) (limitFiberIndex_nonroot F n j)
    have hi := limitFiber_wolfe_pullback F n ξ j U hf'
    rw [hF n] at hi
    exact hi.elim

theorem limit_wolfe_empty {ε : ℝ} (hε : 0 < ε) (ξ : Ordinal)
    (hc : (ξ + 1).card ≤ Cardinal.aleph0)
    (hF : ∀ n, wolfeFamily (F n).pointAtomicModel ε (range (F n).weakRows) ξ = ∅) :
    wolfeFamily (limit F).pointAtomicModel ε (range (limit F).weakRows) (ξ + 1) = ∅ := by
  apply wolfeFamily_empty_of_shifted_derived_empty (limit F).pointAtomicModel hε
    (range (limit F).weakRows) ξ 1 hc
  apply eq_empty_iff_forall_notMem.mpr
  intro μ hμ
  have hh := ordinalDerived_mono (limit_wolfeMeasures_subset_root F ξ hF) (1 : Ordinal) hμ
  have he : ordinalDerived ({(limit F).weakRows ∞} : Set _) (1 : Ordinal) = ∅ := by
    rw [show (1 : Ordinal) = succ 0 by simp, ordinalDerived_succ, ordinalDerived_zero]
    exact derivedSet_eq_empty_of_finite (finite_singleton _)
  rw [he] at hh
  exact hh

end AlspachCompactRows

variable {𝕜 B : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [CompactSpace B] [T2Space B] [Countable B] (p : B)

theorem alspachOmega_wolfe_bound
    (hB : ordinalDerived (univ : Set B) ((ω : Ordinal.{0}) + 1) = ∅)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) (hpow : 1 < (2 : ℝ) ^ m * ε) :
    wolfeFamily (alspachOmegaCompactRows (𝕜 := 𝕜) B p).pointAtomicModel ε
      (range (alspachOmegaCompactRows (𝕜 := 𝕜) B p).weakRows)
      ((ω : Ordinal.{0}) * ((m + 1 : ℕ) : Ordinal) + 1) = ∅ := by
  have hc : (ω * ((m + 1 : ℕ) : Ordinal) + 1).card ≤ Cardinal.aleph0 := by
    apply (Ordinal.card_le_card (alspach_next_block_add_one_lt_omega_sq m).le).trans
    simp only [alspach_omega_sq_eq_mul, Ordinal.card_mul, Ordinal.card_omega0,
      Cardinal.aleph0_mul_aleph0, le_refl]
  apply AlspachCompactRows.limit_wolfe_empty (alspachFiniteCompactRows B p) hε _ hc
  intro n
  apply (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).wolfe_empty_mono
    ((Ordinal.card_le_card (show ω * ((m + 1 : ℕ) : Ordinal) ≤
      ω * ((m + 1 : ℕ) : Ordinal) + 1 from le_self_add)).trans hc)
    (alspachRankBound_lt_next_block m n).le
  exact alspachFinite_wolfe_bound p hB m ε hpow n

theorem alspachOmega_wolfe_omega_sq_empty
    (hB : ordinalDerived (univ : Set B) ((ω : Ordinal.{0}) + 1) = ∅)
    {ε : ℝ} (hε : 0 < ε) :
    wolfeFamily (alspachOmegaCompactRows (𝕜 := 𝕜) B p).pointAtomicModel ε
      (range (alspachOmegaCompactRows (𝕜 := 𝕜) B p).weakRows) ((ω : Ordinal.{0}) ^ (2 : Ordinal)) = ∅ := by
  obtain ⟨m, hm⟩ := alspach_exists_doubling_depth hε
  apply (alspachOmegaCompactRows (𝕜 := 𝕜) B p).wolfe_empty_mono
    (by simp only [alspach_omega_sq_eq_mul, Ordinal.card_mul, Ordinal.card_omega0,
      Cardinal.aleph0_mul_aleph0, le_refl])
    (alspach_next_block_add_one_lt_omega_sq m).le
  exact alspachOmega_wolfe_bound p hB m hε hm

end Posets
