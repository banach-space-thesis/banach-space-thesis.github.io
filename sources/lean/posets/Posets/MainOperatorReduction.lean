import Posets.AdmissionFactorization
import Posets.AcceptanceAdmission

/-! Analytic reductions in step 5 of the proof of Theorem 1.1. These do not
assume or assert the still-open transfinite construction of the families. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ 𝒞 : Set (Set ℕ)}

theorem reducedMatrix_column_tendsto (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (n : ℕ) (B : ℬ) :
    Tendsto (fun k => reducedMatrix 𝕜 T k n) (Along B.val)
      (𝓝 (T (isolatedVector 𝕜 𝒜 n) (Sum.inr B))) := by
  exact (T (isolatedVector 𝕜 𝒜 n)).continuous.continuousAt.tendsto.comp
    (family_tendsto_along ℬ B)

theorem reducedMatrix_not_undermined_outside (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ)
    {B : Set ℕ} (hB : B ∉ ℬ) (hbig : IsAlmostDisjoint (insert B ℬ)) :
    ¬ Undermines 𝕜 B (reducedMatrix 𝕜 T) := by
  rintro ⟨n, hn⟩
  apply hn
  have h := (zero_at_infty (T (isolatedVector 𝕜 𝒜 n))).comp
    (natural_tendsto_cocompact hB hbig)
  exact h.congr (fun k => (matrixAction_singleton (reducedMatrix 𝕜 T) n k).symm)

/-- For any source subfamily of a common almost disjoint family, only
countably many members undermine a reduced matrix. -/
theorem reducedMatrix_undermining_countable (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ)
    (hbig : IsAlmostDisjoint (𝒞 ∪ ℬ)) :
    {B ∈ 𝒞 | Undermines 𝕜 B (reducedMatrix 𝕜 T)}.Countable := by
  let Q : Set (Set ℕ) := ⋃ n : ℕ, Subtype.val '' familySupport 𝕜 (T (isolatedVector 𝕜 𝒜 n))
  have hQ : Q.Countable := Set.countable_iUnion
    (fun n => (familySupport_countable (T (isolatedVector 𝕜 𝒜 n))).image Subtype.val)
  apply hQ.mono
  rintro B ⟨hBC, hB⟩
  have hBB : B ∈ ℬ := by
    by_contra hn
    apply reducedMatrix_not_undermined_outside T hn ?_ hB
    have hs : insert B ℬ ⊆ 𝒞 ∪ ℬ := by
      intro A hA
      rcases hA with rfl | hA
      · exact Or.inl hBC
      · exact Or.inr hA
    exact ⟨fun A hA => hbig.1 A (hs hA),
      fun A hA C hC hAC => hbig.2 A (hs hA) C (hs hC) hAC⟩
  obtain ⟨n, hn⟩ := hB
  apply Set.mem_iUnion.mpr
  refine ⟨n, ⟨⟨B, hBB⟩, ?_, rfl⟩⟩
  change T (isolatedVector 𝕜 𝒜 n) (Sum.inr ⟨B, hBB⟩) ≠ 0
  intro hz
  apply hn
  have h := (reducedMatrix_column_tendsto T n ⟨B, hBB⟩).congr
    (fun k => (matrixAction_singleton (reducedMatrix 𝕜 T) n k).symm)
  simpa only [hz] using h

/-- Subtracting a scalar identity changes each column at just one coordinate,
so it does not change the undermining predicate. -/
theorem undermines_sub_scalar_identity_iff (M : ScalarMatrix 𝕜) (a : 𝕜) (B : Set ℕ) :
    Undermines 𝕜 B (M - a • identityMatrix 𝕜) ↔ Undermines 𝕜 B M := by
  have hcol (n : ℕ) :
      (matrixAction 𝕜 (M - a • identityMatrix 𝕜) (indicator 𝕜 {n})) =ᶠ[Along B]
        matrixAction 𝕜 M (indicator 𝕜 {n}) := by
    have hne : ∀ᶠ k in Along B, k ≠ n :=
      Filter.mem_of_superset (Filter.mem_inf_of_left (Set.finite_singleton n).compl_mem_cofinite)
        (fun _ h => h)
    filter_upwards [hne] with k hk
    simp [matrixAction_singleton, identityMatrix, hk]
  unfold Undermines
  exact exists_congr (fun n => not_congr (tendsto_congr' (hcol n)))

end Posets
