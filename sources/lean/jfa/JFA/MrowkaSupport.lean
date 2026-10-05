import JFA.MrowkaTopology
import JFA.CZeroProduct

/-! Countable supports for functions and separable sets of functions on the
actual product with K_𝒜. A compact tail has compact projection on K_𝒜, hence
meets only finitely many family points. No compactness assumption on the first
factor is needed; in particular these results apply to the discrete omega. -/

noncomputable section
open TopologicalSpace Topology Filter Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {M : Type*} [TopologicalSpace M]

def mrowkaFunctionSupport (f : C₀(M × Mrowka 𝒜, 𝕜)) : Set 𝒜 :=
  {A | ∃ m : M, f (m, Sum.inr A) ≠ 0}

def mrowkaSetSupport (F : Set C₀(M × Mrowka 𝒜, 𝕜)) : Set 𝒜 :=
  {A | ∃ f ∈ F, A ∈ mrowkaFunctionSupport f}

theorem mrowka_function_support_countable (f : C₀(M × Mrowka 𝒜, 𝕜)) :
    (mrowkaFunctionSupport f).Countable := by
  choose K hK htail using fun n : ℕ => czero_compact_tail f (1 / (n + 1 : ℝ)) (by positivity)
  let S : ℕ → Set 𝒜 := fun n => (Sum.inr : 𝒜 → Mrowka 𝒜) ⁻¹' (Prod.snd '' K n)
  have hS : ∀ n, (S n).Finite := fun n =>
    mrowka_compact_meets_remainder_finitely ((hK n).image continuous_snd)
  apply (Set.countable_iUnion (fun n => (hS n).countable)).mono
  rintro A ⟨m, hm⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hm)
  have hp : (m, Sum.inr A) ∈ K n := by
    by_contra hp
    exact (htail n _ hp).not_ge hn.le
  exact mem_iUnion.mpr ⟨n, ⟨(m, Sum.inr A), hp, rfl⟩⟩

theorem mrowka_set_support_countable {F : Set C₀(M × Mrowka 𝒜, 𝕜)}
    (hF : IsSeparable F) : (mrowkaSetSupport F).Countable := by
  obtain ⟨D, hD, hFD⟩ := hF
  let S : Set 𝒜 := ⋃ f ∈ D, mrowkaFunctionSupport f
  have hS : S.Countable := hD.biUnion (fun f _ => mrowka_function_support_countable f)
  apply hS.mono
  rintro A ⟨f, hf, m, hm⟩
  by_contra hAS
  have hzero : D ⊆ {g : C₀(M × Mrowka 𝒜, 𝕜) | g (m, Sum.inr A) = 0} := by
    intro g hg
    by_contra hgm
    exact hAS (mem_iUnion₂.mpr ⟨g, hg, ⟨m, hgm⟩⟩)
  have heval : Continuous (fun g : C₀(M × Mrowka 𝒜, 𝕜) => g (m, Sum.inr A)) :=
    BoundedContinuousFunction.continuous_eval_const.comp ZeroAtInftyContinuousMap.isometry_toBCF.continuous
  exact hm (closure_minimal hzero (isClosed_eq heval continuous_const) (hFD hf))

theorem mrowka_czero_nonseparable (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜) :
    ¬ SeparableSpace (MrowkaCZero 𝕜 𝒜) := by
  letI := mrowka_t2Space h𝒜
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  exact czero_nonseparable_of_nonmetrizable (𝕜 := 𝕜) (mrowka_nonmetrizable h𝒜 hc)

end JFA
