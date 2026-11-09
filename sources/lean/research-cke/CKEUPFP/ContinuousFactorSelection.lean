import CKEUPFP.Selection
import CKEUPFP.StrongOperatorBall
import CKEUPFP.OperatorFields
import CKEUPFP.FactorBalancing

/-!
# Continuous bounded factor selection

This proves the operator-valued selection lemma in Section 2. We use the
continuous Cantor lifting theorem on the genuine closed factorisation relation
in Polish bounded strong operator balls.
-/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped NNReal

namespace CKEUPFP

open StrongOperatorBall

variable {𝕜 P E : Type*} [RCLike 𝕜]
  [TopologicalSpace P] [PolishSpace P] [Uncountable P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [SeparableSpace E]

/-- The two complementary alternatives, with `false` denoting `A` and
`true` denoting `I - A`, as in the paper's sides zero and one. -/
def factorSelectionSide (σ : Bool) (A : E →L[𝕜] E) : E →L[𝕜] E :=
  if σ then ContinuousLinearMap.id 𝕜 E - A else A

omit [TopologicalSpace P] [PolishSpace P] [Uncountable P] [CompleteSpace E] [SeparableSpace E] in
@[simp] theorem factorSelectionSide_false (A : E →L[𝕜] E) :
    factorSelectionSide false A = A := rfl

omit [TopologicalSpace P] [PolishSpace P] [Uncountable P] [CompleteSpace E] [SeparableSpace E] in
@[simp] theorem factorSelectionSide_true (A : E →L[𝕜] E) :
    factorSelectionSide true A = ContinuousLinearMap.id 𝕜 E - A := rfl

/-- Pointwise uniformly bounded identity factorisations of `A(t)` or
`I-A(t)` admit a fixed side and strongly continuous factors after restriction
along an embedded Cantor set. The factors here are actual continuous linear
maps, with the same individual norm bounds `r` as in the hypothesis. -/
theorem continuous_factor_selection
    {M r : ℝ≥0} (A : P → StrongOperatorBall 𝕜 E M) (hA : Continuous A)
    (hpoint : ∀ t : P, ∃ σ : Bool, ∃ L R : E →L[𝕜] E,
      (L.comp (factorSelectionSide σ (A t).operator)).comp R =
        ContinuousLinearMap.id 𝕜 E ∧ ‖L‖ ≤ r ∧ ‖R‖ ≤ r) :
    ∃ (σ : Bool) (e : (ℕ → Bool) → P) (L R : (ℕ → Bool) → E →L[𝕜] E),
      Continuous e ∧ Function.Injective e ∧
      IsStronglyContinuous L ∧ IsStronglyContinuous R ∧
      (∀ t, ‖L t‖ ≤ r ∧ ‖R t‖ ≤ r) ∧
      ∀ t, ((L t).comp (factorSelectionSide σ (A (e t)).operator)).comp (R t) =
        ContinuousLinearMap.id 𝕜 E := by
  classical
  let Aσ (σ : Bool) (t : P) : StrongOperatorBall 𝕜 E (1 + M) :=
    if σ then complement (A t) else inclusion (by simp) (A t)
  have hAσ (σ : Bool) : Continuous (Aσ σ) := by
    cases σ
    · exact StrongOperatorBall.continuous_inclusion (by simp : M ≤ 1 + M) |>.comp hA
    · exact continuous_complement.comp hA
  have hAσop (σ : Bool) (t : P) : (Aσ σ t).operator =
      factorSelectionSide σ (A t).operator := by
    cases σ <;> rfl
  let D := P × (StrongOperatorBall 𝕜 E r × StrongOperatorBall 𝕜 E r)
  let Γ (σ : Bool) : Set D :=
    {z | ∀ x : E, z.2.1.operator ((Aσ σ z.1).operator (z.2.2.operator x)) = x}
  have hΓclosed (σ : Bool) : IsClosed (Γ σ) := by
    change IsClosed {z : D | ∀ x : E,
      z.2.1.operator ((Aσ σ z.1).operator (z.2.2.operator x)) = x}
    simp only [setOf_forall]
    apply isClosed_iInter
    intro x
    have hR : Continuous (fun z : D => z.2.2.operator x) :=
      (continuous_eval x).comp (continuous_snd.comp continuous_snd)
    have hAR : Continuous (fun z : D => (Aσ σ z.1).operator (z.2.2.operator x)) :=
      continuous_apply.comp ((hAσ σ |>.comp continuous_fst).prodMk hR)
    have hLAR : Continuous (fun z : D =>
        z.2.1.operator ((Aσ σ z.1).operator (z.2.2.operator x))) :=
      continuous_apply.comp ((continuous_fst.comp continuous_snd).prodMk hAR)
    exact isClosed_eq hLAR continuous_const
  have hcover : (Set.univ : Set P) ⊆ ⋃ σ : Bool, Prod.fst '' Γ σ := by
    intro t _
    obtain ⟨σ, L, R, hfactor, hL, hR⟩ := hpoint t
    refine Set.mem_iUnion.mpr ⟨σ, ⟨(t, (⟨L, hL⟩, ⟨R, hR⟩)), ?_, rfl⟩⟩
    intro x
    have hx := congrArg (fun F : E →L[𝕜] E => F x) hfactor
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hAσop] using hx
  obtain ⟨σ, hσunc⟩ : ∃ σ : Bool, ¬ (Prod.fst '' Γ σ).Countable := by
    by_contra! h
    exact Set.not_countable_univ (α := P) ((Set.countable_iUnion h).mono hcover)
  obtain ⟨e, s, he, heinj, hs, hes⟩ :=
    closed_relation_continuous_cantor_selection (hΓclosed σ) hσunc
  let L := fun t => (s t).1.operator
  let R := fun t => (s t).2.operator
  have hLstrong : IsStronglyContinuous L :=
    StrongOperatorBall.continuous_iff.mp (continuous_fst.comp hs)
  have hRstrong : IsStronglyContinuous R :=
    StrongOperatorBall.continuous_iff.mp (continuous_snd.comp hs)
  refine ⟨σ, e, L, R, he, heinj, hLstrong, hRstrong,
    fun t => ⟨(s t).1.norm_le, (s t).2.norm_le⟩, ?_⟩
  intro t
  ext x
  change (s t).1.operator
    (factorSelectionSide σ (A (e t)).operator ((s t).2.operator x)) = x
  rw [← hAσop]
  exact hes t x

/-- The selection theorem applied directly to a strongly continuous field of
actual operators and the `C`-PFP assumption. Balancing gives the precise
individual factor bound `√C` used in Section 4. -/
theorem continuous_cp_fp_factor_selection
    {M : ℝ≥0} {C : ℝ} (A : P → E →L[𝕜] E)
    (hA : IsStronglyContinuous A) (hbounded : ∀ t, ‖A t‖ ≤ M)
    (hC : HasCPFP 𝕜 E C) :
    ∃ (σ : Bool) (e : (ℕ → Bool) → P) (L R : (ℕ → Bool) → E →L[𝕜] E),
      Continuous e ∧ Function.Injective e ∧
      IsStronglyContinuous L ∧ IsStronglyContinuous R ∧
      (∀ t, ‖L t‖ ≤ Real.sqrt C ∧ ‖R t‖ ≤ Real.sqrt C) ∧
      ∀ t, ((L t).comp (factorSelectionSide σ (A (e t)))).comp (R t) =
        ContinuousLinearMap.id 𝕜 E := by
  let Ab : P → StrongOperatorBall 𝕜 E M := fun t => ⟨A t, hbounded t⟩
  have hAb : Continuous Ab := StrongOperatorBall.continuous_iff.mpr hA
  let r : ℝ≥0 := ⟨Real.sqrt C, Real.sqrt_nonneg C⟩
  have hpoint : ∀ t : P, ∃ σ : Bool, ∃ L R : E →L[𝕜] E,
      (L.comp (factorSelectionSide σ (Ab t).operator)).comp R =
        ContinuousLinearMap.id 𝕜 E ∧ ‖L‖ ≤ r ∧ ‖R‖ ≤ r := by
    intro t
    rcases hC.exists_balanced_factorisation (A t) with h | h
    · obtain ⟨L, R, hfactor, hL, hR⟩ := h
      exact ⟨false, L, R, hfactor, hL, hR⟩
    · obtain ⟨L, R, hfactor, hL, hR⟩ := h
      exact ⟨true, L, R, hfactor, hL, hR⟩
  exact continuous_factor_selection Ab hAb hpoint

end CKEUPFP
