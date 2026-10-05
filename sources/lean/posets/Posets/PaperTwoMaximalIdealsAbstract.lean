import Posets.NonfactorizationCompressionIdeal
import PosetsCommon.MaximalIdeals
import Mathlib.Analysis.Normed.Operator.Prod

/-! The block-algebra argument behind the opening observation in Section 3.
The full operator algebra on a direct sum is used, including both off-diagonal
corners. Mutual failure of complemented embeddings distinguishes its two ideals. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def paperFirstProjection : E × F →L[𝕜] E × F :=
  (ContinuousLinearMap.inl 𝕜 E F).comp (ContinuousLinearMap.fst 𝕜 E F)

def paperSecondProjection : E × F →L[𝕜] E × F :=
  (ContinuousLinearMap.inr 𝕜 E F).comp (ContinuousLinearMap.snd 𝕜 E F)

theorem paper_projections_add :
    paperFirstProjection (𝕜 := 𝕜) (E := E) (F := F) + paperSecondProjection =
      ContinuousLinearMap.id 𝕜 (E × F) := by
  ext x <;> simp [paperFirstProjection, paperSecondProjection]

theorem paper_projection_factor (X Y : Type*) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (i : X →L[𝕜] Y) (p : Y →L[𝕜] X) (hp : p.comp i = ContinuousLinearMap.id 𝕜 X) :
    ¬DoesNotFactorIdentity 𝕜 (i.comp p) X := by
  intro h
  apply h
  refine ⟨i, p, ?_⟩
  rw [ContinuousLinearMap.comp_assoc, hp, ContinuousLinearMap.comp_id, hp]

theorem paper_corner_mem_of_factor {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {I : Set (Y →L[𝕜] Y)} (hI : IsAlgebraIdeal 𝕜 I) {T : Y →L[𝕜] Y}
    (hT : T ∈ I) (hf : ¬DoesNotFactorIdentity 𝕜 T X)
    (i : X →L[𝕜] Y) (p : Y →L[𝕜] X) : i.comp p ∈ I := by
  classical
  obtain ⟨A, B, hAB⟩ := not_not.mp hf
  have hm := (hI.2.2.2 (A.comp p) T hT).2
  have hn := (hI.2.2.2 (i.comp B) _ hm).1
  have he : (i.comp B) * (T * (A.comp p)) = i.comp p := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc T A p,
      ← ContinuousLinearMap.comp_assoc B (T.comp A) p, hAB]
    simp
  exact he ▸ hn

theorem paper_proper_ideal_subset_one_corner {I : Set (E × F →L[𝕜] E × F)}
    (hI : IsAlgebraIdeal 𝕜 I) (hp : I ≠ univ) :
    I ⊆ {T | DoesNotFactorIdentity 𝕜 T E} ∨
      I ⊆ {T | DoesNotFactorIdentity 𝕜 T F} := by
  classical
  by_contra h
  obtain ⟨hE, hF⟩ := not_or.mp h
  obtain ⟨T, hT, hTE⟩ := Set.not_subset.mp hE
  obtain ⟨U, hU, hUF⟩ := Set.not_subset.mp hF
  have he := paper_corner_mem_of_factor hI hT hTE
    (ContinuousLinearMap.inl 𝕜 E F) (ContinuousLinearMap.fst 𝕜 E F)
  have hf := paper_corner_mem_of_factor hI hU hUF
    (ContinuousLinearMap.inr 𝕜 E F) (ContinuousLinearMap.snd 𝕜 E F)
  have hid : (1 : E × F →L[𝕜] E × F) ∈ I := by
    change ContinuousLinearMap.id 𝕜 (E × F) ∈ I
    rw [← paper_projections_add]
    exact hI.2.1 _ he _ hf
  exact hp (hI.eq_univ_of_unit_mem hid isUnit_one)

theorem paper_first_projection_nonfactor_other
    (h : ¬∃ A : F →L[𝕜] E, ∃ B : E →L[𝕜] F,
      B.comp A = ContinuousLinearMap.id 𝕜 F) :
    DoesNotFactorIdentity 𝕜 (paperFirstProjection (E := E) (F := F)) F := by
  rintro ⟨A, B, hAB⟩
  apply h
  refine ⟨(ContinuousLinearMap.fst 𝕜 E F).comp A,
    B.comp (ContinuousLinearMap.inl 𝕜 E F), ?_⟩
  simpa only [paperFirstProjection, ContinuousLinearMap.comp_assoc] using hAB

theorem paper_second_projection_nonfactor_other
    (h : ¬∃ A : E →L[𝕜] F, ∃ B : F →L[𝕜] E,
      B.comp A = ContinuousLinearMap.id 𝕜 E) :
    DoesNotFactorIdentity 𝕜 (paperSecondProjection (E := E) (F := F)) E := by
  rintro ⟨A, B, hAB⟩
  apply h
  refine ⟨(ContinuousLinearMap.snd 𝕜 E F).comp A,
    B.comp (ContinuousLinearMap.inr 𝕜 E F), ?_⟩
  simpa only [paperSecondProjection, ContinuousLinearMap.comp_assoc] using hAB

theorem paper_two_maximal_ideals_of_pfp [CompleteSpace E] [CompleteSpace F]
    [Nontrivial E] [Nontrivial F] (hE : HasPFP 𝕜 E) (hF : HasPFP 𝕜 F)
    (hEF : ¬∃ A : E →L[𝕜] F, ∃ B : F →L[𝕜] E,
      B.comp A = ContinuousLinearMap.id 𝕜 E)
    (hFE : ¬∃ A : F →L[𝕜] E, ∃ B : E →L[𝕜] F,
      B.comp A = ContinuousLinearMap.id 𝕜 F) :
    {T : E × F →L[𝕜] E × F | DoesNotFactorIdentity 𝕜 T E} ≠
      {T | DoesNotFactorIdentity 𝕜 T F} ∧
    ∀ I : Set (E × F →L[𝕜] E × F), IsMaximalAlgebraIdeal 𝕜 I ↔
      I = {T | DoesNotFactorIdentity 𝕜 T E} ∨
        I = {T | DoesNotFactorIdentity 𝕜 T F} := by
  let J : Set (E × F →L[𝕜] E × F) := {T | DoesNotFactorIdentity 𝕜 T E}
  let K : Set (E × F →L[𝕜] E × F) := {T | DoesNotFactorIdentity 𝕜 T F}
  have hJ : IsClosedIdeal 𝕜 J := isClosedIdeal_nonfactorization_of_hasPFP hE
  have hK : IsClosedIdeal 𝕜 K := isClosedIdeal_nonfactorization_of_hasPFP hF
  have hen : paperFirstProjection (𝕜 := 𝕜) (E := E) (F := F) ∉ J :=
    paper_projection_factor E (E × F) _ _ (by ext x; simp)
  have hfn : paperSecondProjection (𝕜 := 𝕜) (E := E) (F := F) ∉ K :=
    paper_projection_factor F (E × F) _ _ (by ext x; simp)
  have he : paperFirstProjection (𝕜 := 𝕜) (E := E) (F := F) ∈ K :=
    paper_first_projection_nonfactor_other hFE
  have hf : paperSecondProjection (𝕜 := 𝕜) (E := E) (F := F) ∈ J :=
    paper_second_projection_nonfactor_other hEF
  have hJK : ¬J ⊆ K := fun h => hfn (h hf)
  have hKJ : ¬K ⊆ J := fun h => hen (h he)
  have hjp : J ≠ univ := fun h => hen (h ▸ Set.mem_univ _)
  have hkp : K ≠ univ := fun h => hfn (h ▸ Set.mem_univ _)
  have hjm : IsMaximalAlgebraIdeal 𝕜 J := by
    refine ⟨hJ.2, hjp, ?_⟩
    intro I hI hJI
    by_cases hi : I = univ
    · exact Or.inr hi
    · rcases paper_proper_ideal_subset_one_corner hI hi with h | h
      · exact Or.inl (Subset.antisymm h hJI)
      · exact (hJK (hJI.trans h)).elim
  have hkm : IsMaximalAlgebraIdeal 𝕜 K := by
    refine ⟨hK.2, hkp, ?_⟩
    intro I hI hKI
    by_cases hi : I = univ
    · exact Or.inr hi
    · rcases paper_proper_ideal_subset_one_corner hI hi with h | h
      · exact (hKJ (hKI.trans h)).elim
      · exact Or.inl (Subset.antisymm h hKI)
  refine ⟨fun h => hJK h.subset, ?_⟩
  intro I
  constructor
  · intro hi
    rcases paper_proper_ideal_subset_one_corner hi.1 hi.2.1 with h | h
    · exact Or.inl ((hi.2.2 J hJ.2 h).resolve_right hjp).symm
    · exact Or.inr ((hi.2.2 K hK.2 h).resolve_right hkp).symm
  · rintro (rfl | rfl)
    · exact hjm
    · exact hkm

end Posets
