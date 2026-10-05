import JFA.FinitePowerUniqueness
import JFA.AmplifiedXIdeal
import JFA.CZeroComplementedSubspaces

/-! The three kinds of complemented model are pairwise distinct, and the
finite exponent is unique. Separability distinguishes c₀. Tensor cancellation
and scalar finite dimension distinguish the finite powers from each other
and from the whole amplified space. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem Isomorphic.symm (h : Isomorphic 𝕜 E F) : Isomorphic 𝕜 F E := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem Isomorphic.trans (h : Isomorphic 𝕜 E F) (k : Isomorphic 𝕜 F G) :
    Isomorphic 𝕜 E G := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := k
  exact ⟨e.trans f⟩

theorem isomorphic_separableSpace (h : Isomorphic 𝕜 E F) (hE : SeparableSpace E) :
    SeparableSpace F := by
  letI := hE
  obtain ⟨e⟩ := h
  have hr := isSeparable_range e.continuous
  rw [Set.range_eq_univ.mpr e.surjective] at hr
  exact isSeparable_univ_iff.mp hr

theorem not_isomorphic_cZero_of_nonseparable (hE : ¬ SeparableSpace E) :
    ¬ Isomorphic 𝕜 (cZero 𝕜) E := fun h =>
  hE (isomorphic_separableSpace h (czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)))

theorem finitePower_nonseparable (hE : ¬ SeparableSpace E) (n : ℕ) :
    ¬ SeparableSpace (Fin (n + 1) → E) := by
  intro h
  letI := h
  have hr : IsSeparable (range (fun f : Fin (n + 1) → E => f 0)) :=
    isSeparable_range (continuous_apply 0)
  have hsur : Function.Surjective (fun f : Fin (n + 1) → E => f 0) :=
    fun x => ⟨fun _ => x, rfl⟩
  rw [Set.range_eq_univ.mpr hsur] at hr
  exact hE (isSeparable_univ_iff.mp hr)

section FiniteVersusCountable
universe u
variable {𝕜' : Type u} [RCLike 𝕜'] {X : Type u}
  [NormedAddCommGroup X] [NormedSpace 𝕜' X] [CompleteSpace X]

theorem not_isomorphic_finitePower_cZeroSum (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜' X) (n : ℕ) :
    ¬ Isomorphic 𝕜' (Fin n → X) C₀(ℕ, X) := by
  rintro ⟨e⟩
  letI := czero_countable_discrete_separable (𝕜 := 𝕜') (A := ℕ)
  have hTensor : Isomorphic 𝕜' (InjectiveTensor 𝕜' (Fin n → 𝕜') X)
      (InjectiveTensor 𝕜' (cZero 𝕜') X) :=
    ⟨(finitePowerTensorEquiv (𝕜 := 𝕜') (D := Fin n) (X := X)).trans
      (e.trans (tensorCzeroDiscreteEquiv (𝕜 := 𝕜') (A := ℕ) (X := X)).toContinuousLinearEquiv.symm)⟩
  obtain ⟨f⟩ := (corollary_1_2 (𝕜 := 𝕜') (E := Fin n → 𝕜')
    (F := cZero 𝕜') (X := X) (inferInstance : SeparableSpace (Fin n → 𝕜'))
    (inferInstance : SeparableSpace (cZero 𝕜')) hX hfew).mp hTensor
  exact JLMS.cZero_not_finiteDimensional 𝕜'
    (FiniteDimensional.of_injective f.symm.toLinearEquiv.toLinearMap f.symm.injective)

end FiniteVersusCountable
variable {𝒜 : Set (Set ℕ)}

theorem amplified_nonseparable (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜) :
    ¬ SeparableSpace (AmplifiedMrowka 𝕜 𝒜) := by
  intro h
  letI := h
  obtain ⟨J, R, hRJ, _⟩ := amplified_exists_X_coordinate_retract (𝕜 := 𝕜) h𝒜
  have hsur : Function.Surjective R := fun x => ⟨J x, congrArg (fun L => L x) hRJ⟩
  have hr := isSeparable_range R.continuous
  rw [Set.range_eq_univ.mpr hsur] at hr
  exact mrowka_czero_nonseparable h𝒜 hc (isSeparable_univ_iff.mp hr)

theorem not_isomorphic_finitePower_amplified (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) (n : ℕ) :
    ¬ Isomorphic 𝕜 (Fin n → MrowkaCZero 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) := by
  intro h
  letI := mrowka_t2Space h𝒜
  have he : Isomorphic 𝕜 (AmplifiedMrowka 𝕜 𝒜) C₀(ℕ, MrowkaCZero 𝕜 𝒜) :=
    ⟨(czeroDiscreteProductEquiv (𝕜 := 𝕜) (D := ℕ) (L := Mrowka 𝒜)).toContinuousLinearEquiv⟩
  exact not_isomorphic_finitePower_cZeroSum (mrowka_czero_nonseparable h𝒜 hc) hfew n (h.trans he)

theorem amplified_model_unique (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {c d : ComplementedModel}
    (hWc : IsModel 𝕜 (MrowkaCZero 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) W c)
    (hWd : IsModel 𝕜 (MrowkaCZero 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) W d) : c = d := by
  cases c with
  | c0 =>
    cases d with
    | c0 => rfl
    | finitePower n =>
      exact False.elim (not_isomorphic_cZero_of_nonseparable
        (finitePower_nonseparable (mrowka_czero_nonseparable h𝒜 hc) n) (hWc.symm.trans hWd))
    | whole =>
      exact False.elim
        (not_isomorphic_cZero_of_nonseparable (amplified_nonseparable h𝒜 hc) (hWc.symm.trans hWd))
  | finitePower m =>
    cases d with
    | c0 =>
      exact False.elim (not_isomorphic_cZero_of_nonseparable
        (finitePower_nonseparable (mrowka_czero_nonseparable h𝒜 hc) m) (hWd.symm.trans hWc))
    | finitePower n =>
      have h := (finitePower_isomorphic_iff (mrowka_czero_nonseparable h𝒜 hc) hfew (m + 1) (n + 1)).mp
        (hWc.symm.trans hWd)
      exact congrArg ComplementedModel.finitePower (Nat.add_right_cancel h)
    | whole =>
      exact False.elim (not_isomorphic_finitePower_amplified h𝒜 hc hfew (m + 1)
        (hWc.symm.trans hWd))
  | whole =>
    cases d with
    | c0 =>
      exact False.elim
        (not_isomorphic_cZero_of_nonseparable (amplified_nonseparable h𝒜 hc) (hWd.symm.trans hWc))
    | finitePower n =>
      exact False.elim (not_isomorphic_finitePower_amplified h𝒜 hc hfew (n + 1)
        (hWd.symm.trans hWc))
    | whole => rfl

end JFA
