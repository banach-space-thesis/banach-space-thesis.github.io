import JFA.CompactFunctionModels
import JLMS.CZeroTools
import ThesisCommon.Analysis.CompactMetricMilutin
import ThesisCommon.Analysis.CountableCompactClassification
import ThesisCommon.Analysis.OrdinalBakerClassification
import ThesisCommon.Analysis.ContinuousMapPullback

/-! For an infinite compact metric space M, the actual C(M) is isomorphic
to its c₀-sum. In the countable case we use the compact ordinal model,
repeat its smaller ordinal blocks, and remove the scalar at infinity. -/

noncomputable section
set_option maxHeartbeats 1500000
open Filter Set TopologicalSpace Topology Order ThesisCommon
open scoped ZeroAtInfty
namespace JFA
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

private def onePointCzeroProductEquiv (L : Type*) [TopologicalSpace L] [T2Space L] :
    C(OnePoint L, 𝕜) ≃L[𝕜] (𝕜 × C₀(L, 𝕜)) := by
  let part (f : C(OnePoint L, 𝕜)) : C₀(L, 𝕜) :=
    { toFun := fun x => f (x : OnePoint L) - f OnePoint.infty
      continuous_toFun := ((OnePoint.continuous_iff f).mp f.continuous).2.sub continuous_const
      zero_at_infty' := by
        rw [← coclosedCompact_eq_cocompact]
        simpa only [sub_self] using
          ((OnePoint.continuous_iff f).mp f.continuous).1.sub
            (tendsto_const_nhds (x := f OnePoint.infty)) }
  let assemble (z : 𝕜 × C₀(L, 𝕜)) : C(OnePoint L, 𝕜) :=
    OnePoint.continuousMapMk ⟨fun x => z.1 + z.2 x, continuous_const.add z.2.continuous⟩
      z.1 (by
        rw [coclosedCompact_eq_cocompact]
        simpa only [add_zero] using tendsto_const_nhds.add z.2.zero_at_infty')
  refine LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun f => (f OnePoint.infty, part f)
      invFun := assemble
      map_add' := by
        intro f g
        apply Prod.ext
        · rfl
        · ext x
          change (f x + g x) - (f OnePoint.infty + g OnePoint.infty) =
            (f x - f OnePoint.infty) + (g x - g OnePoint.infty)
          abel
      map_smul' := by
        intro a f
        apply Prod.ext
        · rfl
        · ext x
          exact (smul_sub a (f x) (f OnePoint.infty)).symm
      left_inv := by
        intro f
        ext x
        refine OnePoint.rec rfl (fun l => ?_) x
        change f OnePoint.infty + (f l - f OnePoint.infty) = f l
        abel
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · ext x
          exact add_sub_cancel_left z.1 (z.2 x) } 2 2 ?_ ?_
  · intro f
    change max ‖f OnePoint.infty‖ ‖part f‖ ≤ 2 * ‖f‖
    refine max_le ((f.norm_coe_le_norm _).trans ?_) ?_
    · linarith [norm_nonneg f]
    · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
      intro x
      change ‖f x - f OnePoint.infty‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm OnePoint.infty])
  · intro z
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    refine OnePoint.rec ?_ (fun l => ?_) x
    · change ‖z.1‖ ≤ _
      linarith [norm_fst_le z, norm_nonneg z]
    · change ‖z.1 + z.2 l‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      rw [two_mul]
      exact add_le_add (norm_fst_le z) ((z.2.toBCF.norm_coe_le_norm l).trans (norm_snd_le z))

private def sumContinuousEquiv (K L : Type*) [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace L] [CompactSpace L] :
    C(K ⊕ L, 𝕜) ≃L[𝕜] (C(K, 𝕜) × C(L, 𝕜)) := by
  refine LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun f => (f.comp ⟨Sum.inl, continuous_inl⟩, f.comp ⟨Sum.inr, continuous_inr⟩)
      invFun := fun p => ⟨Sum.elim p.1 p.2, p.1.continuous.sumElim p.2.continuous⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := by intro f; ext x; cases x <;> rfl
      right_inv := by intro p; apply Prod.ext <;> ext x <;> rfl } 1 1 ?_ ?_
  · intro f
    rw [one_mul]
    exact max_le ((ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x => f.norm_coe_le_norm (Sum.inl x))
      ((ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x => f.norm_coe_le_norm (Sum.inr x))
  · intro p
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
    rintro (x | y)
    · exact (p.1.norm_coe_le_norm x).trans (norm_fst_le p)
    · exact (p.2.norm_coe_le_norm y).trans (norm_snd_le p)

private theorem ordinalBlockSup_of_enumeration {α : Ordinal.{u}} (hl : IsSuccLimit α)
    (hp : Ordinal.Principal (· + ·) α) (a : ℕ → Iio α) (ha : Function.Surjective a) :
    ordinalBlockSup (fun n => (a n).val) = α := by
  apply le_antisymm
  · apply ciSup_le
    suffices h : ∀ n, ordinalBlockStart (fun n => (a n).val) n < α from fun n => (h n).le
    intro n
    induction n with
    | zero => exact hl.bot_lt
    | succ n ih =>
      rw [ordinalBlockStart_succ, Ordinal.add_one_eq_succ]
      exact hl.succ_lt (hp ih (a n).property)
  · by_contra! h
    obtain ⟨n, hn⟩ := ha ⟨_, h⟩
    exact (ordinalBlockEnd_lt_sup (fun n => (a n).val) n).not_ge
      ((congrArg Subtype.val hn).symm.le.trans (Ordinal.le_add_left _ _))

private def ordinalBlockBelow (a : ℕ → Ordinal.{u}) :
    (Σ n, OrdinalInterval (a n)) ≃ₜ Iio (ordinalBlockSup a) := by
  let h := (ordinalBlockUnion_isOpenEmbedding a).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (ordinalBlockUnion_range a))
  refine h.trans
    { toFun := fun x => ⟨x.val.val, lt_of_le_of_ne x.val.property.2
        (fun he => x.property (Subtype.ext he))⟩
      invFun := fun x => ⟨⟨x.val, bot_le, x.property.le⟩, fun he =>
        x.property.ne (congrArg Subtype.val he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

private def repeatSigmaHomeomorph (K : ℕ → Type u) [∀ n, TopologicalSpace (K n)] :
    (ℕ × (Σ n, K n)) ≃ₜ (Σ n, K (Nat.unpair n).2) := by
  let e : (ℕ × (Σ n, K n)) ≃ₜ (Σ p : ℕ × ℕ, K p.2) :=
    { toFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
      invFun := fun z => (z.1.1, ⟨z.1.2, z.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_prod_of_discrete_left.mpr
        (fun i => continuous_sigma fun j =>
          continuous_sigmaMk (σ := fun p : ℕ × ℕ => K p.2) (i := (i, j)))
      continuous_invFun := continuous_sigma fun p => by
        change Continuous (fun x : K p.2 => (p.1, (⟨p.2, x⟩ : Σ n, K n)))
        exact continuous_const.prodMk (continuous_sigmaMk (σ := K) (i := p.2)) }
  let f := Nat.pairEquiv.symm.sigmaCongrLeft (β := fun p => K p.2)
  exact e.trans (f.toHomeomorphOfContinuousOpen
    (continuous_sigma fun n => continuous_sigmaMk (σ := fun p : ℕ × ℕ => K p.2)
      (i := Nat.unpair n))
    (isOpenMap_sigma.mpr fun n =>
      isOpenMap_sigmaMk (σ := fun p : ℕ × ℕ => K p.2) (i := Nat.unpair n))).symm

private theorem ordinalPowerCzeroSelfSimilar (η : Ordinal.{u}) (hη : η ≠ 0)
    (hc : Countable (Iio (Ordinal.omega0 ^ η))) :
    Nonempty (C(OrdinalInterval (Ordinal.omega0 ^ η), 𝕜) ≃L[𝕜]
      CZeroSum C(OrdinalInterval (Ordinal.omega0 ^ η), 𝕜)) := by
  let α := Ordinal.omega0 ^ η
  have hl : IsSuccLimit α := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη
  letI : Nonempty (Iio α) := ⟨⟨0, hl.bot_lt⟩⟩
  letI : Countable (Iio α) := hc
  obtain ⟨a, ha⟩ := exists_surjective_nat (Iio α)
  let b : ℕ → Ordinal.{u} := fun n => (a n).val
  let a' : ℕ → Iio α := fun n => a (Nat.unpair n).2
  let b' : ℕ → Ordinal.{u} := fun n => (a' n).val
  have ha' : Function.Surjective a' := by
    intro x
    obtain ⟨n, hn⟩ := ha x
    exact ⟨Nat.pair 0 n, by simpa only [a', Nat.unpair_pair] using hn⟩
  have hb : ordinalBlockSup b = α :=
    ordinalBlockSup_of_enumeration hl (Ordinal.principal_add_omega0_opow η) a ha
  have hb' : ordinalBlockSup b' = α :=
    ordinalBlockSup_of_enumeration hl (Ordinal.principal_add_omega0_opow η) a' ha'
  let L := Σ n, OrdinalInterval (b n)
  let E := C₀(L, 𝕜)
  let e₀ : L ≃ₜ (ℕ × L) :=
    (ordinalBlockBelow b).trans ((Homeomorph.setCongr (by rw [hb, hb'] :
      Iio (ordinalBlockSup b) = Iio (ordinalBlockSup b'))).trans
        ((ordinalBlockBelow b').symm.trans (repeatSigmaHomeomorph fun n => OrdinalInterval (b n)).symm))
  let eE : E ≃L[𝕜] CZeroSum E :=
    ((czeroHomeomorphIsometry e₀).trans czeroDiscreteProductEquiv).toContinuousLinearEquiv
  let j : OrdinalInterval (b 0) → L := fun x => ⟨0, x⟩
  let z : L := j ⟨0, le_rfl, bot_le⟩
  let U := range j
  let f : E := JLMS.clopenIndicator U (isClopen_range_sigmaMk (i := 0))
    (isCompact_range (continuous_sigmaMk (σ := fun n => OrdinalInterval (b n)) (i := 0)))
  let P : E →L[𝕜] 𝕜 := czeroEvaluation z
  let J : 𝕜 →L[𝕜] E := (ContinuousLinearMap.id 𝕜 𝕜).smulRight f
  have hPJ : Function.RightInverse J P := by
    intro s
    change s * f z = s
    have hz : z ∈ U := mem_range_self _
    have hfz : f z = 1 := by
      change U.indicator (fun _ : L => (1 : 𝕜)) z = 1
      exact Set.indicator_of_mem hz _
    rw [hfz, mul_one]
  let split := ContinuousLinearEquiv.equivOfRightInverse P J hPJ
  let eSplit := eE.trans ((cZeroMapEquiv (ι := ℕ) split).trans cZeroProdEquiv)
  let eAbsorb : (𝕜 × E) ≃L[𝕜] E :=
    ((ContinuousLinearEquiv.refl 𝕜 𝕜).prodCongr eSplit).trans
      ((ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _).symm.trans
        ((cZeroHeadTailEquiv.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 _)).trans eSplit.symm))
  let eH : OrdinalInterval α ≃ₜ OnePoint L :=
    (ordinalIntervalCongr hb.symm).trans (ordinalOnePointSumHomeomorph b).symm
  let eX := (continuousMapHomeomorphEquiv eH).trans ((onePointCzeroProductEquiv L).trans eAbsorb)
  exact ⟨eX.trans (eE.trans (cZeroMapEquiv (ι := ℕ) eX.symm))⟩

private def finiteOrdinalPowerContinuousEquiv (η : Ordinal.{u}) (hη : η ≠ 0)
    (e : C(OrdinalInterval (Ordinal.omega0 ^ η), 𝕜) ≃L[𝕜]
      CZeroSum C(OrdinalInterval (Ordinal.omega0 ^ η), 𝕜)) (n : ℕ) :
    C(OrdinalInterval (Ordinal.omega0 ^ η * ((n + 1 : ℕ) : Ordinal)), 𝕜) ≃L[𝕜]
      C(OrdinalInterval (Ordinal.omega0 ^ η), 𝕜) := by
  induction n with
  | zero =>
    exact continuousMapHomeomorphEquiv (ordinalIntervalCongr (by simp))
  | succ n ih =>
    let α := Ordinal.omega0 ^ η
    let X := C(OrdinalInterval α, 𝕜)
    have h₁ : 1 < α := by
      simpa only [Ordinal.opow_zero] using (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
        (show 0 < η from bot_lt_iff_ne_bot.mpr hη)
    have h : α * ((n + 1 + 1 : ℕ) : Ordinal) = α * ((n + 1 : ℕ) : Ordinal) + 1 + α := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc,
        Ordinal.add_omega0_opow h₁]
    let es := (ordinalIntervalCongr h).trans (ordinalIntervalSumHomeomorph _ _).symm
    let eprod : (X × X) ≃L[𝕜] X :=
      ((ContinuousLinearEquiv.refl 𝕜 X).prodCongr e).trans (cZeroHeadTailEquiv.symm.trans e.symm)
    exact (continuousMapHomeomorphEquiv es).trans
      ((sumContinuousEquiv _ _).trans ((ih.prodCongr (ContinuousLinearEquiv.refl 𝕜 X)).trans eprod))

/-- The c₀ sum of C(M) is isomorphic to C(M) for infinite compact metric M. -/
theorem infiniteCompactCZeroSelfSimilar (M : Type u) [MetricSpace M] [CompactSpace M] [Infinite M] :
    Nonempty (C(M, 𝕜) ≃L[𝕜] CZeroSum C(M, 𝕜)) := by
  by_cases hc : Countable M
  · letI := hc
    obtain ⟨β, ⟨e⟩⟩ := countableCompact_exists_ordinal_model M
    letI : Infinite (OrdinalInterval β) := Infinite.of_injective e e.injective
    obtain ⟨η, n, hη, hn, ⟨g⟩⟩ := ordinal_compact_infinite_normal_form
      (A := Icc 0 β) isCompact_Icc (infinite_coe_iff.mp inferInstance)
    let α := Ordinal.omega0 ^ η
    letI : Countable (OrdinalInterval (α * (n : Ordinal))) :=
      ((e.trans g).symm.injective).countable
    have hle : α ≤ α * (n : Ordinal) := by
      simpa only [mul_one] using
        (mul_le_mul_left' (show (1 : Ordinal) ≤ (n : Ordinal) by exact_mod_cast hn) α)
    let j : Iio α → OrdinalInterval (α * (n : Ordinal)) := fun x =>
      ⟨x.val, bot_le, x.property.le.trans hle⟩
    have hj : Function.Injective j := fun x y he =>
      Subtype.ext (congrArg (fun z : OrdinalInterval (α * (n : Ordinal)) => z.val) he)
    obtain ⟨s⟩ := ordinalPowerCzeroSelfSimilar (𝕜 := 𝕜) η hη hj.countable
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    let e₁ := (continuousMapHomeomorphEquiv (e.trans g) :
      C(M, 𝕜) ≃L[𝕜] C(OrdinalInterval (α * (n : Ordinal)), 𝕜))
    let e₂ : C(OrdinalInterval (α * (n : Ordinal)), 𝕜) ≃L[𝕜] C(OrdinalInterval α, 𝕜) := by
      rw [hk]
      exact finiteOrdinalPowerContinuousEquiv η hη s k
    let h := e₁.trans e₂
    exact ⟨h.trans (s.trans (cZeroMapEquiv (ι := ℕ) h.symm))⟩
  · letI : Uncountable M := not_countable_iff.mp hc
    exact ⟨compactMetricCZeroEquiv M⟩

end JFA
