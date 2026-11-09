import BanachIsometric.ExactSectionBundleTopology

/-!
# Principal right action and finite Lipschitz exact-section atlases

The action is actual right composition of operators. It is continuous, free
and transitive on each actual fiber, and the natural local trivializations
are equivariant. Compactness supplies a finite atlas with a common bound for
the forward and inverse operator Lipschitz constants.
-/

namespace BanachIsometric

open Set Filter Bundle
open scoped Topology NNReal

noncomputable section

section RightAction

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}

def exactSectionRight (t : ExactSectionSpace S K H) (g : bodyAutomorphismGroup S) :
    ExactSectionSpace S K H :=
  let B := exactBodyMapRight (⟨t.val.2, t.property⟩ : ExactBodyMap S K (H t.val.1)) g
  ⟨(t.val.1, B.val), B.property⟩

omit [PseudoMetricSpace P] in
@[simp] theorem exactSectionRight_proj (t : ExactSectionSpace S K H)
    (g : bodyAutomorphismGroup S) : (exactSectionRight t g).val.1 = t.val.1 := rfl

omit [PseudoMetricSpace P] in
@[simp] theorem exactSectionRight_one (t : ExactSectionSpace S K H) :
    exactSectionRight t 1 = t := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro x
    rfl

omit [PseudoMetricSpace P] in
theorem exactSectionRight_mul (t : ExactSectionSpace S K H)
    (g h : bodyAutomorphismGroup S) :
    exactSectionRight (exactSectionRight t g) h = exactSectionRight t (g * h) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro x
    rfl

theorem continuous_exactSectionRight :
    Continuous (fun p : ExactSectionSpace S K H × bodyAutomorphismGroup S =>
      exactSectionRight p.1 p.2) := by
  apply continuous_induced_rng.mpr
  have hProj : Continuous (fun p : ExactSectionSpace S K H × bodyAutomorphismGroup S =>
      p.1.val.1) := continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hA : Continuous (fun p : ExactSectionSpace S K H × bodyAutomorphismGroup S =>
      p.1.val.2) := continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  have hg : Continuous (fun p : ExactSectionSpace S K H × bodyAutomorphismGroup S =>
      (p.2.val : E →L[ℝ] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  exact hProj.prodMk (hA.clm_comp hg)

omit [PseudoMetricSpace P] in
theorem exactSectionRight_injective (t : ExactSectionSpace S K H) :
    Function.Injective (exactSectionRight t) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply ContinuousLinearMap.ext
  intro x
  apply t.property.1
  exact congrArg (fun w : ExactSectionSpace S K H => w.val.2 x) hgh

variable [FiniteDimensional ℝ E]

omit [PseudoMetricSpace P] in
/-- Freeness and transitivity hold on the actual fibers, rather than merely
on the abstract fiber of a bundle core. -/
theorem exactSectionRight_existsUnique (t s : ExactSectionSpace S K H)
    (hbase : t.val.1 = s.val.1) :
    ∃! g : bodyAutomorphismGroup S, exactSectionRight t g = s := by
  rcases t with ⟨⟨a, A⟩, hA⟩
  rcases s with ⟨⟨b, B⟩, hB⟩
  change a = b at hbase
  subst b
  let A' : ExactBodyMap S K (H a) := ⟨A, hA⟩
  let B' : ExactBodyMap S K (H a) := ⟨B, hB⟩
  let g := exactBodyMapCoordinate A' B'
  have hg : exactSectionRight (⟨(a, A), hA⟩ : ExactSectionSpace S K H) g = ⟨(a, B), hB⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val (exactBodyMapRight_coordinate A' B')
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact exactSectionRight_injective _ (hh.trans hg.symm)

end RightAction

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H)

theorem actualTrivialization_snd_val (i : P) (t : ExactSectionSpace S K H)
    (hi : t.val.1 ∈ Z.baseSet i) :
    (((Z.actualTrivialization i t).2).val : E →L[ℝ] E) =
      (Z.inverse i t.val.1).comp t.val.2 :=
  Z.localTriv_inverse_operator i t hi

/-- The genuine local trivializations respect the principal right action. -/
theorem actualTrivialization_right_equivariant (i : P) (t : ExactSectionSpace S K H)
    (hi : t.val.1 ∈ Z.baseSet i) (g : bodyAutomorphismGroup S) :
    (Z.actualTrivialization i (exactSectionRight t g)).2 =
      (Z.actualTrivialization i t).2 * g := by
  apply Subtype.ext
  apply Units.ext
  change (((Z.actualTrivialization i (exactSectionRight t g)).2).val : E →L[ℝ] E) =
    (((Z.actualTrivialization i t).2).val : E →L[ℝ] E) * (g.val : E →L[ℝ] E)
  rw [Z.actualTrivialization_snd_val i (exactSectionRight t g) hi,
    Z.actualTrivialization_snd_val i t hi]
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable [CompactSpace P]

omit [FiniteDimensional ℝ E] in
/-- A compact parameter space, in particular the paper's parameter sphere,
admits a finite cover by the constructed Lipschitz exact-section charts. -/
theorem exists_finset_chart_cover :
    ∃ I : Finset P, ∀ a : P, ∃ i ∈ I, a ∈ Z.baseSet i := by
  have hcover : (univ : Set P) ⊆ ⋃ i : P, Z.baseSet i := by
    intro a _
    exact mem_iUnion.mpr ⟨a, Z.mem_baseSet a⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover Z.baseSet Z.isOpen_baseSet hcover
  refine ⟨I, ?_⟩
  intro a
  simpa only [mem_iUnion, exists_prop] using hI (mem_univ a)

omit [FiniteDimensional ℝ E] in
/-- On the finite cover a single constant bounds the two operator Lipschitz
estimates used to form the actual bundle charts. -/
theorem exists_finite_uniform_lipschitz_atlas :
    ∃ I : Finset P, ∃ L : ℝ≥0,
      (∀ a : P, ∃ i ∈ I, a ∈ Z.baseSet i) ∧
      ∀ i ∈ I, LipschitzOnWith L (Z.forward i) (Z.baseSet i) ∧
        LipschitzOnWith L (Z.inverse i) (Z.baseSet i) := by
  classical
  obtain ⟨I, hI⟩ := Z.exists_finset_chart_cover
  choose KA hA using Z.forward_lipschitz
  choose KB hB using Z.inverse_lipschitz
  let L := I.sup (fun i => max (KA i) (KB i))
  refine ⟨I, L, hI, ?_⟩
  intro i hi
  have hsup : max (KA i) (KB i) ≤ L :=
    Finset.le_sup (f := fun j => max (KA j) (KB j)) hi
  refine ⟨lipschitzOnWith_iff_restrict.mpr
    ((hA i).to_restrict.weaken ((le_max_left _ _).trans hsup)),
    lipschitzOnWith_iff_restrict.mpr
      ((hB i).to_restrict.weaken ((le_max_right _ _).trans hsup))⟩

end ExactSectionAtlas

end
end BanachIsometric
