import JLMS.SignTreeSplitting
import JLMS.BinaryBranchIndices

/-!
# Finite levels of the Hagler–Johnson binary sign tree

Each level stores its unit vectors, disjoint increasing coordinate families,
the signs realized along every family, and a norm bound on their finite span.
One splitting step appends a unit vector and preserves all earlier vectors.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def finiteVectorSpan {n : ℕ} (v : Fin n → X) : Submodule 𝕜 X :=
  Submodule.span 𝕜 (Set.range v)

theorem finiteVectorSpan_finiteDimensional {n : ℕ} (v : Fin n → X) :
    FiniteDimensional 𝕜 (finiteVectorSpan (𝕜 := 𝕜) v) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)

theorem mem_finiteVectorSpan {n : ℕ} (v : Fin n → X) (j : Fin n) :
    v j ∈ finiteVectorSpan (𝕜 := 𝕜) v :=
  Submodule.subset_span ⟨j, rfl⟩

structure SignTreeLevel (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) where
  vector : Fin n → X
  unit : ∀ j, ‖vector j‖ = 1
  branch : (Fin n → Bool) → ℕ → ℕ
  increasing : ∀ a, StrictMono (branch a)
  injective : Function.Injective (fun p : (Fin n → Bool) × ℕ => branch p.1 p.2)
  sign : ∀ a k j, ‖f (branch a k) (vector j) - (if a j then (1 : 𝕜) else -1)‖ ≤ 1 / 4
  restriction : ∀ a k, ‖(f (branch a k)).comp (finiteVectorSpan (𝕜 := 𝕜) vector).subtypeL‖ ≤ 2

def SignTreeLevel.zero (f : ℕ → (X →L[𝕜] 𝕜)) : SignTreeLevel f 0 where
  vector := Fin.elim0
  unit := fun j => Fin.elim0 j
  branch _ k := k
  increasing _ := strictMono_id
  injective := by
    intro p q h
    exact Prod.ext (Subsingleton.elim _ _) h
  sign := fun _ _ j => Fin.elim0 j
  restriction := by
    intro a k
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    have hx : x.val = 0 := by
      have hmem := x.property
      have hempty : Set.range (Fin.elim0 : Fin 0 → X) = ∅ := by
        ext y
        simp
      simpa only [finiteVectorSpan, hempty, Submodule.span_empty, Submodule.mem_bot] using hmem
    simp [hx]

theorem SignTreeLevel.exists_next (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (hstable : ∀ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = 1)
    {n : ℕ} (H : SignTreeLevel f n) :
    ∃ H' : SignTreeLevel f (n + 1), ∀ j : Fin n, H'.vector j.castSucc = H.vector j := by
  let D (x : X) := finiteVectorSpan (𝕜 := 𝕜) (Fin.snoc H.vector x)
  have hD (x : X) : FiniteDimensional 𝕜 (D x) := finiteVectorSpan_finiteDimensional _
  have hxD (x : X) : x ∈ D x := by
    simpa using mem_finiteVectorSpan (𝕜 := 𝕜) (Fin.snoc H.vector x) (Fin.last n)
  obtain ⟨x, hx, p, hp, hrestr, hsign⟩ := exists_split_sign_families f hC hf hstable
    H.branch H.injective H.increasing D hD hxD
  let H' : SignTreeLevel f (n + 1) := {
    vector := Fin.snoc H.vector x
    unit := by
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hx
      · simpa using H.unit i
    branch := splitBranchIndex H.branch p
    increasing := splitBranchIndex_strictMono H.branch p H.increasing hp
    injective := splitBranchIndex_injective H.branch p H.injective hp.injective
    sign := by
      intro a k j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, splitBranchIndex]
        change ‖f (H.branch (binaryPrefix a) (2 * p k + if binaryLast a then 1 else 0)) x -
          (if binaryLast a then (1 : 𝕜) else -1)‖ ≤ 1 / 4
        cases ha : binaryLast a
        · simpa only [ha, Bool.false_eq_true, if_false, Nat.add_zero] using
            (hsign (binaryPrefix a) k).2
        · simpa only [ha, if_true] using (hsign (binaryPrefix a) k).1
      · simpa only [Fin.snoc_castSucc, splitBranchIndex, binaryPrefix] using
          H.sign (binaryPrefix a) (2 * p k + if binaryLast a then 1 else 0) i
    restriction := by
      intro a k
      change ‖(f (H.branch (binaryPrefix a)
        (2 * p k + if binaryLast a then 1 else 0))).comp (D x).subtypeL‖ ≤ 2
      exact hrestr (binaryPrefix a) k _ (by split <;> omega)
  }
  refine ⟨H', fun j => ?_⟩
  simp [H']

end JLMS
