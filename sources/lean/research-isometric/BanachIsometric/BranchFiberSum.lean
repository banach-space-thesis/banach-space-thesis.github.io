import BanachIsometric.SignedMultiplicity
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Intrinsic signed fiber multiplicity

An actual disjoint injective branch partition parametrizes every fiber exactly
once. Consequently its signed branch sum is the intrinsic signed sum over the
fiber, independently of the constructed partition. Finite fibers recover the
ordinary finite orientation-sign sum.
-/

namespace BanachIsometric

open Set Function MeasureTheory
open scoped Topology NNReal Function

noncomputable def injectiveBranchFiberEquiv {α : Type*} [Nonempty α]
    (f : α → α) (s : Set α) (t : ℕ → Set α)
    (hd : Pairwise (Disjoint on t)) (hc : (⋃ n, t n) = s) (hi : ∀ n, InjOn f (t n))
    (y : α) : {n : ℕ // y ∈ f '' t n} ≃ {x : α // x ∈ s ∧ f x = y} := by
  classical
  let F : {n : ℕ // y ∈ f '' t n} → {x : α // x ∈ s ∧ f x = y} := fun n =>
    ⟨invFunOn f (t n.val) y, by
      constructor
      · rw [← hc]
        exact mem_iUnion.mpr ⟨n.val, invFunOn_mem n.property⟩
      · exact invFunOn_eq n.property⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b hab
    apply Subtype.ext
    by_contra hne
    have hxA := invFunOn_mem a.property
    have hxB := invFunOn_mem b.property
    have hval : invFunOn f (t a.val) y = invFunOn f (t b.val) y := congrArg Subtype.val hab
    exact Set.disjoint_left.mp (hd hne) hxA (hval.symm ▸ hxB)
  · intro x
    have hx : x.val ∈ ⋃ n, t n := by rw [hc]; exact x.property.1
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    let a : {n : ℕ // y ∈ f '' t n} := ⟨n, ⟨x.val, hn, x.property.2⟩⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change invFunOn f (t n) y = x.val
    calc
      invFunOn f (t n) y = invFunOn f (t n) (f x.val) :=
        congrArg (invFunOn f (t n)) x.property.2.symm
      _ = x.val := (hi n).leftInvOn_invFunOn hn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The intrinsic real signed multiplicity of an actual fiber. On finite
fibers it is an ordinary sum of the signs of the derivative determinants. -/
noncomputable def signedFiberSum (f : E → E) (D : E → E →L[ℝ] E)
    (s : Set E) (y : E) : ℝ :=
  ∑' x : {x : E // x ∈ s ∧ f x = y}, jacobianOrientation D x.val

/-- The integer signed count of a finite actual fiber. -/
noncomputable def finiteSignedFiberCount (f : E → E) (D : E → E →L[ℝ] E)
    (s : Set E) (y : E) (hfin : {x : E | x ∈ s ∧ f x = y}.Finite) : ℤ := by
  classical
  letI : Fintype {x : E // x ∈ s ∧ f x = y} := hfin.fintype
  exact ∑ x : {x : E // x ∈ s ∧ f x = y}, (SignType.sign (D x.val).det : ℤ)

theorem signedFiberSum_eq_finiteSignedFiberCount
    (f : E → E) (D : E → E →L[ℝ] E) (s : Set E) (y : E)
    (hfin : {x : E | x ∈ s ∧ f x = y}.Finite) :
    signedFiberSum f D s y = (finiteSignedFiberCount f D s y hfin : ℝ) := by
  classical
  letI : Fintype {x : E // x ∈ s ∧ f x = y} := hfin.fintype
  simp only [signedFiberSum, finiteSignedFiberCount, tsum_fintype, Int.cast_sum,
    SignType.intCast_cast, jacobianOrientation]

theorem signedBranchSum_eq_signedFiberSum
    (f : E → E) (D : E → E →L[ℝ] E) (s : Set E) (t : ℕ → Set E)
    (hd : Pairwise (Disjoint on t)) (hc : (⋃ n, t n) = s) (hi : ∀ n, InjOn f (t n))
    (g : E → ℝ) (y : E) :
    signedBranchSum f D t g y = signedFiberSum f D s y * g y := by
  classical
  let A : Set ℕ := {n | y ∈ f '' t n}
  let F : ℕ → ℝ := fun n => jacobianOrientation D (invFunOn f (t n) y) * g y
  have hterms (n : ℕ) : signedBranchWeight f D (t n) g y = A.indicator F n := by
    by_cases hn : y ∈ f '' t n
    · have hn' : n ∈ A := hn
      simp only [signedBranchWeight, indicator_of_mem hn, indicator_of_mem hn', F]
    · have hn' : n ∉ A := hn
      simp only [signedBranchWeight, indicator_of_notMem hn, indicator_of_notMem hn']
  unfold signedBranchSum
  simp_rw [hterms]
  rw [← tsum_subtype A F]
  have he := (injectiveBranchFiberEquiv f s t hd hc hi y).tsum_eq
    (fun x : {x : E // x ∈ s ∧ f x = y} => jacobianOrientation D x.val * g y)
  change (∑' n : A, F n.val) = _
  change (∑' n : A, F n.val) = _ at he
  rw [he, tsum_mul_right]
  rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A genuine signed multiplicity integral formula on the regular set. The
measurable branches are constructed from the actual invertible derivatives,
and their sum is identified with the intrinsic fiber sum. -/
theorem integral_signedFiberSum (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hdet : ∀ x ∈ s, (D x).det ≠ 0)
    (g : E → ℝ) (hint : IntegrableOn (fun x => (D x).det * g (f x)) s μ) :
    (∫ y, signedFiberSum f D s y * g y ∂μ) = ∫ x in s, (D x).det * g (f x) ∂μ := by
  obtain ⟨t, hd, ht, hc, hi, hformula⟩ := exists_signed_branch_integral μ hs hD hdet
  simpa only [signedBranchSum_eq_signedFiberSum f D s t hd hc hi g] using hformula g hint

end BanachIsometric
