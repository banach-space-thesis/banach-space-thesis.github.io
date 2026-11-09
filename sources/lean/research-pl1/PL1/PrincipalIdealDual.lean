import BanLat.Dual

/-!
# Principal-ideal localization of positive functionals

This public helper reproduces the private witness construction in the pinned
BanLat/Operators/RieszKantorovich.lean (David Muñoz-Lahoz). Its proofs use
Riesz decomposition and the positive-cone extension lemma. No principal
projection in the domain, completeness of the domain, or Schur hypothesis
is assumed. Keeping the helper separate preserves the imported BanLat port.
-/

noncomputable section

namespace PL1.PrincipalIdealDual
open OrderBoundedHom

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

private lemma obZero_apply (x : X) : (0 : OrderBoundedHom X Y) x = (0 : Y) := rfl
private lemma obToLinearMap_apply (f : OrderBoundedHom X Y) (x : X) :
    f.toLinearMap x = f x := rfl

lemma f_mono_of_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) : Monotone f.toLinearMap :=
  Positive.monotone_iff.mpr fun y hy => by
    have := le_iff.mp hf y hy
    simpa only [obZero_apply, obToLinearMap_apply] using this


lemma f_apply_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {y : X} (hy : 0 ≤ y) : 0 ≤ f y := by
  have := le_iff.mp hf y hy
  simpa only [obZero_apply] using this

/-- The value of the witness operator on the positive cone:
`witFun f x₀ y = sup_n f (y ⊓ n • x₀)`. Defaults to `0` outside the regime where
the supremum exists. -/
noncomputable def witFun (f : OrderBoundedHom X Y) (x₀ y : X) : Y :=
  sSup (Set.range fun n : ℕ => f (y ⊓ n • x₀))

lemma witFun_isLUB {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (_hx₀ : 0 ≤ x₀) (_hy : 0 ≤ y) :
    IsLUB (Set.range fun n : ℕ => f (y ⊓ n • x₀)) (witFun f x₀ y) := by
  refine isLUB_csSup ⟨_, 0, rfl⟩ ⟨f y, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact f_mono_of_nonneg hf inf_le_left

lemma witFun_le_f {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : witFun f x₀ y ≤ f y := by
  apply (witFun_isLUB hf hx₀ hy).2
  rintro _ ⟨n, rfl⟩
  exact f_mono_of_nonneg hf inf_le_left

lemma witFun_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : 0 ≤ witFun f x₀ y := by
  refine (witFun_isLUB hf hx₀ hy).1 ⟨0, ?_⟩
  change f (y ⊓ (0 : ℕ) • x₀) = 0
  rw [zero_nsmul, inf_of_le_right hy]
  exact map_zero f.toLinearMap

lemma witFun_eq_at {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witFun f x₀ x₀ = f x₀ := by
  refine le_antisymm (witFun_le_f hf hx₀ hx₀) ?_
  refine (witFun_isLUB hf hx₀ hx₀).1 ⟨1, ?_⟩
  change f (x₀ ⊓ (1 : ℕ) • x₀) = f x₀
  rw [one_nsmul, inf_idem]

lemma witFun_zero_of_disjoint {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) (hd : y ⊓ x₀ = 0) :
    witFun f x₀ y = 0 := by
  have hyn : ∀ n : ℕ, y ⊓ n • x₀ = 0 := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, inf_of_le_right hy]
    | succ n ih =>
      have hle : y ⊓ (n + 1) • x₀ ≤ y ⊓ (n • x₀) + y ⊓ x₀ := by
        rw [succ_nsmul]
        exact inf_le_inf_add_inf_of_nonneg y (n • x₀) x₀ hy
          (nsmul_nonneg hx₀ n) hx₀
      rw [ih, hd, add_zero] at hle
      exact le_antisymm hle (le_inf hy (nsmul_nonneg hx₀ (n + 1)))
  refine le_antisymm ?_ (witFun_nonneg hf hx₀ hy)
  apply (witFun_isLUB hf hx₀ hy).2
  rintro _ ⟨n, rfl⟩
  change f (y ⊓ n • x₀) ≤ 0
  rw [hyn n]
  exact (map_zero f.toLinearMap).le

lemma witFun_add {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y₁ y₂ : X}
    (hx₀ : 0 ≤ x₀) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    witFun f x₀ (y₁ + y₂) = witFun f x₀ y₁ + witFun f x₀ y₂ := by
  refine le_antisymm ?_ ?_
  · apply (witFun_isLUB hf hx₀ (add_nonneg hy₁ hy₂)).2
    rintro _ ⟨n, rfl⟩
    have hznn : 0 ≤ (y₁ + y₂) ⊓ n • x₀ :=
      le_inf (add_nonneg hy₁ hy₂) (nsmul_nonneg hx₀ n)
    have hzy : (y₁ + y₂) ⊓ n • x₀ ≤ y₁ + y₂ := inf_le_left
    obtain ⟨z₁, z₂, hz₁nn, hz₁y₁, hz₂nn, hz₂y₂, hzeq⟩ :=
      riesz_decomposition (x := (y₁ + y₂) ⊓ n • x₀) y₁ y₂ hznn hy₁ hy₂ hzy
    have hz_le : (y₁ + y₂) ⊓ n • x₀ ≤ n • x₀ := inf_le_right
    have hz₁_nx : z₁ ≤ n • x₀ :=
      ((le_add_of_nonneg_right hz₂nn).trans hzeq.symm.le).trans hz_le
    have hz₂_nx : z₂ ≤ n • x₀ :=
      ((le_add_of_nonneg_left hz₁nn).trans hzeq.symm.le).trans hz_le
    have hz₁_inf : z₁ ≤ y₁ ⊓ n • x₀ := le_inf hz₁y₁ hz₁_nx
    have hz₂_inf : z₂ ≤ y₂ ⊓ n • x₀ := le_inf hz₂y₂ hz₂_nx
    calc f ((y₁ + y₂) ⊓ n • x₀)
        = f (z₁ + z₂) := by rw [hzeq]
      _ = f z₁ + f z₂ := map_add f.toLinearMap z₁ z₂
      _ ≤ f (y₁ ⊓ n • x₀) + f (y₂ ⊓ n • x₀) :=
          add_le_add (f_mono_of_nonneg hf hz₁_inf) (f_mono_of_nonneg hf hz₂_inf)
      _ ≤ witFun f x₀ y₁ + witFun f x₀ y₂ :=
          add_le_add ((witFun_isLUB hf hx₀ hy₁).1 ⟨n, rfl⟩)
            ((witFun_isLUB hf hx₀ hy₂).1 ⟨n, rfl⟩)
  · have step1 : ∀ n m : ℕ,
        f (y₁ ⊓ n • x₀) + f (y₂ ⊓ m • x₀) ≤ witFun f x₀ (y₁ + y₂) := by
      intro n m
      have hsum : (y₁ ⊓ n • x₀) + (y₂ ⊓ m • x₀) ≤ (y₁ + y₂) ⊓ ((n + m) • x₀) := by
        refine le_inf (add_le_add inf_le_left inf_le_left) ?_
        rw [add_nsmul]; exact add_le_add inf_le_right inf_le_right
      calc f (y₁ ⊓ n • x₀) + f (y₂ ⊓ m • x₀)
          = f ((y₁ ⊓ n • x₀) + (y₂ ⊓ m • x₀)) :=
            (map_add f.toLinearMap _ _).symm
        _ ≤ f ((y₁ + y₂) ⊓ (n + m) • x₀) := f_mono_of_nonneg hf hsum
        _ ≤ witFun f x₀ (y₁ + y₂) :=
            (witFun_isLUB hf hx₀ (add_nonneg hy₁ hy₂)).1 ⟨n + m, rfl⟩
    have step2 : ∀ m : ℕ,
        witFun f x₀ y₁ + f (y₂ ⊓ m • x₀) ≤ witFun f x₀ (y₁ + y₂) := by
      intro m
      have hub : witFun f x₀ (y₁ + y₂) - f (y₂ ⊓ m • x₀) ∈
          upperBounds (Set.range fun n : ℕ => f (y₁ ⊓ n • x₀)) := by
        rintro _ ⟨n, rfl⟩
        exact le_sub_iff_add_le.mpr (step1 n m)
      exact le_sub_iff_add_le.mp ((witFun_isLUB hf hx₀ hy₁).2 hub)
    have hub : witFun f x₀ (y₁ + y₂) - witFun f x₀ y₁ ∈
        upperBounds (Set.range fun n : ℕ => f (y₂ ⊓ n • x₀)) := by
      rintro _ ⟨m, rfl⟩
      rw [le_sub_iff_add_le, add_comm]; exact step2 m
    have h := (witFun_isLUB hf hx₀ hy₂).2 hub
    have h2 := le_sub_iff_add_le.mp h
    rwa [add_comm] at h2

/-- The witness linear map for `f` and `x₀ ≥ 0`. -/
noncomputable def witLin {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    X →ₗ[ℝ] Y := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension
    (fun y hy => witFun_nonneg hf hx₀ hy)
    (fun y₁ y₂ hy₁ hy₂ => witFun_add hf hx₀ hy₁ hy₂)

lemma witLin_apply_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : witLin hf hx₀ y = witFun f x₀ y := by
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension_nonneg _ _ hy

lemma witLin_positive {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    Positive (witLin hf hx₀) := by
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension_positive _ _

/-- The witness operator as an `OrderBoundedHom`. -/
noncomputable def witOp {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    OrderBoundedHom X Y :=
  ⟨witLin hf hx₀, Positive.isOrderBounded (witLin_positive hf hx₀)⟩

lemma witOp_apply {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) (y : X) :
    witOp hf hx₀ y = witLin hf hx₀ y := rfl

lemma witOp_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    (0 : OrderBoundedHom X Y) ≤ witOp hf hx₀ :=
  le_iff.mpr fun y hy => by
    have h := witLin_positive hf hx₀ y hy
    change (0 : Y) ≤ witLin hf hx₀ y at h
    simpa only [obZero_apply, witOp_apply] using h

lemma witOp_le_f {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witOp hf hx₀ ≤ f :=
  le_iff.mpr fun y hy => by
    change witLin hf hx₀ y ≤ f y
    rw [witLin_apply_nonneg hf hx₀ hy]
    exact witFun_le_f hf hx₀ hy

lemma witOp_apply_self {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witOp hf hx₀ x₀ = f x₀ := by
  change witLin hf hx₀ x₀ = f x₀
  rw [witLin_apply_nonneg hf hx₀ hx₀, witFun_eq_at hf hx₀]

lemma witOp_apply_disjoint {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X} (hx₀ : 0 ≤ x₀)
    (hy : 0 ≤ y) (hd : y ⊓ x₀ = 0) : witOp hf hx₀ y = 0 := by
  change witLin hf hx₀ y = 0
  rw [witLin_apply_nonneg hf hx₀ hy, witFun_zero_of_disjoint hf hx₀ hy hd]


end PL1.PrincipalIdealDual
