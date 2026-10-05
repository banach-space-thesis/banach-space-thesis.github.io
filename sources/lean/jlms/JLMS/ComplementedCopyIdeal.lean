import JLMS.OrthogonalProjectionsIdeal

/-!
# Ogden Lemma 6.15: the complement of a copy of the whole space

A retraction vu = 1 yields a projection uv onto a complemented copy of the
whole space. Repeatedly inserting this copy gives mutually orthogonal copies
of its complement 1 - uv. Each of those copies algebraically generates the
first complement. The orthogonal-projection argument therefore puts 1 - uv
in the continuity ideal of every homomorphism.
-/

noncomputable section
namespace JLMS

theorem exists_orthogonalComplement_copies {B : Type*} [Ring B]
    (u v : B) (hvu : v * u = 1) :
    ∃ p : ℕ → B,
      (∀ n m, p n * p m = if n = m then p n else 0) ∧
      (∀ n, v ^ n * p n * u ^ n = 1 - u * v) := by
  let q := 1 - u * v
  have hqu : q * u = 0 := by simp [q, sub_mul, mul_assoc, hvu]
  have hvq : v * q = 0 := by simp [q, mul_sub, ← mul_assoc, hvu]
  have hqq : q * q = q := by
    change q * (1 - u * v) = q
    rw [mul_sub, mul_one, ← mul_assoc, hqu, zero_mul, sub_zero]
  let p (n : ℕ) := u ^ n * q * v ^ n
  have hpzero : p 0 = q := by simp [p]
  have hpstep (n) : p (n + 1) = u * p n * v := by
    change u ^ (n + 1) * q * v ^ (n + 1) = u * p n * v
    rw [pow_succ' u, pow_succ v]
    simp only [p, mul_assoc]
  have hcancel (n : ℕ) : v ^ n * u ^ n = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ']
      calc
        v ^ n * v * (u * u ^ n) = v ^ n * (v * u) * u ^ n := by simp only [mul_assoc]
        _ = 1 := by rw [hvu, mul_one, ih]
  refine ⟨p, ?_, ?_⟩
  · intro n
    induction n with
    | zero =>
      intro m
      cases m with
      | zero => simp [hpzero, hqq]
      | succ m => simp [hpzero, hpstep, ← mul_assoc, hqu]
    | succ n ih =>
      intro m
      cases m with
      | zero => simp [hpzero, hpstep, mul_assoc, hvq]
      | succ m =>
        calc
          p (n + 1) * p (m + 1) = u * (p n * (v * u) * p m) * v := by
            rw [hpstep, hpstep]
            simp only [mul_assoc]
          _ = u * (p n * p m) * v := by rw [hvu, mul_one]
          _ = if n + 1 = m + 1 then p (n + 1) else 0 := by
            rw [ih]
            by_cases h : n = m <;> simp [h, hpstep]
  · intro n
    change v ^ n * (u ^ n * q * v ^ n) * u ^ n = q
    calc
      v ^ n * (u ^ n * q * v ^ n) * u ^ n =
          (v ^ n * u ^ n) * q * (v ^ n * u ^ n) := by simp only [mul_assoc]
      _ = q := by rw [hcancel]; simp

variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NormedRing B] [NormedSpace 𝕜 B] [CompleteSpace B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem complement_mem_continuityIdeal_of_retraction (θ : B →ₙₐ[𝕜] A)
    (u v : B) (hvu : v * u = 1) : 1 - u * v ∈ continuityIdeal θ := by
  obtain ⟨p, hp, hreturn⟩ := exists_orthogonalComplement_copies u v hvu
  exact continuityIdeal_of_orthogonalProjection_copies θ p hp _
    (fun n => ⟨v ^ n, u ^ n, hreturn n⟩)

end JLMS
