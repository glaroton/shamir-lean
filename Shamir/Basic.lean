import Mathlib

/-!
# Shamir's secret sharing

A. Shamir, *How to Share a Secret*, Communications of the ACM 22(11), 1979.

To share a secret `s` in a field `F` among several parties with threshold `k + 1`, the
dealer picks `k` random coefficients `a 0, …, a (k-1)` and forms the polynomial

  `p(X) = s + a 0 · X + a 1 · X² + ⋯ + a (k-1) · Xᵏ`,

of degree at most `k`. Each party gets a distinct nonzero public point `x` and the share
`p(x)`. We prove the two properties claimed in the paper:

* **Correctness** (`reconstruct`): any `k + 1` shares determine `p`, and so the secret
  `s = p(0)`, by Lagrange interpolation.
* **Perfect secrecy** (`shares_bijective`, `shares_uniform`): any `k` shares reveal nothing.
  For a fixed secret, the map from the random coefficients to the `k` shares is a
  bijection, so when the coefficients are uniformly random the shares are uniformly
  random too, whatever the secret is.
-/

open Polynomial Finset

namespace Shamir

variable {F : Type*} [Field F] {k : ℕ}

/-- The dealer's polynomial: the secret `s` is the constant term, and `a` holds the other
    `k` coefficients. -/
noncomputable def poly (s : F) (a : Fin k → F) : F[X] :=
  C s + ∑ i : Fin k, C (a i) * X ^ (i.val + 1)

/-- The share of the party whose public point is `x`. -/
noncomputable def share (s : F) (a : Fin k → F) (x : F) : F :=
  (poly s a).eval x

/-! ## Basic facts about the polynomial -/

/-- The secret is the value at zero. -/
theorem poly_eval_zero (s : F) (a : Fin k → F) : (poly s a).eval 0 = s := by
  simp [poly, eval_finsetSum]

/-- The polynomial has degree at most `k`. -/
theorem poly_degree_lt (s : F) (a : Fin k → F) : (poly s a).degree < (k + 1 : ℕ) := by
  have h : (poly s a).natDegree ≤ k := by
    unfold poly
    refine natDegree_add_le_of_degree_le (by simp) ?_
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  exact (degree_le_of_natDegree_le h).trans_lt (by exact_mod_cast Nat.lt_succ_self k)

/-- The random coefficients can be read back from the polynomial. -/
theorem poly_coeff_succ (s : F) (a : Fin k → F) (j : Fin k) :
    (poly s a).coeff (j.val + 1) = a j := by
  simp [poly, Fin.val_inj]

/-! ## Correctness -/

/-- **Correctness.** Any `k + 1` parties with distinct points `x 0, …, x k` recover the
    secret: the Lagrange interpolation of their shares, evaluated at zero, is `s`. -/
theorem reconstruct (s : F) (a : Fin k → F) (x : Fin (k + 1) → F)
    (hx : Function.Injective x) :
    (Lagrange.interpolate univ x (fun j => share s a (x j))).eval 0 = s := by
  unfold share
  rw [← Lagrange.eq_interpolate_of_eval_eq _ hx.injOn
    (by simpa using poly_degree_lt s a) (fun j _ => rfl), poly_eval_zero]

/-! ## Perfect secrecy -/

/-- The shares of `k` parties with points `x 0, …, x (k-1)`, as a function of the
    dealer's random coefficients. -/
noncomputable def shares (s : F) (x : Fin k → F) (a : Fin k → F) : Fin k → F :=
  fun j => share s a (x j)

/-- For a fixed secret, different random coefficients give different shares to any `k`
    parties with distinct nonzero points. -/
theorem shares_injective (s : F) (x : Fin k → F) (hx : Function.Injective x)
    (h0 : ∀ j, x j ≠ 0) : Function.Injective (shares s x) := by
  classical
  intro a b hab
  -- The two polynomials agree at `0` (both give `s`) and at every `x j`: `k + 1` points.
  have hpts : #(insert 0 (univ.image x)) = k + 1 := by
    rw [card_insert_of_notMem (by simpa [eq_comm] using h0), card_image_of_injective _ hx,
      card_univ, Fintype.card_fin]
  have heq : poly s a = poly s b := by
    refine eq_of_degree_sub_lt_of_eval_finset_eq (insert 0 (univ.image x)) ?_ ?_
    · rw [hpts]
      exact (degree_sub_le _ _).trans_lt (max_lt (poly_degree_lt s a) (poly_degree_lt s b))
    · intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · rw [poly_eval_zero, poly_eval_zero]
      · obtain ⟨j, -, rfl⟩ := mem_image.mp hy
        exact congrFun hab j
  funext j
  rw [← poly_coeff_succ s a j, ← poly_coeff_succ s b j, heq]

/-- **Perfect secrecy, combinatorial form.** Over a finite field, for any secret, every
    possible list of `k` shares comes from exactly one choice of random coefficients. -/
theorem shares_bijective [Finite F] (s : F) (x : Fin k → F) (hx : Function.Injective x)
    (h0 : ∀ j, x j ≠ 0) : Function.Bijective (shares s x) :=
  Finite.injective_iff_bijective.mp (shares_injective s x hx h0)

/-- **Perfect secrecy, probabilistic form.** If the dealer picks the coefficients uniformly
    at random, the `k` shares are uniformly distributed, so their distribution does not
    depend on the secret. -/
theorem shares_uniform [Fintype F] [DecidableEq F] (s : F) (x : Fin k → F)
    (hx : Function.Injective x) (h0 : ∀ j, x j ≠ 0) :
    (PMF.uniformOfFintype (Fin k → F)).map (shares s x) =
      PMF.uniformOfFintype (Fin k → F) := by
  ext v
  obtain ⟨a, rfl⟩ := (shares_bijective s x hx h0).2 v
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg fun h => hb ((shares_injective s x hx h0) h.symm)]
  · simp

/-- In particular, `k` shares have the same distribution for any two secrets. -/
theorem shares_indistinguishable [Fintype F] [DecidableEq F] (s s' : F) (x : Fin k → F)
    (hx : Function.Injective x) (h0 : ∀ j, x j ≠ 0) :
    (PMF.uniformOfFintype (Fin k → F)).map (shares s x) =
      (PMF.uniformOfFintype (Fin k → F)).map (shares s' x) := by
  rw [shares_uniform s x hx h0, shares_uniform s' x hx h0]

end Shamir
