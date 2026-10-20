# Shamir's secret sharing in Lean

A small, self-contained example of proving a cryptographic scheme correct in [Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).

Lean is a programming language and a proof assistant: you write a mathematical statement, write a proof, and Lean checks every step down to the axioms. Mathlib is its library of formalized mathematics (polynomials, fields, probability, …), which this project builds on.

To install everything and run the proofs on your own computer, follow [INSTALL.md](INSTALL.md).

The scheme is from A. Shamir, [*How to Share a Secret*](https://dl.acm.org/doi/10.1145/359168.359176), Communications of the ACM 22(11), 1979. The whole development is about 150 lines.

## The scheme

Fix a field `F` (in practice a finite field) and a threshold `k + 1`. To share a secret `s ∈ F`:

1. The dealer picks `k` random coefficients `a₀, …, a_{k-1}` and forms the polynomial
   `p(X) = s + a₀·X + a₁·X² + ⋯ + a_{k-1}·Xᵏ`, of degree at most `k`, with `p(0) = s`.
2. Each party gets a distinct, nonzero public point `x` and the share `p(x)`.

Shamir's two claims:

- **Correctness:** any `k + 1` parties can recover `s`.
- **Perfect secrecy:** any `k` parties learn nothing about `s`.

## The idea in one picture

Take threshold `2`, so `k = 1` and the polynomial is a line, `p(X) = s + a₀·X`, crossing the vertical axis at the secret `s`.

- **Two shares are enough.** Two points determine a line, so two parties can draw it and read off where it meets the axis.
- **One share reveals nothing.** Through a single point `(x, p(x))` with `x ≠ 0` passes exactly one line for *each* possible value at `0`. A party holding one share cannot tell which line the dealer drew: when `a₀` is random, every value of the share is equally likely, whatever the secret is.

The general case is the same with polynomials of degree `k`: `k + 1` points determine such a polynomial, but `k` points leave the value at `0` completely free.

## What "proved" means here

A test checks a scheme on some inputs. A proof covers **all** of them: every field, every threshold, every secret, every choice of random coefficients, every set of points. Lean accepts a theorem only if every step of its proof checks. If a step were wrong, or a hypothesis were missing (for example, that the points are distinct), the file would not compile.

What remains to trust is the statement itself, which is why the statements below are explained in words. You never need to read a proof to trust its result, only its statement.

## What is proved

All in [`Shamir/Basic.lean`](Shamir/Basic.lean):

| Theorem | Statement |
|---|---|
| `reconstruct` | Any `k + 1` shares at distinct points determine the secret: the Lagrange interpolation of the shares, evaluated at `0`, is `s`. |
| `shares_injective` | For a fixed secret, different random coefficients give different shares to any `k` parties with distinct nonzero points. |
| `shares_bijective` | Over a finite field, the map from the random coefficients to those `k` shares is a bijection: every possible list of `k` shares comes from exactly one choice of coefficients. |
| `shares_uniform` | If the coefficients are uniformly random, the `k` shares are uniformly random, whatever the secret. |
| `shares_indistinguishable` | So the distribution of the `k` shares is the same for any two secrets. This is perfect secrecy. |

For example, correctness reads:

```lean
theorem reconstruct (s : F) (a : Fin k → F) (x : Fin (k + 1) → F)
    (hx : Function.Injective x) :
    (Lagrange.interpolate univ x (fun j => share s a (x j))).eval 0 = s
```

In words: for every secret `s`, every choice of coefficients `a`, and every `k + 1` points `x 0, …, x k` that are pairwise distinct (`Function.Injective x`), interpolating the shares and evaluating at `0` gives back `s`.

And perfect secrecy:

```lean
theorem shares_uniform [Fintype F] [DecidableEq F] (s : F) (x : Fin k → F)
    (hx : Function.Injective x) (h0 : ∀ j, x j ≠ 0) :
    (PMF.uniformOfFintype (Fin k → F)).map (shares s x) =
      PMF.uniformOfFintype (Fin k → F)
```

`PMF.uniformOfFintype α` is the uniform distribution on a finite type `α`, and `.map f` is the distribution of `f` applied to a sample. So: sampling the coefficients uniformly and computing the `k` shares gives the uniform distribution on lists of `k` field elements, which does not mention `s`.

The hypothesis `h0` matters: a party at the point `0` would receive `p(0) = s` itself.

[`Shamir/Example.lean`](Shamir/Example.lean) works a small case in `ZMod 7`: the secret `3` with threshold `2` and coefficient `2`, so `p(X) = 3 + 2X`, and the shares at the points `1, 2, 3` are `5, 0, 2`.

## How the proofs go

- **Correctness.** The dealer's polynomial has degree less than `k + 1` (`poly_degree_lt`). Mathlib's `Lagrange.eq_interpolate_of_eval_eq` says that such a polynomial equals the interpolation of its values at any `k + 1` distinct points. Evaluating at `0` gives `s` (`poly_eval_zero`).
- **Secrecy.** If two choices of coefficients give the same `k` shares, the two polynomials agree at `k + 1` points: the `k` share points, and `0`, where both equal `s`. Their difference has degree at most `k` and `k + 1` roots, so it is zero (`eq_of_degree_sub_lt_of_eval_finset_eq`). Then the coefficients agree (`poly_coeff_succ`). An injective map from a finite set to itself is a bijection, and a bijection sends the uniform distribution to the uniform distribution.

## Reading the Lean

If you are new to Lean, start with `Shamir/Example.lean`, then read `Shamir/Basic.lean` from the top. A few conventions:

- `F[X]` is the type of polynomials over `F`; `C c` is the constant polynomial `c`, and `X` is the variable.
- `p.eval x` is `p(x)`; `p.degree` is the degree, with `⊥` for the zero polynomial.
- `Fin k` is the type `{0, …, k-1}`, so `a : Fin k → F` is a list of `k` field elements.
- `theorem name (hypotheses) : statement := by tactics`. The tactics (`simp`, `rw`, `refine`, `exact`, …) build the proof step by step. In an editor with the Lean extension, put the cursor inside a proof to see the current goal.

## How to run

[INSTALL.md](INSTALL.md) is a step-by-step guide for Windows, macOS and Linux. In short, with [`elan`](https://github.com/leanprover/elan) (Lean's version manager) installed:

```bash
lake exe cache get   # download prebuilt Mathlib (a few minutes; avoids compiling it)
lake build           # check all the proofs
lake env lean CheckAxioms.lean
```

`CheckAxioms.lean` prints the axioms each theorem depends on. They should be only Lean's three standard ones, `propext`, `Classical.choice` and `Quot.sound`: no `sorry` (an unfinished proof) and no `native_decide` (a proof checked by compiled code rather than by Lean's kernel).

To explore interactively, open the folder in VS Code with the Lean 4 extension.

## Versions

Lean `4.31.0` and Mathlib `v4.31.0` (see `lean-toolchain` and `lakefile.toml`).
