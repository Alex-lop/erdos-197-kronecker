# Erdős #197: rotation codings are not permutable

> **Status: PARTIAL result toward Erdős #197, NOT a solution.** This repository does **not** solve [Erdős Problem #197](https://www.erdosproblems.com/197), which is still open. It proves, and formally verifies in Lean 4, that the rotation (Sturmian) codings $\{n:\{n\alpha+\beta\}\in(a,b)\}$ with $\alpha$ irrational are not permutable: the case $d=1$ of Theorem K of the project's working notes.
>
> **Lean status:** kernel-checked (`lake build`, only `sorry` in `Challenge.lean`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`). Audit: one independent AI auditor (Claude Opus 5.5, 2026-11-11) confirmed the statement and re-ran the checks; the three documentation fixes it asked for were applied afterwards and not re-audited. No human has reviewed this repository.

## The result

Erdős #197 (Erdős–Graham) asks whether $\mathbb N$ can be partitioned into two sets, each with an enumeration (a listing of order type $\omega$) that contains no monotone 3-term arithmetic progression. Call such a set *permutable*. Davis–Entringer–Graham–Simmons (1977) showed that $\mathbb N$ itself is not permutable.

**Theorem K, $d=1$** (`Erdos197Kron.main_result`). Let $\alpha$ be irrational, $\beta$ real and $0\le a<b\le1$. Then $A=\{n\in\mathbb N:\{n\alpha+\beta\}\in(a,b)\}$ has no enumeration without a monotone 3-term arithmetic progression. More precisely, no set $S\supseteq A$ is permutable (`Erdos197Kron.kron_sub`), so no partition of $\mathbb N$ with such an $A$ inside one class answers #197 positively.

**What it does not reach.** The general Theorem K of the working notes ($d$ frequencies $\alpha\in\mathbb R^d$ with $1,\alpha_1,\dots,\alpha_d$ independent over $\mathbb Q$, any open window $U\subseteq\mathbb T^d$; Beatty parity colourings as a corollary) has a hand proof that survived three AI referees but is **not** formalized here. Neither are the Beatty parity corollary, windows given as open subsets of the circle, or Theorem RS (random sets) of the same notes.

**Idea of the proof.** Pick two anchors $f_1,f_2\in A$ with $x_1=\{f_1\alpha+\beta\}<x_2=\{f_2\alpha+\beta\}$ and a start $u_0>f_1,f_2$ with $\{u_0\alpha+\beta\}\in[x_1,x_2]$. The map $u\mapsto2u-f_1$ (if $2\{u\alpha+\beta\}\le x_1+x_2$) or $u\mapsto2u-f_2$ (otherwise) keeps $\{u\alpha+\beta\}$ in $[x_1,x_2]\subseteq(a,b)$, so it gives an infinite increasing chain in $A$. In an enumeration, from some point on both anchors come before the chain, and the anchor rule ($f\prec u\Rightarrow 2u-f\prec u$) makes the positions decrease forever: impossible. Density of $\{n\alpha+\beta\}$ along $n\ge N$ comes from Dirichlet's approximation theorem. The whole argument is in [`docs/proof.md`](docs/proof.md).

## Lean formalization

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The statement to audit (Mathlib-only, proof `sorry`). |
| [`Solution.lean`](Solution.lean) | The same statement, proved. |
| [`Erdos197Kron/Basic.lean`](Erdos197Kron/Basic.lean) | The proof: orbit lemma, (K1), invariant interval, the theorem with density as a hypothesis (`main_of_dense`), density for irrational $\alpha$, the superset form. `no_ap`, `Adm`, `adm_of_enum` and `anchor` are copied verbatim from erdos-197-rho. |
| [`checks/`](checks) | Fidelity and non-vacuity checks (not part of the build). |

```lean
theorem Erdos197Kron.main_result (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·)
```

The inner predicate is formal-conjectures' `¬HasMonotoneAP (Subtype.val ∘ f) 3`, unfolded so that `Challenge.lean` imports only Mathlib; `checks/fidelity.lean` checks this by `exact`. `checks/nonvacuity.lean` shows that the hypotheses are satisfiable ($\alpha=\sqrt2$, $(a,b)=(1/4,3/4)$), that the enumeration predicate is satisfiable, and that every set of the statement is infinite and has enumerations.

Build with `lake build` (Lean `v4.35.0`, Mathlib `v4.35.0`). Then run `lake env lean checks/fidelity.lean` and `lake env lean checks/nonvacuity.lean`; both end with `#print axioms`, which reports only `propext`, `Classical.choice` and `Quot.sound`.

## Credits

- J. A. Davis, R. C. Entringer, R. L. Graham, G. J. Simmons, *On permutations containing no long arithmetic progressions*, Acta Arith. 34 (1977): the problem setting.
- The orbit (descent) step is the infinite-descent argument already used in [erdos-197-rho-partition](https://github.com/Alex-lop/erdos-197-rho-partition) (`Erdos197Rho.chain`). The project's working notes attribute it to W. Kasel ("Part I, Lemma 4" of his notes on the problem); his paper is *Structural rigidity in the Erdős–Graham two-set permutation problem*, arXiv:2609.02939, and the lemma number has not been checked against it.
- google-deepmind/formal-conjectures: the predicate `HasMonotoneAP` and the statement `Erdos197.erdos_197`.

## Use of AI

This work was produced by Claude models (Anthropic) under the direction of **Alex Lopez**. The proof of Theorem K was found by a Claude Opus 5.5 agent in mission 2 of the project (2026-11-05, ledger entry "m2-r3 order/multi"); it survived three adversarial AI referees (Claude Fable 5.1 and Claude Opus 5.5 agents) and has not been refereed by a human. On 2026-11-11 a Claude Opus 5.5 agent wrote the Lean code and this repository, a second Claude Opus 5.5 agent audited it, and Claude Fable 5.2 orchestrated the run, rebuilt the project from scratch, read the proof file and applied the auditor's documentation fixes.

## License

Apache-2.0; see [LICENSE](LICENSE).
