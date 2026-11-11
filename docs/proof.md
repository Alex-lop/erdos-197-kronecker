# Rotation codings are not permutable (Erdős #197, partial result)

*Partial progress on [Erdős Problem #197](https://www.erdosproblems.com/197). The problem itself remains open, and this note does not solve it.*

## Background

**Problem (Erdős–Graham).** Can $\mathbb N$ be partitioned into two sets, each of which admits an enumeration (a listing of order type $\omega$) with no monotone 3-term arithmetic progression? Call $S\subseteq\mathbb N$ *permutable* if it has such an enumeration. Davis, Entringer, Graham and Simmons (1977) showed that $\mathbb N$ itself is not permutable.

This note proves the case $d=1$ of **Theorem K** of the project's working note `work/p197_m2_r3/order/proof.md` (not included in this repository):

> **Theorem K, $d=1$.** Let $\alpha$ be irrational, $\beta\in\mathbb R$ and $0\le a<b\le1$. Then no set $S\supseteq A=\{n\in\mathbb N:\{n\alpha+\beta\}\in(a,b)\}$ is permutable. In particular $A$ is not permutable, and no partition of $\mathbb N$ with $A$ inside one class is a solution of #197.

Here $\{x\}=x-\lfloor x\rfloor$. This covers the Sturmian and rotation codings with an interval window. The general Theorem K of the working note ($d$ frequencies $\alpha\in\mathbb R^d$ with $1,\alpha_1,\dots,\alpha_d$ linearly independent over $\mathbb Q$, an open window $U\subseteq\mathbb T^d$) has a hand proof that survived three AI referees; it is **not** formalized here. Its consequences for Beatty parity colourings and windows that are finite unions of arcs are also not formalized (an arc of $\mathbb T$ that does not wrap around $0$ is an interval $(a,b)$, so those windows are covered through the superset form once one such interval is inside the window, but no such corollary is stated in Lean).

Everything below is formalized in Lean 4 in this repository (`Erdos197Kron/Basic.lean`).

## 1. Admissible rankings

An enumeration $f:\mathbb N\simeq S$ without monotone 3-term AP gives the *position* $\rho(x)=f^{-1}(x)$, which is injective on $S$, obeys the **midpoint rule** (for $x<y<z$ in $S$ with $x+z=2y$, the middle $y$ comes before both ends or after both), and has finite initial segments (only finitely many $x\in S$ have $\rho(x)\le N$). Such a $\rho$ is *admissible* (`Adm`, `adm_of_enum`).

**Anchor rule** (`anchor`). If $a,w,z=2w-a\in S$, $a<w$ and $a\prec w$, then $z\prec w$.

These three items are copied verbatim from the Lean project erdos-197-rho.

## 2. The orbit lemma

**Lemma 2.1 (orbit).** Let $f_1,f_2\in S$ and let $u_0,u_1,\dots\in S$ with $u_k>f_1,f_2$ and $u_{k+1}=2u_k-f_1$ or $u_{k+1}=2u_k-f_2$ for every $k$. Then $S$ has no admissible ranking.

*Proof.* The chain is strictly increasing ($u_{k+1}-u_k=u_k-f>0$), so $u_k\ge k$. Only finitely many points precede $f_1$ or $f_2$: take $B$ with $x\le B$ whenever $\rho(x)\le\rho(f_1)+\rho(f_2)$. For $u_k>B$ both anchors precede $u_k$, and the anchor rule at $(f,u_k,u_{k+1})$ gives $u_{k+1}\prec u_k$. So $\rho(u_{B+1+n})+n\le\rho(u_{B+1})$ for all $n$, which fails at $n=\rho(u_{B+1})+1$. $\square$

This is the infinite-descent argument of `Erdos197Rho.chain` in erdos-197-rho, and the working note (Step 0 of its Theorem RS) attributes it to W. Kasel ("Part I, Lemma 4" of his notes on the problem; his paper is arXiv:2609.02939, and the lemma number has not been checked against it). Lean: `orbit`.

## 3. The invariant interval

Write $\theta_n=\{n\alpha+\beta\}$.

**Lemma 3.1 (K1).** For $f\le u$ in $\mathbb N$, $x=\theta_f$, $y=\theta_u$: if $0\le2y-x<1$ then $\theta_{2u-f}=2y-x$.

*Proof.* $(2u-f)\alpha+\beta-(2y-x)=2\lfloor u\alpha+\beta\rfloor-\lfloor f\alpha+\beta\rfloor\in\mathbb Z$. $\square$ (Lean: `fract_step`.)

**Lemma 3.2 (invariance).** Let $u>f_1,f_2$ with $x_1=\theta_{f_1}$, $x_2=\theta_{f_2}$ and $y=\theta_u\in[x_1,x_2]$. If $2y\le x_1+x_2$ put $v=2u-f_1$, otherwise $v=2u-f_2$. Then $v>u$ and $\theta_v\in[x_1,x_2]$.

*Proof.* In the first case $2y-x_1\in[x_1,x_2]$, in the second $2y-x_2\in(x_1,x_2]$; both lie in $[0,1)$, so Lemma 3.1 applies. $\square$ (Lean: `invariant`.)

## 4. Density

**Lemma 4.1.** For irrational $\alpha$, every $\beta$, every $N$ and every $0\le c<e\le1$ there is $n\ge N$ with $\theta_n\in(c,e)$.

*Proof.* By Dirichlet's theorem (Mathlib `Real.exists_int_int_abs_mul_sub_le`, with $n=\lceil1/(e-c)\rceil$) there are integers $K>0$, $j$ with $|\delta|<e-c$ for $\delta=K\alpha-j$, and $\delta\ne0$ since $\alpha$ is irrational. Put $t=N\alpha+\beta$. If $\delta>0$, let $z=\lfloor t\rfloor+1$ and $m=\lfloor(z+c-t)/\delta\rfloor+1$; then $z+c<t+m\delta\le z+c+\delta<z+e$. If $\delta<0$, let $z=\lfloor t\rfloor-1$ and $m=\lfloor(t-z-e)/(-\delta)\rfloor+1$; then $z+c<z+e+\delta\le t+m\delta<z+e$. In both cases $\theta_{N+Km}=t+m\delta-z\in(c,e)$, since $(N+Km)\alpha+\beta-(t+m\delta)=mj\in\mathbb Z$. $\square$ (Lean: `step_hit`, `dense_of_irrational`.)

## 5. Theorem K, $d=1$

*Proof.* Let $\mu=(a+b)/2$. By Lemma 4.1 pick $f_1$ with $\theta_{f_1}\in(a,\mu)$ and $f_2$ with $\theta_{f_2}\in(\mu,b)$, so $x_1<x_2$ and $[x_1,x_2]\subseteq(a,b)$; then $f_1,f_2\in A\subseteq S$. Pick $u_0>\max(f_1,f_2)$ with $\theta_{u_0}\in(x_1,x_2)$. Iterating Lemma 3.2 gives a chain $u_k$ with $\theta_{u_k}\in[x_1,x_2]$, so $u_k\in A\subseteq S$, and $u_{k+1}=2u_k-f_1$ or $2u_k-f_2$, $u_k>f_1,f_2$. Lemma 2.1 rules out an admissible ranking of $S$. $\square$

Lean: `kron_adm_of_dense` and `main_of_dense` take the conclusion of Lemma 4.1 as a hypothesis; `kron_adm`, `kron_sub` and `main_thm` are unconditional. `Erdos197Kron.main_result` in `Challenge.lean` is the enumeration form for $S=A$.

## 6. History

The general Theorem K ($d\ge1$, open windows in $\mathbb T^d$, an additive cube of $2^d$ anchors and an invariant parallelepiped) was found in mission 2 of the project (ledger entry "m2-r3 order/multi") and survived three adversarial AI referees (proof, computation and scope lenses). The $d=1$ rule above is the reduction stated at the end of its proof in the working note. Neither text has been refereed by a human.
