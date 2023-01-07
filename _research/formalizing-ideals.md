---
title: "Formalizing Ideals in Commutative Algebra"
excerpt: "Supervised by Pierre-Yves Strub at the Laboratoire d'Informatique de l'Ecole Polytechnique (LIX)"
collection: research
---

I am quite nostalgic about this project as it was my first research experience and my introduction to the world of formalization. I undertook this extracurricular internship following a "Logic and Proofs" taught by Prof. Pierre-Yves Strub during my second year of undergraduate. Before starting, I would also like to acknowledge Nazila Sharifi Amina, a fellow undergraduate who worked on this project with me.

## Ideals

The only mathematical prerequiste for understanding this project is to know what a [ring](https://en.wikipedia.org/wiki/Ring_(mathematics)#Definition) is. Once we have this in mind, we start by defining ideals:

>Let $(R, +, \cdot)$ be a ring. $I$ is an ideal of this ring if
>
>* $0 \in I$
>* $\forall x, y \in I$, $x + y \in I$
>* $\forall r \in R, x \in I, rx \in I$

We can now go about formalizing this definition in Coq. We use predicates as representations of sets: the predicate holds true for an element if and only if that element is in our set (it may help to think of it as a characteristic function). A subset of our ring $R$ is thus of type `pred R`, we can define an ideal as a predicate on which the following conditions hold:
```
Definition is_ideal (p : pred R) :=
  [/\ p 0
    , forall x y, p x -> p y -> p (x + y)
    & forall x y, p y -> p (x * y)].
```

Notice that because we are characterizing over $R$, the `_ + _` and `_ * _` operations are implicitly those of the ring.

## Our Goal

Let $\mathfrak{J}$ be the set of all ideals of a ring $R$.

As it turns out, [ideals are useful for cryptography](https://en.wikipedia.org/wiki/Ideal_lattice) and, in the context of a cryptographic verification project, we are interested in showing that the structure $(\mathfrak{J}, +, \cdot)$ is a semi-ring.

Here, the $+$ and $\cdot$ operators are not the usual addition and multiplication, but rather operations on the ideals themselves (which are sets).

## Formalizing Multiplication for Ideals

We will demonstrate the formalization process by examining the following definition of multiplication of ideals and an accompanying lemma:

>Let $\mathfrak{a}$ and $\mathfrak{b}$ be two ideals of $R$. Then, the product of $\mathfrak{a}$ and $\mathfrak{b}$, written $\mathfrak{a} \cdot \mathfrak{b}$ or $\mathfrak{a} \mathfrak{b}$, is defined as:
>
>$$
>  \mathfrak{a} \mathfrak{b} = \left\{
>    \sum_{i < n} a_i b_i \,\middle|\,
>      n \in \mathbb{N},
>      a_0, \ldots, a_{n-1} \in \mathfrak{a},
>      b_0, \ldots, b_{n-1} \in \mathfrak{b}
>  \right\} .
>$$

Remember that we choose to characterize sets through boolean predicates. We can thus represent the product of two ideals as a predicate `is_idealM_r p q` over $R$, where $p$ and $q$ are two ideals of $R$:

```
Definition is_idealM_r (p q : pred R) : pred R :=
  fun x =>
    decide (
      exists2 s : seq (R * R), forall y, y \in s -> y.1 \in p /\ y.2 \in q &
      x = \sum_(y <- s) y.1 * y.2).
```

Informally, `is_idealM_r p q` is a predicate over elements $x \in R$ which is true iff there exists $$(a_i)_{i \leq k} \in p$$ and $ (b_i)_{i \leq k} \in q$ such that $$x = \sum_{i=0}^k a_i \cdot b_i$$.

One of the conditions for $(\mathfrak{J}, +, \cdot)$ to be a semi-ring is that ideals need to be stable under mulitplication. We thus want to show that if $\mathfrak{a}$ and $\mathfrak{b}$ are ideals, then $\mathfrak{a}\mathfrak{b}$ is an ideal.

## Proving that ideals are stable under multiplication

To do this in Coq, we just prove that `is_idealM_r p q` is an ideal (no need to try and understand the following proof):

```
Lemma is_idealM (p q : ideals) : is_ideal (is_idealM_r p q).
Proof.
split=> [|x y|x y].
- by apply/is_idealM_rP; exists [::] => //; rewrite big_nil.
- case/is_idealM_rP=> [sx hx] ->; case/is_idealM_rP=> [sy hy] ->.
  apply/is_idealM_rP; exists (sx ++ sy) => [z|]; last by rewrite big_cat.
  by rewrite mem_cat => /orP [] ?; [apply: hx|apply: hy].
case/is_idealM_rP=> [s hs] ->; rewrite mulr_sumr.
pose t := [seq (x * z.1, z.2) | z <- s].
apply/is_idealM_rP; exists t.
- case => a b /mapP [] [] a' b' /hs /= [] pa' qb' [] -> ->.
  by split => //; apply is_idealS.
by rewrite big_map /=; apply eq_bigr =>  i _; rewrite mulrA.
Qed.
```

What I would like to highlight here is not the structure of the proof, but a subtelty that arrises with the use of `is_idealM_rP`.

```
Lemma is_idealM_rP (p q : pred R) (x : R) :
  reflect
    (exists2 s : seq (R * R),
       forall y, y \in s -> y.1 \in p /\ y.2 \in q &
       x = \sum_(y <- s) y.1 * y.2)
    (is_idealM_r p q x).
Proof. by apply/decideP. Qed.
```

This lemma uses `reflect` to relate the boolean value `is_idealM_r p q x` with a proposition about the existence of `s`. We can then apply this proposition in proofs when needed. Notice that the proof of this reflection relies on the following:

```
Axiom Prop_bool : forall (P : Prop), {P} + {~P}.

Definition decide (P : Prop) : bool :=
  Prop_bool P.

Lemma decideP P : reflect P (decide P).
Proof. by rewrite /decide; case: Prop_bool => /=; constructor. Qed.
```

Which includes the law of excluded middle ($P \lor \lnot P$) in the form of `{P} + {~P}`. We chose to reject the benefits of constructivism as we didn't particularly need them for this project. This was actually my first introduction to the constructive versus classical debate and taught me the value of understanding these nuances when working on formalization.


