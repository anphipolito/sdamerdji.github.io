---
title: "Bootstrapping a Verified Compiler"
excerpt: "Supervised by Johannes Åman Pohjola at the Trustworthy Systems group, University of New South Wales"
collection: research
---

### Pancake

During the summer of 2023, I was fortunate to be able to work as a research assistant with the Trustworthy Systems group at the University of New South Wales. I worked under the supervision of Dr. Johannes
Åman Pohjola on a low-level, device-driver oriented languaged called Pancake. You can find a page explaining the Pancake project and its place within the CakeML ecosystem [here](https://cakeml.org/pancake).

### What's the problem?

Pancake's semantics are specified in higher-order logic (HOL) and so is its compiler. Because we have a logic specification of the compiler, we can evaluate the compiler on a Pancake program using the HOL4 theorem prover. Unfortunately this is very inefficient and compiling simple Pancake programs using this method takes hours.

### How do we solve it?

Our goal is thus to obtain a binary implementation of the compiler which is proven to respect its HOL specification. To do this, we leverage a tool from the CakeML ecosystem called the translator. The translator is a proof-producing synthesis tool that allows us to obtain a deep embedding (in the form of a CakeML AST) from a shallow embedding (our HOL specification) and a proof that the deep embedding satisfies the original specification.

Our strategy is as follows: we translate our Pancake compiler's specification into a CakeML AST. We can then use a CakeML compiler to obtain an executable version of the compiler from the AST. This procedure is inspired by CakeML's bootstrapping scheme which also uses the translator, which we represent conceptually as follows:

<p align="center">
  <img src="../bootstrap.png" alt="CakeML's bootstrapping scheme"/>
</p>

Note that the executable is obtained through in-logic evaluation of the specification on the implementation (the AST).

### Implementing the solution

Following this plan involved helping the translator, either by transforming the Pancake specification into a form that the compiler could work with or by completing the translator's generated proofs when necessary. A simple example of the former would be type instantiation:
```
val _ = translate $ INST_TYPE[alpha|->“:word8 list”,
                              beta|->“:word64 list”,
                              gamma|->“:64”,
			      delta|->“:64”] attach_bitmaps_def;
```
And here is an simple example of the later, where the automatic proof generation resulted in an unecessary precondition:
```
val loop_call_comp_side = Q.prove(
  ‘∀spt prog. (loop_call_comp_side spt prog) ⇔ T’,
  ho_match_mp_tac comp_ind
  \\ rw[]
  \\ simp[Once (fetch "-" "loop_call_comp_side_def")]
  \\ TRY (metis_tac []))
  |> update_precondition;
```

### What's new?

The first and straightforward contribution of this project is the ability to easily compile Pancake programs to standard architectures, enabling benchmarks and more involved pancake projects. The second is that we've shown how to leverage the CakeML ecosystem for derivative projects, in our case by making use of the translator and the verified CakeML compiler.