# Partial Lean formalization of _Analysis I_

The files in this directory contain a formalization of selected portions of my text [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/) into [Lean](https://lean-lang.org/). The formalization is intended to be as faithful a paraphrasing as possible to the original text, while also showcasing Lean's features and syntax.  In particular, the formalization is _not_ optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader are rendered in this translation as `sorry`s.  Readers are welcome to fork the repository here to try their hand at these exercises, but I do not intend to place solutions in this repository directly.

While the arrangement of definitions, theorems, and proofs here are closely paraphrasing the textbook, I am refraining from directly quoting material from the textbook, instead providing references to the original text where appropriate.  As such, this formalization should be viewed as an annotated companion to the primary text, rather than a replacement for it.

Much of the material in this text is duplicated in Lean's standard math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), though with slightly different definitions.  To reconcile these discrepancies, this formalization will gradually transition from the textbook-provided definitions to the Mathlib-provided definitions as one progresses further into the text, thus sacrificing the self-containedness of the formalization in favor of compatibility with Mathlib.  For instance, Chapter 2 develops a theory of the natural numbers independent of Mathlib, but all subsequent chapters will use the Mathlib natural numbers instead.  (An epilogue to Chapter 2 is provided to show that the two notions of the natural numbers are isomorphic.)  As such, this formalization can also be used as an introduction to various portions of Mathlib.

In order to align the formalization with Mathlib conventions, a small number of technical changes have been made to some of the definitions as compared with the textbook version.  Most notably:

- Sequences are indexed to start from zero rather than from one, as Mathlib has much more support for the 0-based natural numbers `ℕ` than the 1-based natural numbers.
- Many operations that are left undefined in the text, such as division by zero, or taking the formal limit of a non-Cauchy sequence, are instead assigned a "junk" value (e.g., `0`) to make the operation totally defined.  This is because Lean has better support for total functions than partial functions (indiscriminate use of the latter can lead into "dependent type hell" in which even very basic manipulations require quite subtle and delicate proofs).  See for instance [this blog post](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/) by Kevin Buzzard for more discussion.
- The Chapter 2 natural numbers are constructed by an inductive type, rather than via a purely axiomatic approach.  However, the Peano Axioms are formalized in [the epilogue to this chapter](https://teorth.github.io/analysis/sec2e/).

## Sections

- _Chapter 1: Introduction (possible future expansion)_
- Chapter 2: Starting at the beginning: the natural numbers
  - Section 2.1: The Peano axioms ([Verso page](https://teorth.github.io/analysis/sec21/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_1.lean))
  - Section 2.2: Addition ([Verso page](https://teorth.github.io/analysis/sec22/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_2.lean))
  - Section 2.3: Multiplication ([Verso page](https://teorth.github.io/analysis/sec23/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_3.lean))
  - Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers ([Verso page](https://teorth.github.io/analysis/sec2e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_analysis/docs/.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_epilogue.lean))
- Chapter 3: Set theory
  - Section 3.1: Fundamentals ([Verso page](https://teorth.github.io/analysis/sec31/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_1.lean))
  - Section 3.2: Russell's paradox ([Verso page](https://teorth.github.io/analysis/sec32/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_2.lean))
  - Section 3.3: Functions ([Verso page](https://teorth.github.io/analysis/sec33/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_3.lean))
  - Section 3.4: Images and inverse images ([Verso page](https://teorth.github.io/analysis/sec34/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_4.lean))
  - Section 3.5: Cartesian products ([Verso page](https://teorth.github.io/analysis/sec35/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_5.lean))
  - Section 3.6: Cardinality of sets ([Verso page](https://teorth.github.io/analysis/sec36/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_6.lean))
- Chapter 4: Integers and rationals
  - Section 4.1: The integers ([Verso page](https://teorth.github.io/analysis/sec41/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_1.lean))
  - Section 4.2: The rationals ([Verso page](https://teorth.github.io/analysis/sec42/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_2.lean))
  - Section 4.3: Absolute value and exponentiation ([Verso page](https://teorth.github.io/analysis/sec43/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_3.lean))
  - Section 4.4: Gaps in the rational numbers ([Verso page](https://teorth.github.io/analysis/sec44/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_4.lean))
- Chapter 5: The Real numbers
  - Section 5.1: Cauchy sequences of rationals ([Verso page](https://teorth.github.io/analysis/sec51/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_1.lean))
  - Section 5.2: Equivalent Cauchy sequences ([Verso page](https://teorth.github.io/analysis/sec52/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_2.lean))
  - Section 5.3: Construction of the real numbers ([Verso page](https://teorth.github.io/analysis/sec53/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_3.lean))
  - Section 5.4: Ordering the reals ([Verso page](https://teorth.github.io/analysis/sec54/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_4.lean))
  - Section 5.5: The least upper bound property ([Verso page](https://teorth.github.io/analysis/sec55/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_5.lean))
  - _Section 5.6: Real exponentiation, part I (possible future expansion)_
  - Chapter 5 epilogue: Isomorphism with the Mathlib real numbers  ([Verso page](https://teorth.github.io/analysis/sec5e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_epilogue.lean))
- Chapter 6: Limits of sequences
  - Section 6.1: Convergence and limit laws ([Verso page](https://teorth.github.io/analysis/sec61/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_1.lean))
  - Section 6.2: The extended real number system ([Verso page](https://teorth.github.io/analysis/sec62/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_2.lean))
  - Section 6.3: Suprema and Infima of sequences ([Verso page](https://teorth.github.io/analysis/sec63/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_3.lean))
  - Section 6.4: Limsup, Liminf, and limit points ([Verso page](https://teorth.github.io/analysis/sec64/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_4.lean))
  - Section 6.5: Some standard limits ([Verso page](https://teorth.github.io/analysis/sec65/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_5.lean))
  - Section 6.6: Subsequences ([Verso page](https://teorth.github.io/analysis/sec66/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_6.lean))
  - _Section 6.7: Real exponentiation, part II (possible future expansion)_
  - Chapter 6 epilogue: Connections with Mathlib limits ([Verso page](https://teorth.github.io/analysis/sec6e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_epilogue.lean))
- Chapter 7: Series
  - Section 7.1: Finite series ([Verso page](https://teorth.github.io/analysis/sec71/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_1.lean))
  - Section 7.2: Infinite series ([Verso page](https://teorth.github.io/analysis/sec72/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_2.lean))
  - Section 7.3: Sums of non-negative numbers ([Verso page](https://teorth.github.io/analysis/sec73/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_3.lean))
  - Section 7.4: Rearrangement of series ([Verso page](https://teorth.github.io/analysis/sec74/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_4.lean))
  - Section 7.5: The root and ratio tests ([Verso page](https://teorth.github.io/analysis/sec75/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_5.lean))
- _Chapter 8: Infinite sets (possible future expansion)_
- Chapter 9: Continuous functions on `ℝ`
  - Section 9.1: Subsets of the real line ([Verso page](https://teorth.github.io/analysis/sec91/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_1.lean))
  - Section 9.2: The algebra of real-valued functions ([Verso page](https://teorth.github.io/analysis/sec92/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_2.lean))
  - Section 9.3: Limiting values of functions ([Verso page](https://teorth.github.io/analysis/sec93/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_3.lean))
  - Section 9.4: Continuous functions ([Verso page](https://teorth.github.io/analysis/sec94/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_4.lean))
  - Section 9.5: Left and right limits ([Verso page](https://teorth.github.io/analysis/sec95/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_5.lean))
  - Section 9.6: The maximum principle ([Verso page](https://teorth.github.io/analysis/sec96/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_6.lean))
  - Section 9.7: The intermediate value theorem ([Verso page](https://teorth.github.io/analysis/sec97/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_7.lean))
  - Section 9.8: Monotonic functions ([Verso page](https://teorth.github.io/analysis/sec98/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_8.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_8.lean))
  - Section 9.9: Uniform continuity ([Verso page](https://teorth.github.io/analysis/sec99/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_9.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_9.lean))
  - Section 9.10: Limits at infinity ([Verso page](https://teorth.github.io/analysis/sec910/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_10.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_10.lean))
- Chapter 10: Differentiation of functions
  - Section 10.1: Basic definitions ([Verso page](https://teorth.github.io/analysis/sec101/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_1.lean))
  - Section 10.2: Local maxima, local minima, and derivatives ([Verso page](https://teorth.github.io/analysis/sec102/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_2.lean))
  - Section 10.3: Monotone functions and derivatives ([Verso page](https://teorth.github.io/analysis/sec103/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_3.lean))
  - Section 10.4: Inverse functions and derivatives ([Verso page](https://teorth.github.io/analysis/sec104/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_4.lean))
  - Section 10.5: L'Hôpital's rule ([Verso page](https://teorth.github.io/analysis/sec105/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_5.lean))
- Chapter 11: The Riemann integral
  - _Section 11.1: Partitions (planned)_
  - _Section 11.2: Piecewise constant functions (planned)_
  - _Section 11.3: Upper and lower Riemann integrals (planned)_
  - _Section 11.4: Basic properties of the Riemann integral (planned)_
  - _Section 11.5: Riemann integrability of continuous functions (planned)_
  - _Section 11.6: Riemann integrability of monotone functions (planned)_
  - _Section 11.7: A non-Riemann integrable function (planned)_
  - _Section 11.8: The Riemann-Stieltjes integral (planned)_
  - _Section 11.9: The two fundamental theorems of calculus (planned)_
  - _Section 11.10: Consequences of the fundamental theorem of calculus (planned)_
- Appendix A: The basics of mathematical logic
  - A.1: Mathematical statements ([Verso page](https://teorth.github.io/analysis/appA1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_1.lean))
  - A.2: Implication ([Verso page](https://teorth.github.io/analysis/appA2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_2.lean))
  - A.3: The structure of proofs ([Verso page](https://teorth.github.io/analysis/appA3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_3.lean))
  - A.4: Variables and quantifiers ([Verso page](https://teorth.github.io/analysis/appA4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_4.lean))
  - A.5: Nested quantifiers ([Verso page](https://teorth.github.io/analysis/appA5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_5.lean))
  - A.6: Some examples of proofs and quantifiers ([Verso page](https://teorth.github.io/analysis/appA6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_6.lean))
  - A.7: Equality ([Verso page](https://teorth.github.io/analysis/appA7/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_7.lean))
- _Appendix B: The decimal system (possible future expansion)_

## Other resources

- [Web page for this project](https://teorth.github.io/analysis/)
  - [Documentation](https://teorth.github.io/analysis/docs/)
- [Web page for the book](https://terrytao.wordpress.com/books/analysis-i/)
  - [Springer edition](https://link.springer.com/book/10.1007/978-981-19-7261-4)
- [Blog post announcing this project](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/), Terence Tao, May 31 2025.
- [Lean Zulip discussion about this project](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Lean.20companion.20to.20.22Analysis.20I.22.20-.20discussion/with/521458888)
- [Notes for contributors](./CONTRIBUTING.md)

## General Lean resources

- [The Lean community](https://leanprover-community.github.io/)
  - [Lean4 web playground](https://live.lean-lang.org/)
  - [How to run a project in Lean locally](https://leanprover-community.github.io/install/project.html)
  - [The Lean community Zulip chat](https://leanprover.zulipchat.com/)
  - [Learning Lean4](https://leanprover-community.github.io/learn.html)
    - [The natural number game](https://adam.math.hhu.de/)
    - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)  - Lean textbook by Jeremy Avigad and Patrick Massot
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  - [Moogle](https://moogle-morphlabs.vercel.app/) - semantic search engine for Mathlib
  - [Loogle](https://loogle.lean-lang.org/) - expression matching search engine for Mathlib
  - [LeanSearch](https://leansearch.net/) - Natural language search engine for Mathlib
  - [List of Mathlib tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)
- Lean extensions:
  - [Canonical](https://github.com/chasenorman/Canonical)
  - [Duper](https://github.com/leanprover-community/duper)
  - [LeanCopilot](https://github.com/lean-dojo/LeanCopilot)
- [Common Lean pitfalls](https://github.com/nielsvoss/lean-pitfalls)
- [Lean4 questions in Proof Stack Exchange](https://proofassistants.stackexchange.com/questions/tagged/lean4)
- [The mechanics of proof](https://hrmacbeth.github.io/math2001/) - introductory Lean textbook by Heather Macbeth
- [My Youtube channel](https://www.youtube.com/@TerenceTao27) has some demonstrations of various Lean formalization, using a variety of tools.
- A [broader list](https://docs.google.com/document/d/1kD7H4E28656ua8jOGZ934nbH2HcBLyxcRgFDduH5iQ0) of AI and formal mathematics resources.

More resource suggestions welcome!

## Building

### Building the project

To build this project after [installing Lean](https://lean-lang.org/documentation/setup/) and cloning this repository, follow these steps:

```
% cd analysis/
% cd Analysis/
% lake exe cache get
% lake build
```

### Building the project's web page

To build the project's web page after [installing Lean](https://lean-lang.org/documentation/setup/) and cloning this repository, follow these steps:

```
% cd analysis/
% cd Analysis/
% lake exe cache get
% lake -R -Kenv=dev build Analysis:docs
% lake build
% cd ../
% cd book/
% lake exe analysis-book
% cd ../
```

After this, `book/_site/` contains the project's web page.
This can be served as a webpage by executing `python3 serve.py`
