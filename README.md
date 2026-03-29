# Lean formalization of _Analysis I_

The files in this directory contain a formalization of my text [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/) into [Lean](https://lean-lang.org/). The formalization is intended to be as faithful a paraphrasing as possible to the original text, while also showcasing Lean's features and syntax.  In particular, the formalization is _not_ optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader are rendered in this translation as `sorry`s.  Readers are welcome to fork the repository here to try their hand at these exercises, but I do not intend to place solutions in this repository directly.

While the arrangement of definitions, theorems, and proofs here are closely paraphrasing the textbook, I am refraining from directly quoting material from the textbook, instead providing references to the original text where appropriate.  As such, this formalization should be viewed as an annotated companion to the primary text, rather than a replacement for it.

Much of the material in this text is duplicated in Lean's standard math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), though with slightly different definitions.  To reconcile these discrepancies, this formalization will gradually transition from the textbook-provided definitions to the Mathlib-provided definitions as one progresses further into the text, thus sacrificing the self-containedness of the formalization in favor of compatibility with Mathlib.  For instance, Chapter 2 develops a theory of the natural numbers independent of Mathlib, but all subsequent chapters will use the Mathlib natural numbers instead.  (An epilogue to Chapter 2 is provided to show that the two notions of the natural numbers are isomorphic.)  As such, this formalization can also be used as an introduction to various portions of Mathlib.

In order to align the formalization with Mathlib conventions, a small number of technical changes have been made to some of the definitions as compared with the textbook version.  Most notably:

- Sequences are indexed to start from zero rather than from one, as Mathlib has much more support for the 0-based natural numbers `ℕ` than the 1-based natural numbers.
- Many operations that are left undefined in the text, such as division by zero, or taking the formal limit of a non-Cauchy sequence, are instead assigned a "junk" value (e.g., `0`) to make the operation totally defined.  This is because Lean has better support for total functions than partial functions (indiscriminate use of the latter can lead into "dependent type hell" in which even very basic manipulations require quite subtle and delicate proofs).  See for instance [this blog post](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/) by Kevin Buzzard for more discussion.
- The Chapter 2 natural numbers are constructed by an inductive type, rather than via a purely axiomatic approach.  However, the Peano Axioms are formalized in [the epilogue to this chapter](https://teorth.github.io/analysis/Analysis/Section_2_epilogue/).

## Sections

- _Chapter 1: Introduction (not formalized)_
- Chapter 2: Starting at the beginning: the natural numbers
  - Section 2.1: The Peano axioms ([Verso page](https://teorth.github.io/analysis/Analysis/Section_2_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean))
  - Section 2.2: Addition ([Verso page](https://teorth.github.io/analysis/Analysis/Section_2_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean))
  - Section 2.3: Multiplication ([Verso page](https://teorth.github.io/analysis/Analysis/Section_2_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean))
  - Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Section_2_epilogue/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_epilogue.lean))
- Chapter 3: Set theory
  - Section 3.1: Fundamentals ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean))
  - Section 3.2: Russell's paradox ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_2.lean))
  - Section 3.3: Functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean))
  - Section 3.4: Images and inverse images ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean))
  - Section 3.5: Cartesian products ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean))
  - Section 3.6: Cardinality of sets ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean))
  - Chapter 3 epilogue: Connections with ZFSet ([Verso page](https://teorth.github.io/analysis/Analysis/Section_3_epilogue/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_epilogue.lean))
- Chapter 4: Integers and rationals
  - Section 4.1: The integers ([Verso page](https://teorth.github.io/analysis/Analysis/Section_4_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean))
  - Section 4.2: The rationals ([Verso page](https://teorth.github.io/analysis/Analysis/Section_4_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean))
  - Section 4.3: Absolute value and exponentiation ([Verso page](https://teorth.github.io/analysis/Analysis/Section_4_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean))
  - Section 4.4: Gaps in the rational numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Section_4_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_4.lean))
- Chapter 5: The Real numbers
  - Section 5.1: Cauchy sequences of rationals ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean))
  - Section 5.2: Equivalent Cauchy sequences ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_2.lean))
  - Section 5.3: Construction of the real numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean))
  - Section 5.4: Ordering the reals ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean))
  - Section 5.5: The least upper bound property ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean))
  - Section 5.6: Real exponentiation, part I ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean))
  - Chapter 5 epilogue: Isomorphism with the Mathlib real numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Section_5_epilogue/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean))
- Chapter 6: Limits of sequences
  - Section 6.1: Convergence and limit laws ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean))
  - Section 6.2: The extended real number system ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean))
  - Section 6.3: Suprema and Infima of sequences ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_3.lean))
  - Section 6.4: Limsup, Liminf, and limit points ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean))
  - Section 6.5: Some standard limits ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_5.lean))
  - Section 6.6: Subsequences ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_6.lean))
  - Section 6.7: Real exponentiation, part II ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_7/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_7.lean))
  - Chapter 6 epilogue: Connections with Mathlib limits ([Verso page](https://teorth.github.io/analysis/Analysis/Section_6_epilogue/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_epilogue.lean))
- Chapter 7: Series
  - Section 7.1: Finite series ([Verso page](https://teorth.github.io/analysis/Analysis/Section_7_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean))
  - Section 7.2: Infinite series ([Verso page](https://teorth.github.io/analysis/Analysis/Section_7_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean))
  - Section 7.3: Sums of non-negative numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Section_7_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean))
  - Section 7.4: Rearrangement of series ([Verso page](https://teorth.github.io/analysis/Analysis/Section_7_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_4.lean))
  - Section 7.5: The root and ratio tests ([Verso page](https://teorth.github.io/analysis/Analysis/Section_7_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_5.lean))
- Chapter 8: Infinite sets
  - Section 8.1: Countability ([Verso page](https://teorth.github.io/analysis/Analysis/Section_8_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean))
  - Section 8.2: Summation on infinite sets ([Verso page](https://teorth.github.io/analysis/Analysis/Section_8_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean))
  - Section 8.3: Uncountable sets ([Verso page](https://teorth.github.io/analysis/Analysis/Section_8_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_3.lean))
  - Section 8.4: The axiom of choice ([Verso page](https://teorth.github.io/analysis/Analysis/Section_8_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_4.lean))
  - Section 8.5: Ordered sets ([Verso page](https://teorth.github.io/analysis/Analysis/Section_8_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean))
- Chapter 9: Continuous functions on `ℝ`
  - Section 9.1: Subsets of the real line ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean))
  - Section 9.2: The algebra of real-valued functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_2.lean))
  - Section 9.3: Limiting values of functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_3.lean))
  - Section 9.4: Continuous functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_4.lean))
  - Section 9.5: Left and right limits ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_5.lean))
  - Section 9.6: The maximum principle ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean))
  - Section 9.7: The intermediate value theorem ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_7/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_7.lean))
  - Section 9.8: Monotonic functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_8/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_8.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_8.lean))
  - Section 9.9: Uniform continuity ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_9/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_9.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_9.lean))
  - Section 9.10: Limits at infinity ([Verso page](https://teorth.github.io/analysis/Analysis/Section_9_10/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_10.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_10.lean))
- Chapter 10: Differentiation of functions
  - Section 10.1: Basic definitions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_10_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean))
  - Section 10.2: Local maxima, local minima, and derivatives ([Verso page](https://teorth.github.io/analysis/Analysis/Section_10_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_2.lean))
  - Section 10.3: Monotone functions and derivatives ([Verso page](https://teorth.github.io/analysis/Analysis/Section_10_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_3.lean))
  - Section 10.4: Inverse functions and derivatives ([Verso page](https://teorth.github.io/analysis/Analysis/Section_10_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_4.lean))
  - Section 10.5: L'Hôpital's rule ([Verso page](https://teorth.github.io/analysis/Analysis/Section_10_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_5.lean))
- Chapter 11: The Riemann integral
  - Section 11.1: Partitions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean))
  - Section 11.2: Piecewise constant functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean))
  - Section 11.3: Upper and lower Riemann integrals ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean))
  - Section 11.4: Basic properties of the Riemann integral ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_4.lean))
  - Section 11.5: Riemann integrability of continuous functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_5.lean))
  - Section 11.6: Riemann integrability of monotone functions ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_6.lean))
  - Section 11.7: A non-Riemann integrable function ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_7/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_7.lean))
  - Section 11.8: The Riemann-Stieltjes integral ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_8/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_8.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean))
  - Section 11.9: The two fundamental theorems of calculus ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_9/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_9.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_9.lean))
  - Section 11.10: Consequences of the fundamental theorem of calculus ([Verso page](https://teorth.github.io/analysis/Analysis/Section_11_10/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_10.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_10.lean))
- Appendix A: The basics of mathematical logic
  - A.1: Mathematical statements ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_1.lean))
  - A.2: Implication ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_2.lean))
  - A.3: The structure of proofs ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_3.lean))
  - A.4: Variables and quantifiers ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_4.lean))
  - A.5: Nested quantifiers ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_5.lean))
  - A.6: Some examples of proofs and quantifiers ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_6.lean))
  - A.7: Equality ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_A_7/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_7.lean))
- Appendix B: The decimal system
  - B.1: The decimal representation of natural numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_B_1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_B_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean))
  - B.2: The decimal representation of real numbers ([Verso page](https://teorth.github.io/analysis/Analysis/Appendix_B_2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_B_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_2.lean))

## Additional content

I am using this repository to host some other minor Lean content unrelated to the text book:

- [A formalization of my book on Measure Theory](https://github.com/teorth/analysis/tree/main/Analysis/MeasureTheory) (work in progress)
- A formalization of physical units
  - Support for systems of units ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/UnitsSystem.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean))
    - Examples of use ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/UnitsSystemExamples.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystemExamples.lean))
  - The SI system of units ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/SI.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/SI.lean))
    - Examples of use ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/SIExamples.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/SIExamples.lean))
- A formalization of finite choice avoiding Lean's axiom of choice
  - [Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/FiniteChoice.html) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/FiniteChoice.lean))
- Some finite probability theory [Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/Probability.html) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean))
- A [solution to Erdos problem \#379](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_379.html) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean))
- [Pikhurko's counterexample to Erdos problem \#613](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_613.html) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean))
- A [solution to Erdos problem \#707](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_707.html) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean))
- A [solution to Erdos problem \#987](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_987.html) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_987.lean))

## Other resources

- [Web page for this project](https://teorth.github.io/analysis/)
  - [Documentation](https://teorth.github.io/analysis/docs/)
- [Web page for the book](https://terrytao.wordpress.com/books/analysis-i/)
  - [Springer edition](https://link.springer.com/book/10.1007/978-981-19-7261-4)
- [Blog post announcing this project](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/), Terence Tao, May 31 2025.
- [Lean Zulip discussion about this project](https://leanprover.zulipchat.com/#narrow/channel/514017-Analysis-I)
- [Notes for contributors](./CONTRIBUTING.md)
- A Lean formalization of the sequel, Analysis II, to the Analysis I text has been created by Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, and Zaiwen Wen, and can be found [here](https://github.com/optpku/ReasBook/tree/main/ReasBook/Books/Analysis2_Tao_2022).

## General Lean resources

- [The Lean community](https://leanprover-community.github.io/)
  - [Lean4 web playground](https://live.lean-lang.org/)
  - [How to run a project in Lean locally](https://leanprover-community.github.io/install/project.html)
  - [The Lean community Zulip chat](https://leanprover.zulipchat.com/)
  - [Learning Lean4](https://leanprover-community.github.io/learn.html)
    - [The natural number game](https://adam.math.hhu.de/)
    - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)  - Lean textbook by Jeremy Avigad and Patrick Massot
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  - [Mathlib help files](https://seasawher.github.io/mathlib4-help/)
  - [Moogle](https://moogle-morphlabs.vercel.app/) - semantic search engine for Mathlib
  - [Loogle](https://loogle.lean-lang.org/) - expression matching search engine for Mathlib
  - [LeanSearch](https://leansearch.net/) - Natural language search engine for Mathlib
  - [List of Mathlib tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)
    - [Lean tactics cheat sheet](https://github.com/fpvandoorn/LeanCourse24/blob/master/lean-tactics.pdf)
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
% ./build.sh
```

### Building the project's web page

To build the project's web page after [installing Lean](https://lean-lang.org/documentation/setup/) and cloning this repository, follow these steps:

```
% ./build-web.sh
```

After this, `_site/` contains the project's web page.
This can be served as a webpage by executing `python3 serve.py`

### Updating the Lean/Mathlib version

Because this project uses a deprecated method to conditionally require `doc-gen4`
in order to update the version of Lean and Mathlib used in the project you need to:
* edit the `lakefile.lean` to change the `require` lines for Mathlib and doc-gen4,
  to pin to the tag corresponding to the next Lean version
  (it is highly recommended that you update in incremental steps)
* edit the `lean-toolchain` to change the Lean version to the next version
* run `lake update -R -Kenv=dev`
* this may have the side effect of setting your `lean-toolchain` to the *latest* Lean version;
  if so, revert it to the intended version
