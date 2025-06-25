import VersoBlog
open Verso Genre Blog

#doc (Page) " Partial Lean formalization of Analysis I" =>

The files in this directory contain a formalization of selected portions of my text [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/) into [Lean](https://lean-lang.org/). The formalization is intended to be as faithful a paraphrasing as possible to the original text, while also showcasing Lean's features and syntax.  In particular, the formalization is _not_ optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader are rendered in this translation as `sorry`s.  Readers are welcome to fork the repository here to try their hand at these exercises, but I do not intend to place solutions in this repository directly.

While the arrangement of definitions, theorems, and proofs here are closely paraphrasing the textbook, I am refraining from directly quoting material from the textbook, instead providing references to the original text where appropriate.  As such, this formalization should be viewed as an annotated companion to the primary text, rather than a replacement for it.

Much of the material in this text is duplicated in Lean's standard math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), though with slightly different definitions.  To reconcile these discrepancies, this formalization will gradually transition from the textbook-provided definitions to the Mathlib-provided definitions as one progresses further into the text, thus sacrificing the self-containedness of the formalization in favor of compatibility with Mathlib.  For instance, Chapter 2 develops a theory of the natural numbers independent of Mathlib, but all subsequent chapters will use the Mathlib natural numbers instead.  (An epilogue to Chapter 2 is provided to show that the two notions of the natural numbers are isomorphic.)  As such, this formalization can also be used as an introduction to various portions of Mathlib.

In order to align the formalization with Mathlib conventions, a small number of technical changes have been made to some of the definitions as compared with the textbook version.  Most notably:
- Sequences are indexed to start from zero rather than from one, as Mathlib has much more support for the 0-based natural numbers `ℕ` than the 1-based natural numbers.
- Many operations that are left undefined in the text, such as division by zero, or taking the formal limit of a non-Cauchy sequence, are instead assigned a "junk" value (e.g., `0`) to make the operation totally defined.  This is because Lean has better support for total functions than partial functions (indiscriminate use of the latter can lead into "dependent type hell" in which even very basic manipulations require quite subtle and delicate proofs).  See for instance [this blog post](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/) by Kevin Buzzard for more discussion.

Currently formalized sections:

- [Section 2.1: The Peano axioms](./sec21/)
- [Section 2.2: Addition](./sec22/)
- [Section 2.3: Multiplication](./sec23/)
- [Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers](./sec2e)
- [Section 3.1: Set theory fundamentals](./sec31/)
- [Section 3.2: Russel's paradox](./sec32/)
- [Section 3.3: Functions](./sec33/)
- [Section 3.4: Images and inverse images](./sec34/)
- [Section 3.5: Cartesian products](./sec35/)
- [Section 3.6: Cardinality of sets](./sec36/)
- [Section 4.1: The integers](./sec41/)
- [Section 4.2: The rationals](./sec42/)
- [Section 4.3: Absolute value and exponentiation](./sec43/)
- [Section 4.4: Gaps in the rational numbers](./sec44/)
- [Section 5.1: Cauchy sequences of rationals](./sec51)
- [Section 5.2: Equivalent Cauchy sequences](./sec52/)
- [Section 5.3: Construction of the real numbers](./sec53/)
- [Section 5.4: Ordering the reals](./sec54/)
- [Section 5.5: The least upper bound property](./sec55/)
- [Chapter 5 epilogue: Isomorphism with the Mathlib reals](./sec5e/)
- [Section 6.1: Convergence and limit laws](./sec61/)
- [Section 6.2: The extended real number system](./sec62/)
- [Section 6.3: Suprema and Infima of sequences](./sec63/)
- [Section 6.4: Lim inf, lim sup, and limit points](./sec64/)
- [Section 6.5: Some standard limits](./sec65/)
- [Section 6.6: Subsequences](./sec66/)
- [Section 6 epilogue: Connections with Mathlib limits](./sec6e/)
- [Section 7.1: Finite series](./sec71/)
- [Section 7.2: Infinite series](./sec72/)
- [Section 7.3: Sums of non-negative numbers](./sec73/)
- [Section 7.4: Rearrangement of series](./sec74/)
- [Section 7.5: The root and ratio tests](./sec75/)
- [Section 9.1: Subsets of the real line](./sec91/)
- [Section 9.2: The algebra of real-valued functions](./sec92/)
- [Section 9.3: Limiting values of functions](./sec93/)
- [Section 9.4: Continuous functions](./sec94/)
- [Section 9.5: Left and right limits](./sec95/)
- [Section 9.6: The maximum principle](./sec96/)
- [Section 9.7: The intermediate value theorem](./sec97/)
- [Section 9.8: Monotone functions](./sec98/)
- [Section 9.9: Uniform continuity](./sec99/)
- [Section 9.10: Limits at infinity](./sec910/)
- [Section 10.1: Basic definitions](./sec101/)
- [Section 10.2: Local extrema and derivatives](./sec102/)
- [Section 10.3: Monotone functions and derivatives](./sec103/)
- [Section 10.4: The inverse function theorem](./sec104/)
- [Section 10.5: L'Hôpital's rule](./sec105/)
- [Appendix A.1: Mathematical statements](./secA1/)
- [Appendix A.2: Implications](./secA2/)
- [Appendix A.3: The structure of proofs](./secA3/)
- [Appendix A.4: Variables and quantifiers](./secA4/)
- [Appendix A.5: Nested quantifiers](./secA5/)
- [Appendix A.6: Some examples of proofs and quantifiers](./secA6/)
- [Appendix A.7: Equality](./secA7/)
