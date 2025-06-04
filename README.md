# Partial Lean formalization of _Analysis I_

The files in this directory contain a formalization of selected portions of my text [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/) into [Lean](https://lean-lang.org/). The formalization is intended to be as faithful a paraphrasing as possible to the original text, while also showcasing Lean's features and syntax.  In particular, the formalization is _not_ optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader are rendered in this translation as `sorry`s.  Readers are welcome to fork the repository here to try their hand at these exercises, but I do not intend to place solutions in this repository directly.

While the arrangement of definitions, theorems, and proofs here are closely paraphrasing the textbook, I am refraining from directly quoting material from the textbook, instead providing references to the original text where appropriate.  As such, this formalization should be viewed as an annotated companion to the primary text, rather than a replacement for it.

Much of the material in this text is duplicated in Lean's standard math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), though with slightly different definitions.  To reconcile these discrepancies, this formalization will gradually transition from the textbook-provided definitions to the Mathlib-provided definitions as one progresses further into the text, thus sacrificing the self-containedness of the formalization in favor of compatibility with Mathlib.  For instance, Chapter 2 develops a theory of the natural numbers independent of Mathlib, but all subsequent chapters will use the Mathlib natural numbers instead.  (An epilogue to Chapter 2 is provided to show that the two notions of the natural numbers are isomorphic.)  As such, this formalization can also be used as an introduction to various portions of Mathlib.

Currently formalized sections:

- [Section 2.1: The Peano axioms](https://teorth.github.io/analysis/docs/Analysis/Section_2_1.html)
- [Section 2.2: Addition](https://teorth.github.io/analysis/docs/Analysis/Section_2_2.html)
- [Section 2.3: Multiplication](https://teorth.github.io/analysis/docs/Analysis/Section_2_3.html)
- [Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers](https://teorth.github.io/analysis/docs/Analysis/Section_2_epilogue.html)
- [Section 3.1: Set theory fundamentals](https://teorth.github.io/analysis/docs/Analysis/Section_3_1.html)
- [Section 4.1: The integers](https://teorth.github.io/analysis/docs/Analysis/Section_4_1.html)
- [Section 4.2: The rationals](https://teorth.github.io/analysis/docs/Analysis/Section_4_2.html)
- [Section 4.3: Absolute value and exponentiation](https://teorth.github.io/analysis/docs/Analysis/Section_4_3.html)
- [Section 5.1: Cauchy sequences of rationals](https://teorth.github.io/analysis/docs/Analysis/Section_5_1.html)
- [Section 5.2: Equivalent Cauchy sequences](https://teorth.github.io/analysis/docs/Analysis/Section_5_2.html)
- [Section 5.3: Construction of the real numbers](https://teorth.github.io/analysis/docs/Analysis/Section_5_3.html)


Other resources:
- [Web page for this project](https://teorth.github.io/analysis/)
- [Web page for the book](https://terrytao.wordpress.com/books/analysis-i/)
  - [Springer edition](https://link.springer.com/book/10.1007/978-981-19-7261-4)
- [How to run a project in Lean locally](https://leanprover-community.github.io/install/project.html)
- [The natural number game](https://adam.math.hhu.de/)
- [The Lean community](https://leanprover-community.github.io/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Blog post announcing this project](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/), Terence Tao, May 31 2025.
- [Lean Zulip discussion about this project](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Lean.20companion.20to.20.22Analysis.20I.22.20-.20discussion/with/521458888)
