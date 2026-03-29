# Lean formalization of _An introduction to measure theory_

The files in this directory contain a formalization of my text [_An introduction to measure theory_](https://terrytao.wordpress.com/books/an-introduction-to-measure-theory/) into [Lean](https://lean-lang.org/). The formalization is intended to be as faithful a paraphrasing as possible to the original text, while also showcasing Lean's features and syntax.  In particular, the formalization is _not_ optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader, as well as many of the proofs in the text are rendered in this translation as `sorry`s.  Readers who are not in my classes are also welcome to submit such proofs.

Some of the material in this text is duplicated in Lean's standard math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), though with slightly different definitions.  To reconcile these discrepancies, this formalization will gradually transition from the textbook-provided definitions to the Mathlib-provided definitions as one progresses further into the text, thus sacrificing the self-containedness of the formalization in favor of compatibility with Mathlib.  For instance, Chapter 2 develops a theory of the natural numbers independent of Mathlib, but all subsequent chapters will use the Mathlib natural numbers instead.  (An epilogue to Chapter 2 is provided to show that the two notions of the natural numbers are isomorphic.)  As such, this formalization can also be used as an introduction to various portions of Mathlib.

## Sections (work in progress)

- Notation section ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Notation.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean))
- Chapter 1: Measure Theory
  - Section 1.1: Prologue: the problem of measure
    - Section 1.1.1: Elementary measure ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_1_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean))
    - Section 1.1.2: Jordan measure ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_1_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean))
    - Section 1.1.3: Connections with the Riemann integral ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_1_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean))
  - Section 1.2: Lebesgue measure
    - Introduction: ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2.lean))
    - Section 1.2.1: Properties of Lebesgue outer measure ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_2_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean))
    - Section 1.2.2: Lebesgue measurability ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_2_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean))
    - Section 1.2.3: Non-measurable sets ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_2_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean))
  - Section 1.3: The Lebesgue integral
    - Section 1.3.1: Integration of simple functions ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_3_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean))
    - Section 1.3.2: Measurable functions ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_3_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean))
    - Section 1.3.3: Unsigned Lebesgue integrals ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_3_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_3.lean))
    - Section 1.3.4: Absolute integrability ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_3_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean))
    - Section 1.3.5: Littlewood's three principles ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_3_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_5.lean))
  - Section 1.4: Abstract measure spaces
    - Section 1.4.1: Boolean algebras ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_4_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_1.lean))
    - Section 1.4.2: $\sigma$-algebras and measurable spaces ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_4_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean))
    - Section 1.4.3: Countably additive measures and measure spaces ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_4_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean))
    - Section 1.4.4: Measurable functions, and integration on a measure space ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_4_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_4.lean))
    - Section 1.4.5: The convergence theorems ([Documentation](https://teorth.github.io/analysis/docs/Analysis/MeasureTheory/Section_1_4_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_5.lean))
  - Section 1.5: Modes of convergence
    - Introduction: (Documentation) (Lean source)
    - Section 1.5.1: Uniqueness (Documentation) (Lean source)
    - Section 1.5.2: The case of a step function (Documentation) (Lean source)
    - Section 1.5.3: Finite measure spaces (Documentation) (Lean source)
    - Section 1.5.4: Domination and uniform integrability (Documentation) (Lean source)
  - Section 1.6: Differentiation theorems
    - Introduction: (Documentation) (Lean source)
    - Section 1.6.1: The Lebesgue differentiation theorem in one dimension (Documentation) (Lean source)
    - Section 1.6.2: The Lebesgue differentiation theorem in higher dimensions (Documentation) (Lean source)
    - Section 1.6.3: Almost everywhere differentiability (Documentation) (Lean source)
  - Section 1.7: Outer measure, pre-measure, and product measures
    - Introduction: (Documentation) (Lean source)
    - Section 1.7.1: Outer measures and the Carathéodory extension theorem (Documentation) (Lean source)
    - Section 1.7.2: Pre-measures (Documentation) (Lean source)
    - Section 1.7.3: Lebesgue-Stieltjes measure (Documentation) (Lean source)
    - Section 1.7.4: Product measure (Documentation) (Lean source)
  - Chapter 2: Related articles _(possible future expansion)_

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
