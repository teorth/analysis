import Analysis.Section_2_1
import Analysis.Section_2_2
import Analysis.Section_2_3
import Analysis.Section_2_epilogue
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_3
import Analysis.Section_3_4
import Analysis.Section_3_5
import Analysis.Section_3_6
import Analysis.Section_3_epilogue
import Analysis.Section_4_1
import Analysis.Section_4_2
import Analysis.Section_4_3
import Analysis.Section_4_4
import Analysis.Section_5_1
import Analysis.Section_5_2
import Analysis.Section_5_3
import Analysis.Section_5_4
import Analysis.Section_5_5
import Analysis.Section_5_6
import Analysis.Section_5_epilogue
import Analysis.Section_6_1
import Analysis.Section_6_2
import Analysis.Section_6_3
import Analysis.Section_6_4
import Analysis.Section_6_5
import Analysis.Section_6_6
import Analysis.Section_6_7
import Analysis.Section_6_epilogue
import Analysis.Section_7_1
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_7_5
import Analysis.Section_8_1
import Analysis.Section_8_2
import Analysis.Section_8_3
import Analysis.Section_8_4
import Analysis.Section_8_5
import Analysis.Section_9_1
import Analysis.Section_9_2
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_9_5
import Analysis.Section_9_6
import Analysis.Section_9_7
import Analysis.Section_9_8
import Analysis.Section_9_9
import Analysis.Section_9_10
import Analysis.Section_10_1
import Analysis.Section_10_2
import Analysis.Section_10_3
import Analysis.Section_10_4
import Analysis.Section_10_5
import Analysis.Section_11_1
import Analysis.Section_11_2
import Analysis.Section_11_3
import Analysis.Section_11_4
import Analysis.Section_11_5
import Analysis.Section_11_6
import Analysis.Section_11_7
import Analysis.Section_11_8
import Analysis.Section_11_9
import Analysis.Section_11_10
import Analysis.Appendix_A_1
import Analysis.Appendix_A_2
import Analysis.Appendix_A_3
import Analysis.Appendix_A_4
import Analysis.Appendix_A_5
import Analysis.Appendix_A_6
import Analysis.Appendix_A_7
import Analysis.Appendix_B_1
import Analysis.Appendix_B_2

import Analysis.Misc.UnitsSystem
import Analysis.Misc.UnitsSystemExamples
import Analysis.Misc.SI
import Analysis.Misc.SIExamples
import Analysis.Misc.FiniteChoice
import Analysis.Misc.Probability
import Analysis.Misc.erdos_379
import Analysis.Misc.erdos_613
import Analysis.Misc.erdos_707
import Analysis.Misc.erdos_987

import Analysis.MeasureTheory.Notation
import Analysis.MeasureTheory.Section_1_1_1
import Analysis.MeasureTheory.Section_1_1_2
import Analysis.MeasureTheory.Section_1_1_3
import Analysis.MeasureTheory.Section_1_2_0
import Analysis.MeasureTheory.Section_1_2_1
import Analysis.MeasureTheory.Section_1_2_2
import Analysis.MeasureTheory.Section_1_2_3
import Analysis.MeasureTheory.Section_1_3_1
import Analysis.MeasureTheory.Section_1_3_2
import Analysis.MeasureTheory.Section_1_3_3
import Analysis.MeasureTheory.Section_1_3_4
import Analysis.MeasureTheory.Section_1_3_5

/-!
 The files in this directory contain a formalization of selected portions of my text [Analysis I](https://terrytao.wordpress.com/books/analysis-i/) into [Lean](https://lean-lang.org/). The formalization is intended to be as faithful a paraphrasing as possible to the original text, while also showcasing Lean's features and syntax. In particular, the formalization is not optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader are rendered in this translation as sorrys. Readers are welcome to fork the repository here to try their hand at these exercises, but I do not intend to place solutions in this repository directly.

While the arrangement of definitions, theorems, and proofs here are closely paraphrasing the textbook, I am refraining from directly quoting material from the textbook, instead providing references to the original text where appropriate. As such, this formalization should be viewed as an annotated companion to the primary text, rather than a replacement for it.

Much of the material in this text is duplicated in Lean's standard math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), though with slightly different definitions. To reconcile these discrepancies, this formalization will gradually transition from the textbook-provided definitions to the Mathlib-provided definitions as one progresses further into the text, thus sacrificing the self-containedness of the formalization in favor of compatibility with Mathlib. For instance, Chapter 2 develops a theory of the natural numbers independent of Mathlib, but all subsequent chapters will use the Mathlib natural numbers instead. (An epilogue to Chapter 2 is provided to show that the two notions of the natural numbers are isomorphic.) As such, this formalization can also be used as an introduction to various portions of Mathlib.

In order to align the formalization with Mathlib conventions, a small number of technical changes have been made to some of the definitions as compared with the textbook version. Most notably:

    Sequences are indexed to start from zero rather than from one, as Mathlib has much more support for the 0-based natural numbers ℕ than the 1-based natural numbers.

    Many operations that are left undefined in the text, such as division by zero, or taking the formal limit of a non-Cauchy sequence, are instead assigned a "junk" value (e.g., 0) to make the operation totally defined. This is because Lean has better support for total functions than partial functions (indiscriminate use of the latter can lead into "dependent type hell" in which even very basic manipulations require quite subtle and delicate proofs). See for instance [this blog post](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/) by Kevin Buzzard for more discussion.

[*Generated documentation*](docs/) is available for the project and its dependencies.
-/
