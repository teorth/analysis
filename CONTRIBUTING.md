# Contributing

I would be interested in having volunteers “playtest” the companion to see if this can actually be done (and if the helper lemmas or “API” provided in the Lean files are sufficient to fill in the sorries in a conceptually straightforward manner without having to rely on more esoteric Lean programming techniques). Any other feedback will of course also be welcome.


# Adding a section

1. Add the relevant file to `analysis/Analysis`
2. Copy a line of the `sections` definition in `book/lakefile.lean`, adapt it to the new section.
3. Add a line to the `demoSite` definition in `book/AnalysisBook.lean` for the new section.
4. Adapt the line in the README
5. Add a line in `book/AnalysisBook/Home.lean`