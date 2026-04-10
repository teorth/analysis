# Contributing

I would be interested in having volunteers "playtest" the companion (using downstream forks of the repository) to see if this can actually be done (and if the helper lemmas or "API" provided in the Lean files are sufficient to fill in the sorries in a conceptually straightforward manner without having to rely on more esoteric Lean programming techniques). Any other feedback will of course also be welcome.  However, I do not intend to place solutions in this repository directly.

## Building

```bash
lake exe cache get   # Fetch Mathlib prebuilt cache (run once)
lake build           # Build and verify all proofs
```

The Lean toolchain version is pinned in `lean-toolchain`. Mathlib is pinned in `lakefile.lean`.

## Style conventions

- **Faithfulness over golfing.** Proofs should closely parallel the textbook argument, even if a shorter proof exists. Do not golf or "clean up" existing proofs — this has led to reverts (e.g., [#476]).
- **Textbook definitions first.** Early chapters (especially Ch. 2) use custom definitions, not Mathlib. Later chapters transition to Mathlib. Respect whichever convention the section uses.
- **Verso docstrings.** The project uses `doc.verso = true` for literate documentation. Docstrings use Verso format, not standard Lean doc comments.
- **Line length.** Follow Mathlib convention: 100 characters max.
- **Sorry warnings.** The project suppresses sorry warnings (`-Dwarn.sorry=false` in `lakefile.lean`) by design.

[#476]: https://github.com/teorth/analysis/pull/476

## Adding a section

1. Add the relevant file to `Analysis/`
2. Adapt the line in the README
