# The infinite Ramsey theorem in Lean 4

[![CI](https://github.com/yannpequignot/lean-infinite-ramsey/actions/workflows/ci.yml/badge.svg)](https://github.com/yannpequignot/lean-infinite-ramsey/actions/workflows/ci.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-purple.svg)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)

A single-file, `sorry`-free Lean 4 proof of the **infinite Ramsey theorem at arbitrary
arity**, staged as a candidate Mathlib contribution. It elaborates against Mathlib `v4.28.0`
and depends only on `Mathlib.Data.Fintype.Pigeonhole`, `Mathlib.Data.Nat.Lattice`, and
`Mathlib.Data.Nat.Nth`.

## What it proves

A colouring of the `r`-element subsets of `ℕ` is a function `c : Finset ℕ → κ` (evaluated on
finsets of cardinality `r`); a *monochromatic* set is an infinite `N` all of whose `r`-subsets
get one colour.

| Declaration | Statement |
|---|---|
| `infinite_ramsey (r) (c) (hM : M.Infinite)` | For every finite colouring `c` of the `r`-subsets and every infinite `M ⊆ ℕ`, there is an infinite `N ⊆ M` monochromatic on its `r`-subsets. Proved by **induction on `r`**. |
| `infinite_ramsey_seq` | Enumeration form: the monochromatic set is the range of a `StrictMono e : ℕ → ℕ`. |
| `infinite_ramsey_pairs`, `infinite_ramsey_triples` | The arity `2` (RT²) and `3` (RT³) instances. |

The inductive step is the classical "fan" argument: from an infinite `S`, take the least
element `a`; the link colouring `e ↦ c (insert a e)` drops the arity by one, so the induction
hypothesis at `r` gives an infinite monochromatic successor set. Iterating and a final
pigeonhole on the fan colours yields the monochromatic set at arity `r + 1`.

## Context

This is offered toward the recurring effort to get infinite Ramsey into Mathlib
([#mathlib4 › Infinite Ramsey theory](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Infinite.20Ramsey.20theory);
earlier attempts: [#12167](https://github.com/leanprover-community/mathlib4/pull/12167),
[#12773](https://github.com/leanprover-community/mathlib4/pull/12773),
[#27217](https://github.com/leanprover-community/mathlib4/pull/27217)). It is deliberately
**minimal-import and self-contained** — no dependency PRs, no edits to other files — to sidestep
the `large-import` / `blocked-by-other-PR` issues that stalled several earlier attempts. The
`Finset ℕ` colouring interface follows B. Mehta's (unported) Lean 3 `inf_ramsey.lean`; the prior
Mathlib PRs used a `Fin k ↪o` encoding instead. The final interface, target path, and namespaces
are provisional and for discussion on the Mathlib Zulip.

## Verifying it

```bash
lake exe cache get   # download the prebuilt Mathlib oleans (do this first)
lake build           # kernel-checks the proof
```

To confirm there is no hidden `sorry`, add anywhere in the file:

```lean
#print axioms infinite_ramsey
-- expected: [propext, Classical.choice, Quot.sound]   (no sorryAx)
```

## AI usage

This proof was developed with AI assistance (Aristotle and Claude Code). I understand and stand
behind every statement, and I am offering to do the review and maintenance work through a Mathlib
PR — not to drop generated code on anyone.

## License

Released under the Apache 2.0 license, matching Mathlib. Copyright (c) 2026 Yann Pequignot.
