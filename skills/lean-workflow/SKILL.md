---
name: lean-workflow
description: Lean proof workflow for breaking problems into minimal examples, using scratch files, and iterating with lake. Use for Lean4/mathlib tasks across repos.
metadata:
  short-description: Lean proof workflow
---

# Lean Workflow

Use this when working on Lean4/mathlib proofs in any repo.

## Core workflow (short)

1. Identify the *first* failing lemma or `sorry`.
2. Create a scratch file with the minimal imports.
3. Reproduce the goal with a tiny example (unnamed theorem).
4. Iterate in small steps; keep it compiling after each step.
5. When it works, port the proof back to the main file and re-run `lake env lean`.

## Practical rules

- Prefer minimal imports first; if unsure, mirror the main file imports.
- Keep the main file compiling; avoid large refactors until proof is stable.
- Use `#check`, `#synth`, `#print`, `#reduce` to inspect goals/types.
- If proofs are slow, isolate them into smaller lemmas and simplify the statement.
- When shrinking imports, avoid `Mathlib.Tactic` by rewriting tactic-only steps (e.g. use `Polynomial.induction_on'` directly instead of `induction'`).
- If `simp` makes no progress on a local `set`/`let`, unfold it explicitly with `simp [name]`.
- Keep this skill doc updated with concise workflow gems discovered during the task.
- When stuck: strip complexity to the smallest failing example, then rebuild from simpler working cases. If still unsolved, report both the minimal failing example and the closest working example side-by-side.

## Scratch-file pattern

- Name: `scratch_<topic>.lean` next to the main file.
- Start with 1-2 trivial examples, then scale up to the real statement.
- Use unnamed `example` blocks to probe the proof state.

## When to consult Claude (non-interactive)

If blocked or a tactic name is unknown:

- Run `claude --help` to see CLI usage.
- Use non-interactive mode:
  - `claude -p "..."`

Keep Claude requests minimal: show the goal, key hypotheses, and the exact error.
