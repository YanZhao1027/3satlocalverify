# Research context for automation / code assistants

Before making claims about the ten research gates, first read
`research/AGENT_CONTEXT.md`, `research/ten_gates.json` and the relevant
source-linked section in `docs/RESEARCH_GATE_BOARD.md`. The JSON file is the
**only editable gate-state registry**; the Markdown board and JSONL retrieval
cards are generated.

During research, identify the original OpenAI/math revision and the acceptance
criterion. Preserve raw Lean compiler logs, real source-bit execution inputs,
outputs, and reproducibility commands. Distinguish universal kernel proofs from
bounded measurements, single-CNF examples, and offline record integrity checks.

After results or failures, record their scope and limitations in the registry,
append `research/REVIEW_LOG.md` and run:
  python3 scripts/research_board.py --write
  python3 scripts/research_board.py --check
  python3 scripts/research_board.py --search afterCode

Do not change a gate to passed until all acceptance criteria are independently
reproducible and closure evidence is recorded. Do not claim ETH has been refuted
or full upstream #SAT execution from any individual local subroutine result.

This is a repo-local research evidence index, not a running vector database,
automated experiment agent or background GitHub status sync.
