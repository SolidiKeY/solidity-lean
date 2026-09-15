@AGENTS.md

## Claude Code

Family conventions live in `.claude/rules/` and load automatically when you
open a matching file — do not read them pre-emptively.

Use the `lean-verify` skill for the edit/check loop here. The `lean-proof`
skill from the leanprover plugin covers general Lean proving technique; the
`mathlib-*` skills do not apply, since this package has no Mathlib.

The Lean MCP server is configured in `.mcp.json`; its Mathlib search tools are
disabled for the same reason.

<!-- Keep this file short: it is loaded into every session, as is AGENTS.md.
     Anything that is only needed when editing a particular family belongs in
     .claude/rules/ with a paths: frontmatter, not here. -->
