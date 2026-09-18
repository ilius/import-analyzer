# CLAUDE.md

Guidance for Claude Code (and other agents) working in this repository.

## Project

`import-analyzer.py` is a single-file CLI tool that scans a Python project and
keeps `__all__` lists in sync with the symbols the project actually imports and
uses. Given a scan directory it:

1. Resolves the project root by walking up to the nearest `pyproject.toml`.
2. Reads `[tool.import-analyzer]` config from that file (`exclude` and
   `exclude_toplevel_module`).
3. Walks the tree, parses every `.py` file, records imports and attribute
   accesses.
4. For every imported module, computes the symbols missing from its `__all__`
   and either prints them (`--no-modify`) or rewrites the file in place.
5. Opens the modified files in `$IDE` (default `xdg-open`).

## Testing

The tool is regression-tested against two large real-world projects. Output
must stay byte-identical for the same inputs. Run both and compare stdout and
stderr:

```sh
./import-analyzer.py --no-modify ~/starcal
./import-analyzer.py --no-modify ~/pyglossary
```

Both exit 0 and print lists of `__all__` additions. Compare against the
pre-refactor output (see `git show HEAD:import-analyzer.py`) if in doubt.

To test the modify path without touching the real repos, copy a project to a
scratch dir first, e.g. `cp -r ~/starcal /tmp/ia_test/`.

## Architecture notes (post-refactor)

- All top-level executable code was moved into `main()`; the file no longer
  runs config loading, argparse, or analysis at import time.
- State lives in the `ImportAnalyzer` class. The `is_excluded` and
  `moduleFilePath` helpers are `@lru_cache` closures created in
  `_loadConfig()` so they can capture config without module-level globals.
- The old giant `handleStatement` AST dispatcher is replaced by a table-driven
  traversal: `_LEAF_TYPES` (nodes with no children) + `_CHILD_GETTERS`
  (nodes whose traversal differs from "visit every child"). The default is
  `ast.iter_child_nodes`. Keep any new node type in mind when extending:
  `Delete`, `Slice`, `FunctionDef`/`AsyncFunctionDef`, `ClassDef`, `Lambda`,
  `Raise`, and `TypeAlias` deliberately do NOT visit all children.
- `processFile` takes `files` explicitly. Before the refactor it relied on the
  `files` loop variable leaking from the module-level `os.walk`; do not
  reintroduce that implicit global dependency.
- Convention: methods on `ImportAnalyzer` use camelCase (e.g. `processFile`),
  module-level helpers use snake_case. Format with `./format` (ruff format +
  ruff check) and typecheck with `mypy`; both must pass.