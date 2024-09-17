[![CI](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci.yml/badge.svg)](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci.yml)

# tree-sitter-systemverilog

Full SystemVerilog IEEE 1800-2023 grammar for [tree-sitter](https://github.com/tree-sitter/tree-sitter).

# Differences with [tree-sitter-verilog](https://github.com/tree-sitter/tree-sitter-verilog)

## Pros ##
- Full implementation of the latest SystemVerilog standard (IEEE 1800-2023)
- Robust and reliable: [sv-tests results](https://chipsalliance.github.io/sv-tests-results/)
- Actively maintained
- Thoroughly tested (~2000 tests, including the whole UVM 2.0 and some open source projects)
- Implements node fields
- Supports parsing of code snippets (e.g., always block outside of a module)
- Basic preprocessing capabilities
- Currently used on Emacs `verilog-ts-mode` and `nvim systemverilog` plugin

## Cons
- Generated parser is double the size
  - Generation of the compiled grammar takes longer (this only needs to be done once)

## References

- https://en.wikipedia.org/wiki/Verilog
- http://tree-sitter.github.io/tree-sitter/creating-parsers

