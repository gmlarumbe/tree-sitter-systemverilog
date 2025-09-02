[![CI](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci.yml/badge.svg)](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci.yml)
[![CI-Bindings](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci_bind.yml/badge.svg)](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci_bind.yml)

# tree-sitter-systemverilog

Full SystemVerilog IEEE 1800-2023 grammar for [tree-sitter](https://github.com/tree-sitter/tree-sitter).

# Differences with [tree-sitter-verilog](https://github.com/tree-sitter/tree-sitter-verilog)

## Pros ##
- Full implementation of the latest SystemVerilog standard (IEEE 1800-2023)
- Robust and reliable: [sv-tests results](https://chipsalliance.github.io/sv-tests-results/)
- Actively maintained
- Implements node fields
- Supports parsing of code snippets (e.g., always block outside of a module)
- Basic preprocessing capabilities
- Thoroughly tested (~3000 tests) including:
  - [UVM 2.0](https://www.accellera.org/downloads/standards/uvm)
  - [sv-tests](https://github.com/chipsalliance/sv-tests)
  - [cva6](https://github.com/openhwgroup/cva6)
  - [pulp_axi](https://github.com/pulp-platform/axi)
  - [basejump_stl](https://github.com/bespoke-silicon-group/basejump_stl)
  - [ucontroller](https://github.com/gmlarumbe/ucontroller)
- Currently used by:
  - Emacs [`verilog-ts-mode`](https://github.com/gmlarumbe/verilog-ts-mode)
  - [`nvim systemverilog`](https://github.com/nvim-treesitter/nvim-treesitter) plugin
  - [`helix`](https://helix-editor.com/)
  - [mergiraf](https://mergiraf.org/)

## Cons
- Generated parser size is larger (~60MB vs ~45MB)
  - Generation of the compiled grammar takes longer (only needs to be done once)

## References

- https://en.wikipedia.org/wiki/Verilog
- http://tree-sitter.github.io/tree-sitter/creating-parsers

