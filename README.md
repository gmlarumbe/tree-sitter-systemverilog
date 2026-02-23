[![CI](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci.yml/badge.svg)](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci.yml)
[![CI-Bindings](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci_bind.yml/badge.svg)](https://github.com/gmlarumbe/tree-sitter-systemverilog/actions/workflows/ci_bind.yml)
[![npm](https://img.shields.io/npm/v/tree-sitter-systemverilog?color=blue)](https://www.npmjs.com/package/tree-sitter-systemverilog)
[![pypi](https://img.shields.io/pypi/v/tree-sitter-systemverilog?color=blue)](https://pypi.org/project/tree-sitter-systemverilog/)
[![crates](https://img.shields.io/crates/v/tree-sitter-systemverilog?color=blue)](https://crates.io/crates/tree-sitter-systemverilog)
[![guix](https://packages.guix.gnu.org/packages/tree-sitter-systemverilog/badges/latest-version.svg)](https://packages.guix.gnu.org/packages/tree-sitter-systemverilog)

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

