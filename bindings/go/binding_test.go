package tree_sitter_systemverilog_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_systemverilog "github.com/gmlarumbe/tree-sitter-systemverilog/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_systemverilog.Language())
	if language == nil {
		t.Errorf("Error loading SystemVerilog grammar")
	}
}
