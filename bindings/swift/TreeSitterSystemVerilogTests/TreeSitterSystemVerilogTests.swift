import XCTest
import SwiftTreeSitter
import TreeSitterSystemverilog

final class TreeSitterSystemverilogTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_systemverilog())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading SystemVerilog grammar")
    }
}
