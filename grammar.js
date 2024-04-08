/* eslint-disable arrow-parens */
/* eslint-disable camelcase */
/* eslint-disable-next-line spaced-comment */
/* eslint-disable-no-undef */
/* eslint-disable-no-unused-vars */
/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

'use strict';

const PREC = {

  PARENT: 37,     // () [] :: .                                   Left Highest
  UNARY: 36,      // + - ! ~ & ~& | ~| ^ ~^ ^~ ++ -- (unary)
  POW: 35,        // **                                           Left
  MUL: 34,        // * / %                                        Left
  ADD: 33,        // + - (binary)                                 Left
  SHIFT: 32,      // << >> <<< >>>                                Left
  RELATIONAL: 31, // < <= > >= inside dist                        Left
  EQUAL: 30,      // == != === !== ==? !=?                        Left
  AND: 29,        // & (binary)                                   Left
  XOR: 28,        // ^ ~^ ^~ (binary)                             Left
  OR: 27,         // | (binary)                                   Left

  // The matches operator shall have higher precedence than the && and || operators
  MATCHES: 26,

  LOGICAL_AND: 25, // &&                                           Left
  LOGICAL_OR: 24, // ||                                           Left
  CONDITIONAL: 23, // ?: (conditional operator)                    Right
  IMPLICATION: 22, // –> <–>                                       Right
  ASSIGN: 21,     // = += -= *= /= %= &= ^= |= <<= >>= <<<= >>>= := :/ <= None
  CONCAT: 20,     // {} {{}}                            Concatenation   Lowest

  SPARENT: 19,    // [* ] [= ] [-> ]
  SHARP2: 18,     // ##                                                 Left
  throughout: 17, // throughout                                         Right
  within: 16,     // within                                             Left
  intersect: 15,  // intersect                                          Left
  nexttime: 14,   // not, nexttime, s_nexttime
  and: 13,        // and                                                Left
  or: 12,         // or                                                 Left
  iff: 11,        // iff                                                Right
  until: 10,      // until, s_until, until_with, s_until_with, implies  Right
  INCIDENCE: 9,   // |->, |=>, #-#, #=#                                 Right
  always: 8       // always, s_always, eventually, s_eventually,        —
  // if-else, case , accept_on, reject_on,
  // sync_accept_on, sync_reject_on
};

function sepBy1(sep, rule) {
  return seq(rule, repeat(seq(sep, rule)))
}

function sepBy(sep, rule) {
  return optional(sepBy1(sep, rule))
}

function sepBy1prec(sep, precedence, rule) {
  return seq(rule, repeat(prec(precedence, seq(sep, rule))))
}

/**
 *
 * @param {(Rule|string|RegExp)[]} rules
 *
 * @return {ChoiceRule}
 *
 */
function optseq(...rules) {
  return optional(seq(...rules));
}

function enclosing(keyword, identifier) {
  return seq(keyword, optseq(':', identifier));
}


/**
 *
 * @param {(Rule|string|RegExp)[]} rules
 *
 * @return {RepeatRule}
 *
 */
function repseq(...rules) {
  return repeat(seq(...rules));
}

// /**
//  * Creates a rule to match one or more of the rules separated by the separator
//  *
//  * @param {string} separator - The separator to use.
//  * @param {Rule} rule
//  *
//  * @return {PrecLeftRule}
//  *
//  */
// function sep1(separator, rule) {
//   return prec.left(seq(
//     rule,
//     repeat(prec.left(seq(separator, rule)))
//   ));
// }

// /**
//  *
//  * @param {number} precedence
//  * @param {string} separator
//  * @param {Rule} rule
//  *
//  * @returns {PrecLeftRule}
//  *
//  */
// function psep1(precedence, separator, rule) {
//   return prec.left(precedence, seq(
//     rule,
//     repeat(prec.left(seq(separator, rule)))
//   ));
// }

/**
 *
 * @param {GrammarSymbols<string>} $
 * @param {number} prior
 * @param {Rule|string} ops
 *
 * @returns {PrecLeftRule}
 *
 */
function exprOp($, prior, ops) {
  return prec.left(prior, seq($.expression, ops, repeat($.attribute_instance), $.expression));
}

/**
 *
 * @param {GrammarSymbols<string>} $
 * @param {number} prior
 * @param {Rule|string} ops
 *
 * @returns {PrecLeftRule}
 *
 */
function constExprOp($, prior, ops) {
  return prec.left(prior, seq($.constant_expression, ops, repeat($.attribute_instance), $.constant_expression));
}

/**
 *
 * @param {string} command
 *
 * @returns {AliasRule}
 *
 */
function directive(command) {
  return alias(new RegExp('`' + command), 'directive_' + command);
}

/*
    Verilog parser grammar based on IEEE Std 1800-2023.
*/

const rules = {
  // Tree-sitter entry point
  source_file: $ => repeat($._description), // TODO: What about [timeunits_declaration]
  // source_file: $ => seq(optional($.timeunits_declaration), repeat($._description)), // TODO: What about [timeunits_declaration]

// * A.1 Source text
// ** A.1.1 Library source text

  // library_text: $ => repeat($.library_description),

  // library_description: $ => choice(
  //   $.library_declaration,
  //   $.include_statement,
  //   // $.config_declaration,
  //   ';'
  // ),

  // library_declaration: $ => seq(
  //   'library',
  //   $.library_identifier,
  //   sep1(',', $.file_path_spec),
  //   optseq('-incdir', sep1(',', $.file_path_spec)),
  //   ';'
  // ),

  // include_statement: $ => seq('include', $.file_path_spec, ';'),

// ** A.1.2 SystemVerilog source text
  _description: $ => prec('_description', choice(
    $.module_declaration,
    // $.udp_declaration, // TODO: Simplifying debugging
    $.interface_declaration,
    $.program_declaration,
    $.package_declaration,
    seq(repeat($.attribute_instance), choice($._package_item, $.bind_directive)),
    // $.config_declaration, // TODO: Simplifying debugging
    // DANGER: Out of the LRM
    $._directives,
    $.statement_or_null, // have them here to parse snippets
    $._module_item,
    // End of DANGER
  )),

  _module_header: $ => seq( // Not in LRM, groups common tokens of module headers
    repeat($.attribute_instance),
    $.module_keyword,
    optional($.lifetime),
    field('name', $.module_identifier),
    repeat($.package_import_declaration),
    optional($.parameter_port_list)
  ),

  module_nonansi_header: $ => seq(
    $._module_header,
    $.list_of_ports,
    ';'
  ),

  module_ansi_header: $ => seq(
    $._module_header,
    optional($.list_of_port_declarations),
    ';'
  ),

  module_declaration: $ => prec('module_declaration', choice(
    seq( // ANSI
      $.module_nonansi_header,
      optional($.timeunits_declaration),
      repeat($._module_item),
      enclosing('endmodule', $.module_identifier)
    ),
    seq( // nonANSI
      $.module_ansi_header,
      optional($.timeunits_declaration),
      repeat($._non_port_module_item),
      enclosing('endmodule', $.module_identifier)
    ),
    seq( // extern module with dot star as the ports of the module (23.5)
      repeat($.attribute_instance),
      $.module_keyword,
      optional($.lifetime),
      field('name', $.module_identifier),
      '(', '.*', ')', ';',
      optional($.timeunits_declaration),
      repeat($._module_item),
      enclosing('endmodule', $.module_identifier)
    ),
    seq('extern', $.module_nonansi_header),
    seq('extern', $.module_ansi_header)
  )),

  module_keyword: $ => choice('module', 'macromodule'),

  interface_declaration: $ => choice(
    seq(
      $.interface_nonansi_header,
      optional($.timeunits_declaration),
      repeat($.interface_item),
      enclosing('endinterface', $.interface_identifier)
    ),
    seq(
      $.interface_ansi_header,
      optional($.timeunits_declaration),
      repeat($._non_port_interface_item),
      enclosing('endinterface', $.interface_identifier)
    ),
    seq(
      repeat($.attribute_instance),
      'interface',
      field('name', $.interface_identifier),
      '(', '.*', ')', ';',
      optional($.timeunits_declaration),
      repeat($.interface_item),
      enclosing('endinterface', $.interface_identifier)
    ),
    seq('extern', $.interface_nonansi_header),
    seq('extern', $.interface_ansi_header)
  ),

  // Not in LRM, groups common tokens of interface headers
  _interface_header: $ => seq(
    repeat($.attribute_instance),
    'interface',
    optional($.lifetime),
    field('name', $.interface_identifier),
    repeat($.package_import_declaration),
    optional($.parameter_port_list)
  ),

  interface_nonansi_header: $ => seq(
    $._interface_header,
    $.list_of_ports,
    ';'
  ),

  interface_ansi_header: $ => seq(
    $._interface_header,
    optional($.list_of_port_declarations),
    ';'
  ),

  program_declaration: $ => choice(
    seq(
      $.program_nonansi_header,
      optional($.timeunits_declaration),
      repeat($.program_item),
      enclosing('endprogram', $.program_identifier)
    ),
    seq(
      $.program_ansi_header,
      optional($.timeunits_declaration),
      repeat($.non_port_program_item),
      enclosing('endprogram', $.program_identifier)
    ),
    seq(
      repeat($.attribute_instance),
      'program',
      field('name', $.program_identifier),
      '(', '.*', ')', ';',
      optional($.timeunits_declaration),
      repeat($.program_item),
      enclosing('endprogram', $.program_identifier)
    ),
    seq('extern', $.program_nonansi_header),
    seq('extern', $.program_ansi_header)
  ),

  // Not in LRM, groups common tokens of program headers
  _program_header: $ => seq(
    repeat($.attribute_instance),
    'program',
    optional($.lifetime),
    field('name', $.program_identifier),
    repeat($.package_import_declaration),
    optional($.parameter_port_list)
  ),

  program_nonansi_header: $ => seq(
    $._program_header,
    $.list_of_ports,
    ';'
  ),

  program_ansi_header: $ => seq(
    $._program_header,
    optional($.list_of_port_declarations),
    ';'
  ),

  checker_declaration: $ => seq(
    'checker',
    field('name', $.checker_identifier),
    optseq('(', optional($.checker_port_list), ')'),
    ';',
    repseq(repeat($.attribute_instance), $._checker_or_generate_item),
    enclosing('endchecker', $.checker_identifier)
  ),

  class_declaration: $ => seq(
    optional('virtual'),
    'class',
    optional($.final_specifier),
    field('name', $.class_identifier),
    optional($.parameter_port_list),
    optseq(
      'extends',
      $.class_type,
      optseq('(', choice(optional($.list_of_arguments), 'default'), ')')
    ),
    optseq('implements', sepBy1(',', $.interface_class_type)),
    ';',
    repeat($.class_item),
    enclosing('endclass', $.class_identifier)
  ),

  interface_class_declaration: $ => seq(
    'interface', 'class',
    field('name', $.class_identifier),
    optional($.parameter_port_list),
    optseq('extends', optional(sepBy1(',', $.interface_class_type)), ';'),
    repeat($.interface_class_item),
    enclosing('endclass',$.class_identifier)
  ),

  package_declaration: $ => seq(
    repeat($.attribute_instance),
    'package', optional($.lifetime),
    field('name', $.package_identifier), ';',
    optional($.timeunits_declaration),
    repseq(repeat($.attribute_instance), $._package_item),
    enclosing('endpackage',$.package_identifier)
  ),

  timeunits_declaration: $ => choice(
    seq('timeunit', $.time_literal, optseq('/', $.time_literal), ';'),
    seq('timeprecision', $.time_literal, ';'),
    seq('timeunit', $.time_literal, ';', 'timeprecision', $.time_literal, ';'),
    seq('timeprecision', $.time_literal, ';', 'timeunit', $.time_literal, ';')
  ),


// ** A.1.3 Module parameters and ports
  parameter_port_list: $ => seq(
    '#', '(',
    optional(choice(
      seq($.list_of_param_assignments, repseq(',', $.parameter_port_declaration)),
      sepBy1(',', $.parameter_port_declaration)
    )),
    ')'
  ),

  parameter_port_declaration: $ => choice(
    $.any_parameter_declaration,
    seq($.data_type, $.list_of_param_assignments),
    $.type_parameter_declaration,
  ),

  // Only the $.port_reference branch will be possible in a non-ansi declaration
  list_of_ports: $ => seq('(', sepBy(',', alias($.port_reference, $.port)), ')'),

  list_of_port_declarations: $ => seq(
    '(',
    sepBy(',', seq(
      repeat($.attribute_instance),
      $.ansi_port_declaration)
    ),
    ')'
  ),

  port_declaration: $ => seq(
    repeat($.attribute_instance),
    choice(
      $.inout_declaration,
      $.input_declaration,
      $.output_declaration,
      $.ref_declaration,
      $.interface_port_declaration
    )
  ),

  port: $ => choice( // Modified to avoid matching empty string
    $._port_expression,
    seq('.', $.port_identifier, '(', optional($._port_expression), ')')
  ),

  _port_expression: $ => choice(
    $.port_reference,
    seq('{', sepBy1(',', $.port_reference), '}')
  ),

  port_reference: $ => prec('port_reference', seq(
    $.port_identifier,
    optional($.constant_select1)
  )),

  port_direction: $ => prec('port_direction', choice('input', 'output', 'inout', 'ref')),

  // INFO: Drom's one
  net_port_header1: $ => prec('net_port_header1', choice(
    seq(optional($.port_direction), $.net_port_type1),
    $.port_direction
  )),
  // End of INFO

  // INFO: Mine, adapted to 1800-2023
  // INFO: Gave issues with ansi_port_declaration with example:
  //  input clk;
  // net_port_header1: $ => seq(optional($.port_direction), $.net_port_type1),
  // End of INFO

  variable_port_header: $ => prec('variable_port_header', seq(optional($.port_direction), $._variable_port_type)),

  // INFO: Drom's one
  interface_port_header: $ => prec('interface_port_header', seq(
    choice(
      $.interface_identifier,
      'interface'
    ),
    optional(seq('.', $.modport_identifier))
  )),
  // End of INFO

  ansi_port_declaration: $ => prec('ansi_port_declaration', choice(
    prec.dynamic(0, seq(
      optional(choice($.net_port_header1, $.interface_port_header)),
      $.port_identifier,
      repeat(prec('ansi_port_declaration', $.unpacked_dimension)),
      optional(seq('=', $.constant_expression))
    )),
    prec.dynamic(1, seq(
      optional($.variable_port_header),
      $.port_identifier,
      repeat($._variable_dimension),
      optional(seq('=', $.constant_expression))
    )),
    seq(
      optional($.port_direction), '.', $.port_identifier,
      '(', optional($.expression), ')'
    )
  )),

// ** A.1.4 Module items
  severity_system_task: $ => choice(
    // INFO: LRM makes $.finish_number mandatory, but seems tool specific, so relax requirement
    seq('$fatal', optional(seq('(', optional(seq($.finish_number, ',')), optional($.list_of_arguments), ')')), ';'),
    seq(choice('$error', '$warning', '$info'), optional(seq('(', optional($.list_of_arguments), ')')), ';')
  ),

  finish_number: $ => choice('0', '1', '2'),

  // TODO: Maybe inline this one?
  _elaboration_severity_system_task: $ => $.severity_system_task,

  _module_common_item: $ => prec('_module_common_item', choice(
    $._module_or_generate_item_declaration,
  //   $.interface_instantiation,
  //   $.program_instantiation,
    $._assertion_item,
    $.bind_directive,
    $.continuous_assign,
    $.net_alias,
    $.initial_construct,
    $.final_construct,
    $.always_construct,
    $.loop_generate_construct,
    $.conditional_generate_construct,
    $._elaboration_severity_system_task
  )),

  _module_item: $ => choice(
    seq($.port_declaration, ';'),
    $._non_port_module_item
  ),

  module_or_generate_item: $ => prec('module_or_generate_item', seq(
    repeat($.attribute_instance),
    choice(
      $.parameter_override,
      // $.gate_instantiation, // TODO: Removed temporarily to simplify parsing
      // $.udp_instantiation, // TODO: Removed temporarily to simplify parsing
      $.module_instantiation,
      $._module_common_item
    )
  )),

  _module_or_generate_item_declaration: $ => prec('_module_or_generate_item_declaration', choice(
    $.package_or_generate_item_declaration,
    $.genvar_declaration,
    $.clocking_declaration,
    seq('default', 'clocking', $.clocking_identifier, ';'),
    seq('default', 'disable', 'iff', $.expression_or_dist, ';')
  )),

  _non_port_module_item: $ => prec('_non_port_module_item', choice(
    $._directives, // // DANGER: This one is not in the LRM but adds good support for lots of stuff
    $.generate_region,
    $.module_or_generate_item,
    // $.specify_block,
    // seq(repeat($.attribute_instance), $.specparam_declaration), // TODO: Make it simpler
    $.program_declaration,
    $.module_declaration,
    $.interface_declaration,
    $.timeunits_declaration
  )),

  parameter_override: $ => seq(
    'defparam',
    $.list_of_defparam_assignments,
    ';'
  ),

  bind_directive: $ => seq(
    'bind',
    choice(
      seq(
        $.bind_target_scope,
        optional(seq(':', $.bind_target_instance_list))
      ),
      $.bind_target_instance
    ),
    $._bind_instantiation,
    // ';' // INFO: bug in spec, colon already included in $._bind_instantiation
  ),

  bind_target_scope: $ => choice(
    $.module_identifier,
    $.interface_identifier
  ),

  bind_target_instance: $ => seq(
    $.hierarchical_identifier,
    optional($.constant_bit_select1)
  ),

  bind_target_instance_list: $ => sepBy1(',', $.bind_target_instance),

  _bind_instantiation: $ => choice(
    // $.program_instantiation, // TODO: Remove temporarily to narrow conflicts
    $.module_instantiation,
    // $.interface_instantiation, // TODO: Remove temporarily to narrow conflicts
    // $.checker_instantiation // TODO: Remove temporarily to narrow conflicts
  ),

// ** A.1.5 Configuration source text

  // config_declaration: $ => seq(
  //   'config', $.config_identifier, ';',
  //   repseq($.local_parameter_declaration, ';'),
  //   $.design_statement,
  //   repeat($.config_rule_statement),
  //   'endconfig', optseq(':', $.config_identifier)
  // ),

  // design_statement: $ => seq(
  //   'design',
  //   repseq(
  //     optseq($.library_identifier, '.'),
  //     $.cell_identifier
  //   ),
  //   ';'
  // ),

  // config_rule_statement: $ => choice(
  //   seq($.default_clause, $.liblist_clause, ';'),
  //   seq($.inst_clause, $.liblist_clause, ';'),
  //   seq($.inst_clause, $.use_clause, ';'),
  //   seq($.cell_clause, $.liblist_clause, ';'),
  //   seq($.cell_clause, $.use_clause, ';')
  // ),

  // default_clause: $ => 'default',

  // inst_clause: $ => seq('instance', $.inst_name),

  // inst_name: $ => seq($.topmodule_identifier, repseq('.', $.instance_identifier)),

  // cell_clause: $ => seq('cell', optseq($.library_identifier, '.'), $.cell_identifier),

  // liblist_clause: $ => seq('liblist', repeat($.library_identifier)),

  // use_clause: $ => seq(
  //   'use',
  //   choice(
  //     sep1(',', $.named_parameter_assignment),
  //     seq(
  //       optseq($.library_identifier, '.'),
  //       $.cell_identifier,
  //       optional(sep1(',', $.named_parameter_assignment))
  //     )
  //   ),
  //   optseq(':', 'config')
  // ),

// ** A.1.6 Interface items
  interface_or_generate_item: $ => prec('interface_or_generate_item', choice(
    seq(repeat($.attribute_instance), $._module_common_item),
    seq(repeat($.attribute_instance), $.extern_tf_declaration),
    $._directives // INFO: Out of LRM but for convenience
  )),

  extern_tf_declaration: $ => choice(
    seq('extern', $._method_prototype, ';'),
    seq('extern', 'forkjoin', $.task_prototype, ';')
  ),

  interface_item: $ => choice(
    seq($.port_declaration, ';'),
    $._non_port_interface_item
  ),

  _non_port_interface_item: $ => choice(
    $.generate_region,
    $.interface_or_generate_item,
    // $.program_declaration,
    $.modport_declaration,
    $.interface_declaration,
    $.timeunits_declaration
  ),

// ** A.1.7 Program items
  program_item: $ => choice(
    seq($.port_declaration, ';'),
    $.non_port_program_item
  ),

  non_port_program_item: $ => choice(
    seq(repeat($.attribute_instance), $.continuous_assign),
    seq(repeat($.attribute_instance), $._module_or_generate_item_declaration),
    seq(repeat($.attribute_instance), $.initial_construct),
    seq(repeat($.attribute_instance), $.final_construct),
    seq(repeat($.attribute_instance), $.concurrent_assertion_item),
    $.timeunits_declaration,
    // $._program_generate_item
  ),

  _program_generate_item: $ => choice(
    // $.loop_generate_construct,
    // TODO
    // $.conditional_generate_construct,
    // $.generate_region,
    // $._elaboration_severity_system_task
  ),

// ** A.1.8 Checker items
  checker_port_list: $ => sepBy1(',', $.checker_port_item),

  checker_port_item: $ => seq( // TODO
    repeat($.attribute_instance),
    optional($.checker_port_direction),
    optional($.property_formal_type1),
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optseq('=', $._property_actual_arg)
  ),

  checker_port_direction: $ => choice('input', 'output'),

  _checker_or_generate_item: $ => choice(
    $.checker_or_generate_item_declaration,
    $.initial_construct,
    $.always_construct,
    $.final_construct,
    $._assertion_item,
    $.continuous_assign,
    $._checker_generate_item,
    // INFO: Out of LRM: This is a workaround to support checker_instantiations and
    // avoid multiple conflicts with module/interface/program instantiations.
    // The proper way to do it would be uncommenting the $.checker_instantiation
    // in $.concurrent_assertion_item and removing the one below
    $.checker_instantiation
  ),

  checker_or_generate_item_declaration: $ => choice(
    seq(optional('rand'), $.data_declaration),
    $.function_declaration,
    $.checker_declaration,
    $._assertion_item_declaration,
    $.covergroup_declaration,
    $.genvar_declaration,
    $.clocking_declaration,
    seq('default', 'clocking', $.clocking_identifier, ';'),
    // prec.right(PREC.iff, seq('default', 'disable', 'iff', $.expression_or_dist, ';')),
    seq('default', 'disable', 'iff', $.expression_or_dist, ';'),
    ';'
  ),

  _checker_generate_item: $ => choice(
    $.loop_generate_construct,
    $.conditional_generate_construct,
    $.generate_region,
    $._elaboration_severity_system_task
  ),

// ** A.1.9 Class items
  class_item: $ => choice(
    $._directives, // INFO: Out of LRM but useful for basic parsing in the UVM
    seq(repeat($.attribute_instance), $.class_property),
    seq(repeat($.attribute_instance), $.class_method),
    seq(repeat($.attribute_instance), $._class_constraint),
    seq(repeat($.attribute_instance), $.class_declaration),
    seq(repeat($.attribute_instance), $.interface_class_declaration),
    seq(repeat($.attribute_instance), $.covergroup_declaration),
    seq($.any_parameter_declaration, ';'),
    ';'
  ),

  class_property: $ => prec('class_property', choice(
    seq(repeat($._property_qualifier), $.data_declaration),
    seq(
      'const',
      repeat($.class_item_qualifier),
      $.data_type,
      $.const_identifier,
      optional(seq('=', $.constant_expression)),
      ';'
    )
  )),

  class_method: $ => prec('class_method', choice(
    seq(repeat($.method_qualifier), $.task_declaration),
    seq(repeat($.method_qualifier), $.function_declaration),
    seq('pure', 'virtual', repeat($.class_item_qualifier), $._method_prototype, ';'),
    seq('extern', repeat($.method_qualifier), $._method_prototype, ';'),
    seq(repeat($.method_qualifier), $.class_constructor_declaration),
    seq('extern', repeat($.method_qualifier), $.class_constructor_prototype)
  )),

  class_constructor_prototype: $ => seq(
    'function',
    'new',
    optional(seq('(', optional($.class_constructor_arg_list), ')')),
    ';'
  ),

  class_constructor_arg_list: $ => sepBy1(',', $.class_constructor_arg),

  class_constructor_arg: $ => choice($.tf_port_item1, 'default'),

  interface_class_item: $ => choice(
    $.type_declaration,
    seq(repeat($.attribute_instance), $.interface_class_method),
    seq($.any_parameter_declaration, ';'),
    ';'
  ),

  interface_class_method: $ => seq('pure', 'virtual', $._method_prototype, ';'),

  _class_constraint: $ => choice(
    $.constraint_prototype,
    $.constraint_declaration
  ),

  class_item_qualifier: $ => prec('class_item_qualifier', choice('static', 'protected', 'local')),

  _property_qualifier: $ => choice(
    $.random_qualifier,
    $.class_item_qualifier
  ),

  random_qualifier: $ => choice('rand', 'randc'),

  method_qualifier: $ => prec('method_qualifier', choice(
    seq(optional('pure'), 'virtual'),
    $.class_item_qualifier
  )),

  _method_prototype: $ => choice(
    $.task_prototype,
    $.function_prototype
  ),

  class_constructor_declaration: $ => prec('class_constructor_declaration', seq(
    'function',
    optional($.class_scope),
    'new',
    optional(seq('(', optional($.class_constructor_arg_list), ')')),
    ';',
    repeat($.block_item_declaration),
    optional(seq('super', '.', 'new', optional(seq('(', optional($.list_of_arguments), ')')), ';')),
    repeat($.function_statement_or_null),
    'endfunction', optional(seq(':', 'new'))
  )),

// ** A.1.10 Constraints

  constraint_declaration: $ => seq(
    optional('static'),
    'constraint',
    optional($.dynamic_override_specifiers),
    $.constraint_identifier,
    $.constraint_block
  ),

  constraint_block: $ => seq('{', repeat($.constraint_block_item), '}'),

  constraint_block_item: $ => choice(
    seq('solve', $.solve_before_list, 'before', $.solve_before_list, ';'),
    $.constraint_expression
  ),

  solve_before_list: $ => sepBy1(',', $.constraint_primary),

  constraint_primary: $ => seq(
    optional(choice(
      seq($.implicit_class_handle, '.'),
      $.class_scope
    )),
    $.hierarchical_identifier,
    optional($.select1),
    optional(seq('(', ')'))
  ),

  // constraint_expression: $ => choice(
  //   seq(optional('soft'), $.expression_or_dist, ';'),
  //   seq($.uniqueness_constraint, ';'),
  //   prec.right(PREC.IMPLICATION, seq($.expression, '–>', $.constraint_set)),
  //   prec.left(seq(
  //     'if', '(', $.expression, ')', $.constraint_set,
  //     optseq('else', $.constraint_set)
  //   )),
  //   seq(
  //     'foreach', '(',
  //     $.ps_or_hierarchical_array_identifier,
  //     '[', optional($.loop_variables1), ']',
  //     ')',
  //     $.constraint_set
  //   ),
  //   seq('disable', 'soft', $.constraint_primary, ';')
  // ),
  constraint_expression: $ => choice(
    seq(optional('soft'), $.expression_or_dist, ';'),
    seq($.uniqueness_constraint, ';'),
    prec.right(PREC.IMPLICATION, seq($.expression, '–>', $.constraint_set)),
    prec.left(seq(
      'if', '(', $.expression, ')', $.constraint_set,
      optional(seq('else', $.constraint_set))
    )),
    seq(
      'foreach', '(',
      $.ps_or_hierarchical_array_identifier,
      '[', optional($.loop_variables1), ']',
      ')',
      $.constraint_set
    ),
    seq('disable', 'soft', $.constraint_primary, ';')
  ),

  uniqueness_constraint: $ => seq(
    'unique', '{', $.range_list, '}'
  ),

  constraint_set: $ => prec('constraint_set', choice(
    $.constraint_expression,
    seq('{', repeat($.constraint_expression), '}')
  )),

  dist_list: $ => sepBy1(',', $.dist_item),

  dist_item: $ => choice(
    seq($.value_range, optional($.dist_weight)),
    seq('default', ':/', $.expression)
  ),

  dist_weight: $ => seq(choice(':=', ':/'), $.expression),

  constraint_prototype: $ => seq(
    optional($.constraint_prototype_qualifier),
    optional('static'),
    'constraint',
    $.constraint_identifier,
    optional($.dynamic_override_specifiers),
    ';'
  ),

  constraint_prototype_qualifier: $ => choice('extern', 'pure'),

  extern_constraint_declaration: $ => seq(
    optional('static'),
    'constraint',
    optional($.dynamic_override_specifiers),
    $.class_scope,
    $.constraint_identifier,
    $.constraint_block
  ),

  identifier_list: $ => sepBy1(',', $._identifier),


// ** A.1.11 Package items
  _package_item: $ => prec('_package_item', choice(
    $.package_or_generate_item_declaration,
    // $.anonymous_program,
    $.package_export_declaration,
    // $.timeunits_declaration
  )),

  package_or_generate_item_declaration: $ => prec('package_or_generate_item_declaration', choice(
    prec.dynamic(0, $.net_declaration),
    prec.dynamic(1, $.data_declaration),
    $.task_declaration,
    $.function_declaration,
    $.checker_declaration,
    $.dpi_import_export,
    $.extern_constraint_declaration,
    $.class_declaration,
    $.interface_class_declaration,
    $.class_constructor_declaration,
    seq($.any_parameter_declaration, ';'),
    $.covergroup_declaration,
    $._assertion_item_declaration,
    ';',
    $._directives  // DANGER: Out of LRM
  )),

  // anonymous_program: $ => seq(
  //   'program', ';', repeat($.anonymous_program_item), 'endprogram'
  // ),

  // anonymous_program_item: $ => choice(
  //   $.task_declaration,
  //   $.function_declaration,
  //   $.class_declaration,
  //   $.covergroup_declaration,
  //   $.class_constructor_declaration,
  //   ';'
  // ),

// * A.2 Declarations
// ** A.2.1 Declaration types
// *** A.2.1.1 Module parameter declarations
  local_parameter_declaration: $ => seq(
    'localparam',
    choice(
      seq(optional($.data_type_or_implicit1), $.list_of_param_assignments),
      $.type_parameter_declaration,
    )),

  parameter_declaration: $ => seq(
    'parameter',
    choice(
      seq(optional($.data_type_or_implicit1), $.list_of_param_assignments),
      $.type_parameter_declaration,
    )),

  _forward_type: $ => choice('enum', 'struct', 'union', 'class', 'interface class'),

  type_parameter_declaration: $ => seq(
    'type',
    optional($._forward_type),
    $.list_of_type_assignments
  ),

  any_parameter_declaration: $ => choice(
    $.local_parameter_declaration,
    $.parameter_declaration
  ),

  // specparam_declaration: $ => seq(
  //   'specparam',
  //   optional($.packed_dimension),
  //   $.list_of_specparam_assignments,
  //   ';'
  // ),

// *** A.2.1.2 Port declarations

  inout_declaration: $ => seq(
    'inout', optional($.net_port_type1), $.list_of_port_identifiers
  ),

  input_declaration: $ => seq(
    'input',
    choice(
      prec.dynamic(0, seq(optional($.net_port_type1), $.list_of_port_identifiers)),
      prec.dynamic(1, seq(optional($._variable_port_type), $.list_of_variable_identifiers))
    )
  ),

  output_declaration: $ => seq(
    'output',
    choice(
      prec.dynamic(0, seq(optional($.net_port_type1), $.list_of_port_identifiers)),
      prec.dynamic(1, seq(optional($._variable_port_type), $.list_of_variable_port_identifiers))
    )
  ),

  interface_port_declaration: $ => prec('interface_port_declaration', seq(
    $.interface_identifier,
    optional(seq('.', $.modport_identifier)),
    $.list_of_interface_identifiers
  )),

  ref_declaration: $ => seq(
    'ref', $._variable_port_type, $.list_of_variable_identifiers
  ),

// *** A.2.1.3 Type declarations
  data_declaration: $ => choice(
    seq(
      optional('const'),
      // In a data_declaration, it shall be illegal to omit the explicit data_type
      // before a list_of_variable_decl_assignments unless the var keyword is used.

      // TODO: Maybe use $._var_data_type ? And replace it with these contents?
      // INFO: I think it's not an option because _var_data_type doesn't have
      // the automatic/static lifetime into account
      choice(
        seq('var', optional($.lifetime), optional($.data_type_or_implicit1)),
        seq(optional($.lifetime), $.data_type_or_implicit1),
      ),
      $.list_of_variable_decl_assignments,
      ';'
    ),
    $.type_declaration,
    $.package_import_declaration,
    $.nettype_declaration
  ),

  // INFO: Original one
  // package_import_declaration: $ => seq(
  //   'import', sep1(',', $.package_import_item), ';'
  // ),
  // End of INFO

  // INFO: Mine, without precedences. WIP
  package_import_declaration: $ => seq(
    'import',
    $.package_import_item, repeat(seq($.package_import_item, ",")),
    ';'
  ),
  // End of INFO

  package_import_item: $ => seq(
    $.package_identifier, '::', choice($._identifier, '*')
  ),

  package_export_declaration: $ => seq(
    'export', choice('*::*', sepBy1(',', $.package_import_item)), ';'
  ),

  genvar_declaration: $ => seq(
    'genvar', $.list_of_genvar_identifiers, ';'
  ),

  net_declaration: $ => prec('net_declaration', choice(
    seq(
      $.net_type,
      optional(choice($.drive_strength, $.charge_strength)),
      optional(choice('vectored', 'scalared')),
      optional($.data_type_or_implicit1),
      optional($.delay3), // TODO: Removed temporarily by Larumbe
      $.list_of_net_decl_assignments,
      ';'
    ),
    seq(
      $._net_type_identifier,
      optional($.delay_control),
      $.list_of_net_decl_assignments,
      ';'
    ),
    // seq(
    //   'interconnect',
    //   optional($.implicit_data_type1),
    //   optseq('#', $.delay_value),
    //   sep1(',', seq($._net_identifier, repeat($.unpacked_dimension))),
    //   ';'
    // )
  )),

  // type_declaration: $ => seq(
  //   'typedef',
  //   choice(
  //     seq($.data_type, $._type_identifier, repeat($._variable_dimension)),
  //     seq(
  //       $.interface_instance_identifier, optional($.constant_bit_select1),
  //       '.', $._type_identifier, $._type_identifier
  //     ),
  //     seq(
  //       optional(choice(
  //         'enum', 'struct', 'union', 'class', seq('interface', 'class')
  //       )),
  //       $._type_identifier
  //     )
  //   ),
  //   ';'
  // ),
  type_declaration: $ => seq(
    'typedef',
    choice(
      seq($.data_type_or_incomplete_class_scoped_type, $._type_identifier, repeat($._variable_dimension)),
      seq($.interface_port_identifier, optional($.constant_bit_select1), '.', $._type_identifier, $._type_identifier),
      seq(optional($._forward_type), $._type_identifier)
    ),
    ';'
  ),

  data_type_or_incomplete_class_scoped_type: $ => prec('data_type_or_incomplete_class_scoped_type', choice(
    $.data_type,
    $.incomplete_class_scoped_type
  )),

  // incomplete_class_scoped_type :: =
  //    type_identifier :: type_identifier_or_class_type
  //    | incomplete_class_scoped_type :: type_identifier_or_class_type
  //
  incomplete_class_scoped_type: $ => prec('incomplete_class_scoped_type', choice(
    seq($._type_identifier, '::', $.type_identifier_or_class_type),
    $.incomplete_class_scoped_type, '::', $.type_identifier_or_class_type
  )),


  type_identifier_or_class_type: $ => choice($._type_identifier, $.class_type),

  nettype_declaration: $ => prec('nettype_declaration', seq(
    'nettype',
    choice(
      seq(
        $.data_type,
        $._net_type_identifier,
        optional(seq(
          'with',
          optional(choice($.package_scope, $.class_scope)),
          $.tf_identifier
        ))
      ),
      seq(
        optional(choice($.package_scope, $.class_scope)),
        $._net_type_identifier,
        $._net_type_identifier
      )
    ),
    ';'
  )),

  lifetime: $ => prec('lifetime', choice('static', 'automatic')),


// ** A.2.2 Declaration data types
// *** A.2.2.1 Net and variable types
  casting_type: $ => prec('casting_type', choice(
    $._simple_type,
    $.constant_primary,
    $._signing,
    'string',
    'const'
  )),

  data_type: $ => prec('data_type', choice(
    prec.right(seq($.integer_vector_type, optional($._signing), repeat($.packed_dimension))),
    seq($.integer_atom_type, optional($._signing)),
    $.non_integer_type,
    seq(
      $.struct_union,
      optional(seq('packed', optional($._signing))),
      // '{', repeat1($.struct_union_member), '}',
      '{', repeat1(choice($._directives, $.struct_union_member)), '}', // INFO: _directives out of LRM, for sv-tests/generic/typedef tests
      repeat($.packed_dimension)
    ),
    seq(
      'enum', optional($.enum_base_type),
      // '{', sepBy1(',', $.enum_name_declaration), '}',
      '{', choice($._directives, sepBy1(',', $.enum_name_declaration)), '}', // INFO: _directives out of LRM, for sv-tests/generic/typedef tests
      repeat($.packed_dimension)
    ),
    'string',
    'chandle',
    seq(
      'virtual', optional('interface'),
      $.interface_identifier,
      optional($.parameter_value_assignment),
      optional(seq('.', $.modport_identifier))
    ),
    seq(
      optional(choice($.class_scope, $.package_scope)),
      $._type_identifier,
      repeat($.packed_dimension)
    ),
    $.class_type,
    // 'event',
    // $.ps_covergroup_identifier,
    $.type_reference
  )),

  data_type_or_implicit1: $ => prec('data_type_or_implicit1', choice(
    $.data_type,
    $.implicit_data_type1
  )),

  // INFO: Original by Drom, changed from standard to avoid matching the empty string
  implicit_data_type1: $ => prec.right(choice( // reordered : repeat -> repeat1
    seq($._signing, repeat($.packed_dimension)),
    repeat1($.packed_dimension)
  )),
  // End of INFO

  enum_base_type: $ => choice(
    seq($.integer_atom_type, optional($._signing)),
    seq($.integer_vector_type, optional($._signing), optional($.packed_dimension)),
    seq($._type_identifier, optional($.packed_dimension))
  ),

  enum_name_declaration: $ => seq(
    $.enum_identifier,
    optional(seq(
      '[', $.integral_number, optional(seq(':', $.integral_number)), ']'
    )),
    optional(seq('=', $.constant_expression))
  ),

  class_scope: $ => seq($.class_type, '::'),

  class_type: $ => prec('class_type', seq(
    $.ps_class_identifier,
    optional($.parameter_value_assignment),
    repeat(prec('class_type', seq('::', $.class_identifier, optional($.parameter_value_assignment))))
  )),

  interface_class_type: $ => seq(
    $.ps_class_identifier,
    optional($.parameter_value_assignment)
  ),

  _integer_type: $ => choice(
    $.integer_vector_type,
    $.integer_atom_type
  ),

  integer_atom_type: $ => choice('byte', 'shortint', 'int', 'longint', 'integer', 'time'),

  integer_vector_type: $ => choice('bit', 'logic', 'reg'),

  non_integer_type: $ => choice('shortreal', 'real', 'realtime'),

  net_type: $ => choice('supply0', 'supply1', 'tri', 'triand', 'trior', 'trireg', 'tri0', 'tri1', 'uwire', 'wire', 'wand', 'wor'),

  // INFO: Original by drom
  // net_port_type1: $ => choice(
  //   prec.left(-1, seq($.net_type, $.data_type_or_implicit1)),
  //   $.net_type,
  //   $.data_type_or_implicit1,

  //   $._net_type_identifier,
  //   seq('interconnect', optional($.implicit_data_type1))
  // ),
  // End of INFO

  // INFO: Larumbe's one
  net_port_type1: $ => prec('net_port_type1', choice( // Reorder, avoid matching empty string
    seq($.net_type, $.data_type_or_implicit1),
    $.net_type,
    $.data_type_or_implicit1,
    $._net_type_identifier,
    seq('interconnect', optional($.implicit_data_type1))
  )),
  // End of INFO

  _variable_port_type: $ => $._var_data_type,

  _var_data_type: $ => prec('_var_data_type', choice(
    $.data_type,
    seq('var', optional($.data_type_or_implicit1))
  )),

  _signing: $ => choice('signed', 'unsigned'),

  _simple_type: $ => prec('_simple_type', choice(
    $._integer_type,
    $.non_integer_type,
    $.ps_type_identifier,
    $.ps_parameter_identifier
  )),

  struct_union_member: $ => seq(
    repeat($.attribute_instance),
    optional($.random_qualifier),
    $.data_type_or_void,
    $.list_of_variable_decl_assignments,
    ';'
  ),

  data_type_or_void: $ => choice(
    $.data_type,
    'void'
  ),

  struct_union: $ => choice(
    'struct',
    seq('union', optional(choice('soft', 'tagged')))
  ),

  type_reference: $ => seq(
    'type', '(',
    choice(
      $.expression,
      $.data_type_or_incomplete_class_scoped_type
    ),
    ')'
  ),

// *** A.2.2.2 Strengths

  drive_strength: $ => seq(
    '(',
    choice(
      seq($.strength0, ',', $.strength1),
      seq($.strength1, ',', $.strength0),
      seq($.strength0, ',', 'highz1'),
      seq($.strength1, ',', 'highz0'),
      seq('highz0', ',', $.strength1),
      seq('highz1', ',', $.strength0)
    ),
    ')'
  ),

  strength0: $ => choice('supply0', 'strong0', 'pull0', 'weak0'),

  strength1: $ => choice('supply1', 'strong1', 'pull1', 'weak1'),

  charge_strength: $ => seq('(', choice('small', 'medium', 'large'), ')'),

// *** A.2.2.3 Delays
  delay3: $ => seq('#', choice(
    $.delay_value,
    seq(
      '(',
      $.mintypmax_expression,
      optional(seq($.mintypmax_expression, optional($.mintypmax_expression))),
      ')'
    ))),

  // delay2: $ => seq('#', choice(
  //   $.delay_value,
  //   seq('(', $.mintypmax_expression, optional($.mintypmax_expression), ')')
  // )),

  delay_value: $ => choice(
    $.unsigned_number,
    $.real_number,
    $.ps_identifier,
    $.time_literal,
    '1step'
  ),

// ** A.2.3 Declaration lists
  list_of_defparam_assignments: $ => sepBy1(',', $.defparam_assignment),

  list_of_genvar_identifiers: $ => sepBy1(',', $.genvar_identifier),

  list_of_interface_identifiers: $ => sepBy1(',', seq(
    $.interface_identifier,
    repeat($.unpacked_dimension)
  )),

  list_of_net_decl_assignments: $ => sepBy1(',', $.net_decl_assignment),

  // list_of_param_assignments: $ => sep1(',', $.param_assignment),
  // list_of_param_assignments: $ => prec.right(sepBy1(',', $.param_assignment)),
  // list_of_param_assignments: $ => prec.left(sepBy1(',', $.param_assignment)),
  list_of_param_assignments: $ => sepBy1(',', $.param_assignment),

  // INFO: Original by drom
  // list_of_port_identifiers: $ => sep1(',', seq(
  //   $.port_identifier,
  //   repeat($.unpacked_dimension)
  // )),
  // End of INFO:

  // INFO: Larumbe's one
  list_of_port_identifiers: $ => prec('list_of_port_identifiers', sepBy1prec(',', 'list_of_port_identifiers', seq(
    $.port_identifier,
    repeat(prec('list_of_port_identifiers', $.unpacked_dimension))
  ))),
  // End of INFO


  // list_of_udp_port_identifiers: $ => sep1(',', $.port_identifier),

  // list_of_specparam_assignments: $ => sep1(',', $.specparam_assignment),

  list_of_tf_variable_identifiers: $ => sepBy1(',', seq(
    $.port_identifier,
    repeat($._variable_dimension),
    optional(seq('=', $.expression))
  )),

  // list_of_type_assignments: $ => sep1(',', $.type_assignment),
  // list_of_type_assignments: $ => prec.right(sepBy1(',', $.type_assignment)),
  // list_of_type_assignments: $ => prec.left(sepBy1(',', $.type_assignment)),
  list_of_type_assignments: $ => sepBy1(',', $.type_assignment),

  list_of_variable_decl_assignments: $ => sepBy1(',', $.variable_decl_assignment),

  list_of_variable_identifiers: $ => prec('list_of_variable_identifiers', sepBy1prec(',', 'list_of_variable_identifiers', seq(
    $._variable_identifier,
    repeat(prec('list_of_variable_identifiers', $._variable_dimension))
  ))),

  list_of_variable_port_identifiers: $ => prec('list_of_variable_port_identifiers', sepBy1prec(',', 'list_of_variable_port_identifiers', seq(
    $.port_identifier,
    repeat(prec('list_of_variable_port_identifiers', $._variable_dimension)),
    optional(seq('=', $.constant_expression))
  ))),

// ** A.2.4 Declaration assignments
  defparam_assignment: $ => seq(
    $._hierarchical_parameter_identifier,
    '=',
    $.constant_mintypmax_expression
  ),

  // INFO: Original by drom
  // net_decl_assignment: $ => prec.left(PREC.ASSIGN, seq(
  //   $._net_identifier,
  //   repeat($.unpacked_dimension),
  //   optseq('=', $.expression)
  // )),
  // End of INFO

  // INFO: Larumbe's one
  net_decl_assignment: $ => seq(
    $._net_identifier,
    repeat($.unpacked_dimension),
    optional(seq('=', $.expression))
  ),
  // End of INFO

  param_assignment: $ => seq(
    $.parameter_identifier,
    repeat($._variable_dimension),
    optional(seq('=', $.constant_param_expression))
  ),

  // specparam_assignment: $ => choice(
  //   seq($.specparam_identifier, '=', $.constant_mintypmax_expression),
  //   $.pulse_control_specparam
  // ),

  // type_assignment: $ => seq(
  //   $._type_identifier,
  //   optseq('=', $.data_type)
  // ),
  type_assignment: $ => seq(
    $._type_identifier,
    optional(seq('=', $.data_type))
  ),

  // pulse_control_specparam: $ => choice(
  //   seq(
  //     'PATHPULSE$=',
  //     '(',
  //     $.reject_limit_value,
  //     optseq(',', $.error_limit_value),
  //     ')'
  //   )
  //   // seq(
  //   //   'PATHPULSE$',
  //   //   $.specify_input_terminal_descriptor,
  //   //   '$',
  //   //   $.specify_output_terminal_descriptor,
  //   //   '=', '(', $.reject_limit_value, optseq(',', $.error_limit_value), ')'
  //   // )
  // ),

  // error_limit_value: $ => $.limit_value,

  // reject_limit_value: $ => $.limit_value,

  // limit_value: $ => $.constant_mintypmax_expression,

  variable_decl_assignment: $ => choice(
    seq(
      $._variable_identifier,
      repeat($._variable_dimension),
      optional(seq('=', $.expression))
    ),
    seq(
      $.dynamic_array_variable_identifier,
      $.unsized_dimension,
      repeat($._variable_dimension),
      optional(seq('=', $.dynamic_array_new))
    ),
    seq(
      $.class_variable_identifier,
      optional(seq('=', $.class_new))
    )
  ),

  class_new: $ => choice(
    prec.dynamic(1, seq(optional($.class_scope), 'new', optional(seq('(', optional($.list_of_arguments), ')')))),
    prec.dynamic(0, seq('new', $.expression))
  ),

  dynamic_array_new: $ => seq(
    'new', '[', $.expression, ']', optional(seq('(', $.expression, ')'))
  ),

// ** A.2.5 Declaration ranges
  unpacked_dimension: $ => prec('unpacked_dimension', seq(
    '[',
    choice(
      $.constant_range,
      $.constant_expression
    ),
    ']'
  )),

  packed_dimension: $ => prec('packed_dimension', choice(
    seq('[', $.constant_range, ']'),
    $.unsized_dimension
  )),

  associative_dimension: $ => seq(
    '[', choice($.data_type, '*'), ']'
  ),

  _variable_dimension: $ => prec('_variable_dimension', choice(
    $.unsized_dimension,
    prec.dynamic(0, $.unpacked_dimension),
    $.associative_dimension,
    prec.dynamic(1, $.queue_dimension)
  )),

  queue_dimension: $ => prec('queue_dimension', seq(
    '[', '$', optional(seq(':', $.constant_expression)), ']'
  )),

  unsized_dimension: $ => seq('[', ']'),

// ** A.2.6 Function declarations
  function_data_type_or_implicit1: $ => choice(
    $.data_type_or_void,
    $.implicit_data_type1
  ),

  function_declaration: $ => seq(
    'function',
    optional($.dynamic_override_specifiers),
    optional($.lifetime),
    $.function_body_declaration
  ),

  function_body_declaration: $ => seq(
    optional($.function_data_type_or_implicit1),
    optional(choice(
      seq($.interface_identifier, '.'),
      $.class_scope
    )),
    $.function_identifier,
    choice(
      seq(';', repeat($.tf_item_declaration)),
      seq('(', optional($.tf_port_list), ')', ';', repeat($.block_item_declaration))
    ),
    repeat($.function_statement_or_null),
    'endfunction',
    optional(seq(':', $.function_identifier))
  ),

  function_prototype: $ => seq(
    'function',
    optional($.dynamic_override_specifiers),
    $.data_type_or_void,
    $.function_identifier,
    optional(seq('(', optional($.tf_port_list), ')'))
  ),

  dpi_import_export: $ => choice(
    seq(
      'import',
      $.dpi_spec_string,
      optional($.dpi_function_import_property),
      optional(seq($.simple_identifier, '=')), // TODO: Change to $c_identifier: might it have to do with tree-sitter $word => ?
      // optional(seq($.c_identifier, '=')),
      $.dpi_function_proto,
      ';'
    ),
    seq(
      'import',
      $.dpi_spec_string,
      optional($.dpi_task_import_property),
      optional(seq($.simple_identifier, '=')), // TODO: Change to $c_identifier: might it have to do with tree-sitter $word => ?
      // optional(seq($.c_identifier, '=')),
      $.dpi_task_proto,
      ';'
    ),
    seq(
      'export',
      $.dpi_spec_string,
      optional(seq($.simple_identifier, '=')), // TODO: Change to $c_identifier: might it have to do with tree-sitter $word => ?
      // optional(seq($.c_identifier, '=')),
      'function',
      $.function_identifier,
      ';'
    ),
    seq(
      'export',
      $.dpi_spec_string,
      optional(seq($.simple_identifier, '=')), // TODO: Change to $c_identifier: might it have to do with tree-sitter $word => ?
      // optional(seq($.c_identifier, '=')),
      'task',
      $.task_identifier,
      ';'
    )
  ),

  dpi_spec_string: $ => choice('"DPI-C"', '"DPI"'),

  dpi_function_import_property: $ => choice('context', 'pure'),

  dpi_task_import_property: $ => 'context',

  dpi_function_proto: $ => $.function_prototype,

  dpi_task_proto: $ => $.task_prototype,


// ** A.2.7 Task declarations
  task_declaration: $ => seq(
    'task',
    optional($.dynamic_override_specifiers),
    optional($.lifetime),
    $.task_body_declaration
  ),

  task_body_declaration: $ => seq(
    optional(choice(
      seq($.interface_identifier, '.'),
      $.class_scope
    )),
    $.task_identifier,
    choice(
      seq(
        ';',
        repeat($.tf_item_declaration)
      ),
      seq(
        '(', optional($.tf_port_list), ')', ';',
        repeat($.block_item_declaration)
      )
    ),
    repeat($.statement_or_null),
    'endtask',
    optional(seq(':', $.task_identifier))
  ),


  tf_item_declaration: $ => choice(
    $.block_item_declaration,
    $.tf_port_declaration
  ),

  tf_port_list: $ => sepBy1(',', $.tf_port_item1),

  // INFO: drom's writing
  // tf_port_item1: $ => seq(
  //   repeat($.attribute_instance),
  //   optional($.tf_port_direction),
  //   optional('var'),
  //   choice(
  //     seq(
  //       $.data_type_or_implicit1,
  //       optseq(
  //         $.port_identifier,
  //         repeat($._variable_dimension),
  //         optseq('=', $.expression)
  //       )
  //     ),
  //     seq(
  //       $.port_identifier,
  //       repeat($._variable_dimension),
  //       optseq('=', $.expression)
  //     )
  //   )
  // ),
  // INFO: My rewriting/refactoring
  tf_port_item1: $ => prec('tf_port_item1', seq(
    repeat($.attribute_instance),
    optional($.tf_port_direction),
    optional('var'),
    choice(
      seq($.data_type_or_implicit1, optional($.port_identifier)),
      $.port_identifier,
    ),
    repeat($._variable_dimension),
    optional(seq('=', $.expression))
  )),

  tf_port_direction: $ => prec('tf_port_direction', choice(
    $.port_direction,
    seq(optional('const'), 'ref', optional('static'))
  )),

  tf_port_declaration: $ => seq(
    repeat($.attribute_instance),
    $.tf_port_direction,
    optional('var'),
    optional($.data_type_or_implicit1),
    $.list_of_tf_variable_identifiers,
    ';'
  ),

  task_prototype: $ => seq(
    'task',
    optional($.dynamic_override_specifiers),
    $.task_identifier,
    optional(seq('(', optional($.tf_port_list), ')'))
  ),

  // INFO: These were not present on drom's 2017 grammar
  // dynamic_override_specifiers ::= [ initial_or_extends_specifier ] [ final_specifier ]
  dynamic_override_specifiers: $ => choice( // Reorder to avoid matching the empty string
    seq($.initial_or_extends_specifier, optional($.final_specifier)),
    $.final_specifier
  ),

  // initial_or_extends_specifier ::=
  //   : initial
  //   | : extends
  initial_or_extends_specifier: $ => seq(':', choice('initial', 'extends')),

  // final_specifier ::= : final
  final_specifier: $ => seq(':', 'final'),


// ** A.2.8 Block item declarations
  block_item_declaration: $ => seq(
    repeat($.attribute_instance),
    choice(
      $.data_declaration,
      seq($.any_parameter_declaration, ';'),
      // $.overload_declaration,   // INFO: Removed from 1800-2023
      $.let_declaration
    )
  ),

  // overload_declaration: $ => seq(
  //   'bind',
  //   $.overload_operator,
  //   'function',
  //   $.data_type,
  //   $.function_identifier,
  //   '(',
  //   $.overload_proto_formals,
  //   ')',
  //   ';'
  // ),

  // overload_operator: $ => choice('+', '++', '–', '––', '*', '**', '/', '%', '==', '!=', '<', '<=', '>', '>=', '='),

  // overload_proto_formals: $ => sep1(',', $.data_type),

// ** A.2.9 Interface declarations
  modport_declaration: $ => seq('modport', sepBy1(',', $.modport_item), ';'),

  modport_item: $ => seq(
    $.modport_identifier,
    '(', sepBy1(',', $.modport_ports_declaration), ')'
  ),

  modport_ports_declaration: $ => seq(
    repeat($.attribute_instance),
    choice(
      $.modport_simple_ports_declaration,
      $.modport_tf_ports_declaration,
      $.modport_clocking_declaration
    )
  ),

  modport_clocking_declaration: $ => seq('clocking', $.clocking_identifier),

  modport_simple_ports_declaration: $ => seq(
    $.port_direction,
    sepBy1(',', $.modport_simple_port)
  ),

  modport_simple_port: $ => choice(
    $.port_identifier,
    seq('.', $.port_identifier, '(', optional($.expression), ')')
  ),

  modport_tf_ports_declaration: $ => seq(
    $.import_export, sepBy1(',', $._modport_tf_port)
  ),

  _modport_tf_port: $ => choice(
    $._method_prototype,
    $.tf_identifier
  ),

  import_export: $ => choice('import', 'export'),

// ** A.2.10 Assertion declarations
  concurrent_assertion_item: $ => prec('concurrent_assertion_item', choice(
    seq(optional(seq($._block_identifier, ':')), $._concurrent_assertion_statement),
    // $.checker_instantiation
  )),

  _concurrent_assertion_statement: $ => choice(
    $.assert_property_statement,
    $.assume_property_statement,
    $.cover_property_statement,
    $.cover_sequence_statement,
    $.restrict_property_statement
  ),

  assert_property_statement: $ => seq(
    'assert', 'property', '(', $.property_spec, ')', $.action_block
  ),

  assume_property_statement: $ => seq(
    'assume', 'property', '(', $.property_spec, ')', $.action_block
  ),

  cover_property_statement: $ => seq(
    'cover', 'property', '(', $.property_spec, ')', $.statement_or_null
  ),

  expect_property_statement: $ => seq(
    'expect', '(', $.property_spec, ')', $.action_block
  ),

  cover_sequence_statement: $ => seq(
    'cover', 'sequence', '(',
    optional($.clocking_event),
    // optional(prec.right(PREC.iff, seq(
    //   'disable', 'iff', '(', $.expression_or_dist, ')'
    // ))),
    optional(seq(
      'disable', 'iff', '(', $.expression_or_dist, ')'
    )),
    $.sequence_expr,
    ')',
    $.statement_or_null
  ),

  restrict_property_statement: $ => seq(
    'restrict', 'property', '(', $.property_spec, ')', ';'
  ),

  property_instance: $ => seq(
    $.ps_or_hierarchical_property_identifier,
    optional(seq('(', optional($.property_list_of_arguments), ')'))
  ),

  // property_list_of_arguments: $ => choice(
  //   seq(
  //     sep1(',', optional($._property_actual_arg)),
  //     repeat1(seq( // TODO remove 1
  //       ',', '.', $._identifier, '(', optional($._property_actual_arg), ')'
  //     ))
  //   ),
  //   sep1(',', seq(
  //     '.', $._identifier, '(', optional($._property_actual_arg), ')'
  //   ))
  // ),

  // INFO: Copied from list_of_arguments
  property_list_of_arguments: $ => prec.left(PREC.PARENT, choice(  // Reordered to avoid matching empty string
    // First case: mixing positional and named arguments
    seq(
      $.expression,
      repeat(seq(',', optional($._property_actual_arg))),
      repeat(seq(',', '.', $._identifier, '(', optional($._property_actual_arg), ')'))
    ),
    seq(
      optional($._property_actual_arg),
      repeat1(seq(',', optional($._property_actual_arg))),
      repeat(seq(',', '.', $._identifier, '(', optional($._property_actual_arg), ')'))
    ),
    seq(
      optional($._property_actual_arg),
      repeat(seq(',', optional($._property_actual_arg))),
      repeat1(seq(',', '.', $._identifier, '(', optional($._property_actual_arg), ')'))
    ),
    // Second case: using only named arguments
    sepBy1(',', seq('.', $._identifier, '(', optional($._property_actual_arg), ')'))
  )),

  _property_actual_arg: $ => choice(
    $.property_expr,
    $._sequence_actual_arg
  ),

  _assertion_item_declaration: $ => choice(
    $.property_declaration,
    $.sequence_declaration,
    $.let_declaration
  ),

  property_declaration: $ => seq(
    'property',
    $.property_identifier,
    optional(seq('(', optional($.property_port_list), ')')),
    ';',
    repeat($.assertion_variable_declaration),
    $.property_spec,
    optional(';'),
    'endproperty', optional(seq(':', $.property_identifier))
  ),

  property_port_list: $ => sepBy1(',', $.property_port_item),

  property_port_item: $ => seq(
    repeat($.attribute_instance),
    optional(seq(
      'local',
      optional($.property_lvar_port_direction)
    )),
    optional($.property_formal_type1),
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optional(seq('=', $._property_actual_arg))
  ),

  property_lvar_port_direction: $ => 'input',

  property_formal_type1: $ => choice(
    $.sequence_formal_type1,
    'property'
  ),

  property_spec: $ => seq(
    optional($.clocking_event),
    // optional(prec.right(PREC.iff, seq(
    //   'disable', 'iff', '(', $.expression_or_dist, ')'
    // ))),
    optional(seq(
      'disable', 'iff', '(', $.expression_or_dist, ')'
    )),
    $.property_expr
  ),

  // TODO: Review/fix
  property_expr: $ => choice(
    $.sequence_expr,
    seq('strong', '(', $.sequence_expr, ')'),
    seq('weak', '(', $.sequence_expr, ')'),
    prec.left(PREC.PARENT, seq('(', $.property_expr, ')')),

    // FIXME no assosiativity rules per spec
    prec.left(PREC.nexttime, seq('not', $.property_expr)),
    prec.left(PREC.or, seq($.property_expr, 'or', $.property_expr)),
    prec.left(PREC.and, seq($.property_expr, 'and', $.property_expr)),

    prec.right(PREC.INCIDENCE, seq($.sequence_expr, '|->', $.property_expr)),
    prec.right(PREC.INCIDENCE, seq($.sequence_expr, '|=>', $.property_expr)),

    // FIXME no assosiativity rules per spec
    prec.left(seq('if', '(', $.expression_or_dist, ')', $.property_expr, optional(seq('else', $.property_expr)))), // FIXME spec bug ( ) are not red seq('case', '(', $.expression_or_dist, ')', repeat1($.property_case_item), 'endcase'),  // FIXME spec bug ( ) are not red
    prec.left(seq('case', '(', $.expression_or_dist, ')', repeat1($.property_case_item), 'endcase')),
    prec.right(PREC.INCIDENCE, seq($.sequence_expr, '#-#', $.property_expr)),
    prec.right(PREC.INCIDENCE, seq($.sequence_expr, '#=#', $.property_expr)),

    // FIXME no assosiativity rules per spec
    prec.left(PREC.nexttime, seq('nexttime', $.property_expr)),
    prec.left(PREC.nexttime, seq('nexttime', '[', $.constant_expression, ']', $.property_expr)), // FIXME spec bug constant _expression with the space
    prec.left(PREC.nexttime, seq('s_nexttime', $.property_expr)),
    prec.left(PREC.nexttime, seq('s_nexttime', '[', $.constant_expression, ']', $.property_expr)),

    prec.left(PREC.always, seq('always', $.property_expr)),
    prec.left(PREC.always, seq('always', '[', $.cycle_delay_const_range_expression, ']', $.property_expr)),
    prec.left(PREC.always, seq('s_always', '[', $.constant_range, ']', $.property_expr)),
    prec.left(PREC.always, seq('s_eventually', $.property_expr)),
    prec.left(PREC.always, seq('eventually', '[', $.constant_range, ']', $.property_expr)),
    prec.left(PREC.always, seq('s_eventually', '[', $.cycle_delay_const_range_expression, ']', $.property_expr)),

    prec.right(PREC.until, seq(
      $.property_expr,
      choice('until', 's_until', 'until_with', 's_until_with', 'implies'),
      $.property_expr
    )),

    prec.right(PREC.iff, seq($.property_expr, 'iff', $.property_expr)),

    // FIXME no assosiativity rules per spec
    prec.left(PREC.always, seq(
      choice('accept_on', 'reject_on', 'sync_accept_on', 'sync_reject_on'),
      '(', $.expression_or_dist, ')', $.property_expr
    )),
    $.property_instance,
    prec.left(seq($.clocking_event, $.property_expr)) // FIXME no assosiativity rules per spec
  ),

  property_case_item: $ => choice(
    seq(
      sepBy1(',', $.expression_or_dist), ':', $.property_expr, ';'
    ),
    seq(
      'default', optional(':'), $.property_expr, ';'
    )
  ),

  sequence_declaration: $ => seq(
    'sequence',
    $._sequence_identifier,
    optional(seq('(', optional($.sequence_port_list), ')')), ';',
    repeat($.assertion_variable_declaration),
    $.sequence_expr, optional(';'),
    'endsequence', optional(seq(':', $._sequence_identifier))
  ),

  sequence_port_list: $ => sepBy1(',', $.sequence_port_item),

  sequence_port_item: $ => seq(
    repeat($.attribute_instance),
    optional(seq('local', optional($.sequence_lvar_port_direction))),
    optional($.sequence_formal_type1),
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optional(seq('=', $._sequence_actual_arg))
  ),

  sequence_lvar_port_direction: $ => choice('input', 'inout', 'output'),

  sequence_formal_type1: $ => choice(
    $.data_type_or_implicit1,
    'sequence',
    'untyped'
  ),

  // TODO: Come here when time dictates
  // sequence_expr: $ => choice(
  //   // prec.left(sep1(',', $.cycle_delay_range)), // FIXME precedence?
  //   // prec.left(PREC.SHARP2, seq($.sequence_expr, repeat1(seq($.cycle_delay_range, $.sequence_expr)))),
  //   // seq($.expression_or_dist, optional($._boolean_abbrev)),
  //   // seq($.sequence_instance, optional($.sequence_abbrev)),
  //   // prec.left(seq('(', $.sequence_expr, repseq(',', $._sequence_match_item), ')', optional($.sequence_abbrev))),
  //   // prec.left(PREC.and, seq($.sequence_expr, 'and', $.sequence_expr)),
  //   // prec.left(PREC.intersect, seq($.sequence_expr, 'intersect', $.sequence_expr)),
  //   // prec.left(PREC.or, seq($.sequence_expr, 'or', $.sequence_expr)),
  //   // seq('first_match', '(', $.sequence_expr, repseq(',', $._sequence_match_item), ')'),
  //   // prec.right(PREC.throughout, seq($.expression_or_dist, 'throughout', $.sequence_expr)),
  //   // prec.left(PREC.within, seq($.sequence_expr, 'within', $.sequence_expr)),
  //   // prec.left(seq($.clocking_event, $.sequence_expr)) // FIXME precedence?
  // ),

  // TODO: Come here when time dictates
  sequence_expr: $ => choice(
    repeat1(seq($.cycle_delay_range, $.sequence_expr)),
    seq($.sequence_expr, repeat1(seq($.cycle_delay_range, $.sequence_expr))),
    seq($.expression_or_dist, optional($._boolean_abbrev)),
    seq($.sequence_instance, optional($.sequence_abbrev)),
    seq('(', $.sequence_expr, repeat(seq(',', $._sequence_match_item)), ')', optional($.sequence_abbrev)),
    prec.left(PREC.and, seq($.sequence_expr, 'and', $.sequence_expr)),
    prec.left(PREC.intersect, seq($.sequence_expr, 'intersect', $.sequence_expr)),
    prec.left(PREC.or, seq($.sequence_expr, 'or', $.sequence_expr)),
    seq('first_match', '(', $.sequence_expr, repeat(seq(',', $._sequence_match_item)), ')'),
    prec.right(PREC.throughout, seq($.expression_or_dist, 'throughout', $.sequence_expr)),
    prec.left(PREC.within, seq($.sequence_expr, 'within', $.sequence_expr)),
    seq($.clocking_event, $.sequence_expr)
  ),

  cycle_delay_range: $ => choice(
    seq('##', $.constant_primary),
    seq('##', '[', $.cycle_delay_const_range_expression, ']'),
    '##[*]',
    '##[+]'
  ),

  // sequence_method_call: $ => seq($.sequence_instance, '.', $.method_identifier),

  _sequence_match_item: $ => choice(
    $.operator_assignment,
    $.inc_or_dec_expression,
    $.subroutine_call
  ),

  sequence_instance: $ => seq(
    $.ps_or_hierarchical_sequence_identifier,
    optional(seq('(', optional($.sequence_list_of_arguments), ')'))
  ),

  // sequence_list_of_arguments: $ => choice(
  //   // seq(
  //   //   sep1(',', optional($._sequence_actual_arg)),
  //   //   repseq(',', '.', $._identifier, '(', optional($._sequence_actual_arg), ')')
  //   // ),
  //   sep1(',', seq('.', $._identifier, '(', optional($._sequence_actual_arg), ')'))
  // ),

  // INFO: Copied from list_of_arguments
  sequence_list_of_arguments: $ => prec.left(PREC.PARENT, choice(  // Reordered to avoid matching empty string
    // First case: mixing positional and named arguments
    seq(
      $._sequence_actual_arg,
      repeat(seq(',', optional($._sequence_actual_arg))),
      repeat(seq(',', '.', $._identifier, '(', optional($._sequence_actual_arg), ')'))
    ),
    seq(
      optional($._sequence_actual_arg),
      repeat1(seq(',', optional($._sequence_actual_arg))),
      repeat(seq(',', '.', $._identifier, '(', optional($._sequence_actual_arg), ')'))
    ),
    seq(
      optional($._sequence_actual_arg),
      repeat(seq(',', optional($._sequence_actual_arg))),
      repeat1(seq(',', '.', $._identifier, '(', optional($._sequence_actual_arg), ')'))
    ),
    // Second case: using only named arguments
    sepBy1(',', seq('.', $._identifier, '(', optional($._sequence_actual_arg), ')'))
  )),


  _sequence_actual_arg: $ => prec('_sequence_actual_arg', choice(
    $.event_expression,
    $.sequence_expr,
    '$',
  )),

  _boolean_abbrev: $ => choice(
    $.consecutive_repetition,
    $.non_consecutive_repetition,
    $.goto_repetition
  ),

  sequence_abbrev: $ => $.consecutive_repetition,

  consecutive_repetition: $ => choice(
    seq('[*', $._const_or_range_expression, ']'),
    '[*]',
    '[+]'
  ),

  non_consecutive_repetition: $ => seq('[=', $._const_or_range_expression, ']'),

  goto_repetition: $ => seq('[->', $._const_or_range_expression, ']'),

  _const_or_range_expression: $ => choice(
    $.constant_expression,
    $.cycle_delay_const_range_expression
  ),

  cycle_delay_const_range_expression: $ => prec('cycle_delay_const_range_expression', choice(
    seq($.constant_expression, ':', $.constant_expression),
    seq($.constant_expression, ':', '$')
  )),

  expression_or_dist: $ => prec('expression_or_dist', seq(
    $.expression,
    optional(prec.left(PREC.RELATIONAL, seq('dist', '{', $.dist_list, '}')))
  )),

  assertion_variable_declaration: $ => seq(
    $._var_data_type,
    $.list_of_variable_decl_assignments,
    ';'
  ),

// ** A.2.11 Covergroup declarations
  covergroup_declaration: $ => seq(
    'covergroup',
    choice(
      seq(
        $.covergroup_identifier,
        optional(seq('(', optional($.tf_port_list), ')')),
        optional($.coverage_event),
      ),
      seq('extends', $.covergroup_identifier)
    ),
    ';',
    repeat($.coverage_spec_or_option),
    'endgroup', optional(seq(':', $.covergroup_identifier))
  ),

  coverage_spec_or_option: $ => choice(
    seq(repeat($.attribute_instance), $._coverage_spec),
    seq(repeat($.attribute_instance), $.coverage_option, ';')
  ),

  coverage_option: $ => choice(
    seq('option', '.', $.member_identifier, '=', $.expression),
    seq('type_option', '.', $.member_identifier, '=', $.constant_expression)
  ),

  _coverage_spec: $ => choice($.cover_point, $.cover_cross),

  coverage_event: $ => choice(
    $.clocking_event,
    seq('with', 'function', 'sample', '(', optional($.tf_port_list), ')'),
    seq('@@', '(', $.block_event_expression, ')')
  ),

  block_event_expression: $ => choice(
    prec.left(PREC.or, seq($.block_event_expression, 'or', $.block_event_expression)),
    seq('begin', $.hierarchical_btf_identifier),
    seq('end', $.hierarchical_btf_identifier)
  ),

  hierarchical_btf_identifier: $ => choice(
    $._hierarchical_tf_identifier,
    $._hierarchical_block_identifier,
    // prec.left(PREC.PARENT, seq(
    //   choice(seq($.hierarchical_identifier, '.'), $.class_scope),
    //   $.method_identifier
    // ))
    seq(
      optional(choice(seq($.hierarchical_identifier, '.'), $.class_scope)),
      $.method_identifier
    )
  ),

  cover_point: $ => seq(
    optional(seq(optional($.data_type_or_implicit1), $.cover_point_identifier, ':')),
    'coverpoint', $.expression,
    // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')'))),
    optional(seq('iff', '(', $.expression, ')')),
    $.bins_or_empty
  ),

  bins_or_empty: $ => choice(
    seq('{', repeat($.attribute_instance), repeat(seq($.bins_or_options, ';')), '}'),
    ';'
  ),

  // TODO: Refactor: Last sentence is common, and first one is common in first 4 choices
  bins_or_options: $ => choice(
    $.coverage_option,
    seq(
      optional('wildcard'),
      $.bins_keyword,
      $._bin_identifier,
      optional(seq('[', optional($._covergroup_expression), ']')),
      '=',
      '{', $.covergroup_range_list, '}',
      optional(seq('with', '(', $._with_covergroup_expression, ')')),
      // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
      optional(seq('iff', '(', $.expression, ')'))
    ),
    seq(
      optional('wildcard'),
      $.bins_keyword,
      $._bin_identifier,
      optional(seq('[', optional($._covergroup_expression), ']')),
      '=',
      $.cover_point_identifier,
      'with', '(', $._with_covergroup_expression, ')',
      // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
      optional(seq('iff', '(', $.expression, ')'))
    ),
    seq(
      optional('wildcard'),
      $.bins_keyword,
      $._bin_identifier,
      optional(seq('[', optional($._covergroup_expression), ']')),
      '=',
      $._set_covergroup_expression,
      // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
      optional(seq('iff', '(', $.expression, ')'))
    ),
    seq(
      optional('wildcard'),
      $.bins_keyword,
      $._bin_identifier,
      optional(seq('[', ']')),
      '=',
      $.trans_list,
      // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
      optional(seq('iff', '(', $.expression, ')'))
    ),
    seq(
      $.bins_keyword,
      $._bin_identifier,
      optional(seq('[', optional($._covergroup_expression), ']')),
      '=',
      'default',
      // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
      optional(seq('iff', '(', $.expression, ')'))
    ),
    seq(
      $.bins_keyword,
      $._bin_identifier,
      '=',
      'default',
      'sequence',
      // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
      optional(seq('iff', '(', $.expression, ')'))
    )
  ),

  bins_keyword: $ => choice('bins', 'illegal_bins', 'ignore_bins'),

  trans_list: $ => sepBy1(',', seq('(', $.trans_set, ')')),

  trans_set: $ => sepBy1('=>', $.trans_range_list),

  trans_range_list: $ => choice(
    $.trans_item,
    seq($.trans_item, '[*', $.repeat_range, ']'),
    seq($.trans_item, '[->', $.repeat_range, ']'),
    seq($.trans_item, '[=', $.repeat_range, ']')
  ),

  trans_item: $ => $.covergroup_range_list,

  repeat_range: $ => seq(
    $._covergroup_expression, optional(seq(':', $._covergroup_expression))
  ),

  cover_cross: $ => seq(
    optional(seq($.cross_identifier, ':')),
    'cross',
    $.list_of_cross_items,
    // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')'))),
    optional(seq('iff', '(', $.expression, ')')),
    $.cross_body
  ),

  list_of_cross_items: $ => seq($._cross_item, ',', sepBy1(',', $._cross_item)),

  _cross_item: $ => choice(
    $.cover_point_identifier,
    $._variable_identifier
  ),

  cross_body: $ => choice(
    seq('{', repeat($.cross_body_item), '}'),
    ';'
  ),

  cross_body_item: $ => choice(
    $.function_declaration,
    seq($.bins_selection_or_option, ';')
  ),

  bins_selection_or_option: $ => choice(
    seq(repeat($.attribute_instance), $.coverage_option),
    seq(repeat($.attribute_instance), $.bins_selection)
  ),

  bins_selection: $ => seq(
    $.bins_keyword, $._bin_identifier, '=', $.select_expression,
    // optional(prec.right(PREC.iff, seq('iff', '(', $.expression, ')')))
    optional(seq('iff', '(', $.expression, ')'))
  ),

  select_expression: $ => choice(
    $.select_condition,
    prec.left(PREC.UNARY, seq('!', $.select_condition)),
    prec.left(PREC.LOGICAL_AND, seq($.select_expression, '&&', $.select_expression)),
    prec.left(PREC.LOGICAL_OR, seq($.select_expression, '||', $.select_expression)),
    prec.left(PREC.PARENT, seq('(', $.select_expression, ')')),
    seq(
      $.select_expression, 'with', '(', $._with_covergroup_expression, ')',
      optional(seq('matches', $._integer_covergroup_expression))
    ),
    $.cross_identifier,
    seq(
      $._cross_set_expression,
      optional(seq('matches', $._integer_covergroup_expression))
    )
  ),

  select_condition: $ => seq(
    'binsof', '(', $.bins_expression, ')',
    optional(seq('intersect', '{', $.covergroup_range_list, '}'))
  ),

  bins_expression: $ => choice(
    $._variable_identifier,
    // prec.left(PREC.PARENT, seq($.cover_point_identifier, optseq('.', $._bin_identifier)))
    seq($.cover_point_identifier, optional(seq('.', $._bin_identifier)))
  ),

  covergroup_range_list: $ => sepBy1(',', $.covergroup_value_range),

  covergroup_value_range: $ => choice(
    $._covergroup_expression,
    seq('[', $._covergroup_expression, ':', $._covergroup_expression, ']'),
    seq('[', '$', ':', $._covergroup_expression, ']'),
    seq('[', $._covergroup_expression, ':', '$', ']'),
    seq('[', $._covergroup_expression, '+/-', $._covergroup_expression, ']'),
    seq('[', $._covergroup_expression, '+%-', $._covergroup_expression, ']'),
  ),

  _with_covergroup_expression: $ => $._covergroup_expression,

  _set_covergroup_expression: $ => $._covergroup_expression,

  _integer_covergroup_expression: $ => choice($._covergroup_expression, '$'),

  _cross_set_expression: $ => $._covergroup_expression,

  _covergroup_expression: $ => $.expression,

// ** A.2.12 Let declarations
  let_declaration: $ => seq(
    'let', $.let_identifier,
    optional(seq('(', optional($.let_port_list), ')')),
    '=', $.expression, ';'
  ),

  let_identifier: $ => $._identifier,

  let_port_list: $ => sepBy1(',', $.let_port_item),

  let_port_item: $ => seq(
    repeat($.attribute_instance),
    optional($.let_formal_type1),
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optional(seq('=', $.expression))
  ),

  let_formal_type1: $ => choice(
    $.data_type_or_implicit1,
    'untyped'
  ),

  let_expression: $ => prec.left(seq(
    optional($.package_scope),
    $.let_identifier,
    optional(seq('(', optional($.let_list_of_arguments), ')'))
  )),

  // INFO: Copied from $.list_of_arguments
  let_list_of_arguments: $ => prec.left(PREC.PARENT, choice(  // Reordered to avoid matching empty string
    // First case: mixing positional and named arguments
    seq(
      $.let_actual_arg,
      repeat(seq(',', optional($.let_actual_arg))),
      repeat(seq(',', '.', $._identifier, '(', optional($.let_actual_arg), ')'))
    ),
    seq(
      optional($.let_actual_arg),
      repeat1(seq(',', optional($.let_actual_arg))),
      repeat(seq(',', '.', $._identifier, '(', optional($.let_actual_arg), ')'))
    ),
    seq(
      optional($.let_actual_arg),
      repeat(seq(',', optional($.let_actual_arg))),
      repeat1(seq(',', '.', $._identifier, '(', optional($.let_actual_arg), ')'))
    ),
    // Second case: using only named arguments
    sepBy1(',', seq('.', $._identifier, '(', optional($.let_actual_arg), ')'))
  )),


  let_actual_arg: $ => $.expression,

  // let_list_of_arguments: $ => alias($.list_of_arguments, $.let_list_of_arguments),

  // let_actual_arg: $ => alias($.expression, $.let_actual_arg),


// * A.3 Primitive instances
// ** A.3.1 Primitive instantiation and instances

  // gate_instantiation: $ => seq(
  //   choice(
  //     seq(
  //       $.cmos_switchtype,
  //       // optional($.delay3),
  //       sep1(',', $.cmos_switch_instance)
  //     ),
  //     seq(
  //       $.enable_gatetype,
  //       // optional($.drive_strength), optional($.delay3),
  //       sep1(',', $.enable_gate_instance)
  //     ),
  //     seq(
  //       $.mos_switchtype,
  //       // optional($.delay3),
  //       sep1(',', $.mos_switch_instance)
  //     ),
  //     seq(
  //       $.n_input_gatetype,
  //       optional($.drive_strength), optional($.delay2),
  //       sep1(',', $.n_input_gate_instance)
  //     ),
  //     seq(
  //       $.n_output_gatetype,
  //       optional($.drive_strength), optional($.delay2),
  //       sep1(',', $.n_output_gate_instance)
  //     ),
  //     seq(
  //       $.pass_en_switchtype,
  //       optional($.delay2),
  //       sep1(',', $.pass_enable_switch_instance)
  //     ),
  //     seq(
  //       $.pass_switchtype,
  //       sep1(',', $.pass_switch_instance)
  //     ),
  //     seq(
  //       'pulldown',
  //       optional($.pulldown_strength),
  //       sep1(',', $.pull_gate_instance)
  //     ),
  //     seq(
  //       'pullup',
  //       optional($.pullup_strength),
  //       sep1(',', $.pull_gate_instance)
  //     )
  //   ),
  //   ';'
  // ),

  // cmos_switch_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(',
  //   $.output_terminal, ',',
  //   $.input_terminal, ',',
  //   $.ncontrol_terminal, ',',
  //   $.pcontrol_terminal,
  //   ')'
  // ),

  // enable_gate_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.output_terminal, ',', $.input_terminal, ',', $.enable_terminal, ')'
  // ),

  // mos_switch_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.output_terminal, ',', $.input_terminal, ',', $.enable_terminal, ')'
  // ),

  // n_input_gate_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.output_terminal, ',', sep1(',', $.input_terminal), ')'
  // ),

  // n_output_gate_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', sep1(',', $.output_terminal), ',', $.input_terminal, ')'
  // ),

  // pass_switch_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.inout_terminal, ',', $.inout_terminal, ')'
  // ),

  // pass_enable_switch_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.inout_terminal, ',', $.inout_terminal, ',', $.enable_terminal, ')'
  // ),

  // pull_gate_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.output_terminal, ')'
  // ),

// ** A.3.2 Primitive strengths

  // pulldown_strength: $ => choice(
  //   seq('(', $.strength0, ',', $.strength1, ')'),
  //   seq('(', $.strength1, ',', $.strength0, ')'),
  //   seq('(', $.strength0, ')')
  // ),

  // pullup_strength: $ =>choice(
  //   seq(',', $.strength0, ',', $.strength1, ')'),
  //   seq(',', $.strength1, ',', $.strength0, ')'),
  //   seq(',', $.strength1, ')')
  // ),

// ** A.3.3 Primitive terminals

  // enable_terminal: $ => $.expression,
  // inout_terminal: $ => $.net_lvalue,
  // input_terminal: $ => $.expression,
  // ncontrol_terminal: $ => $.expression,
  // output_terminal: $ => $.net_lvalue,
  // pcontrol_terminal: $ => $.expression,

// ** A.3.4 Primitive gate and switch types

  // cmos_switchtype: $ => choice('cmos', 'rcmos'),
  // enable_gatetype: $ => choice('bufif0', 'bufif1', 'notif0', 'notif1'),
  // mos_switchtype: $ => choice('nmos', 'pmos', 'rnmos', 'rpmos'),
  // n_input_gatetype: $ => choice('and', 'nand', 'or', 'nor', 'xor', 'xnor'),
  // n_output_gatetype: $ => choice('buf', 'not'),
  // pass_en_switchtype: $ => choice('tranif0', 'tranif1', 'rtranif1', 'rtranif0'),
  // pass_switchtype: $ => choice('tran', 'rtran'),

// * A.4 Instantiations
// ** A.4.1 Instantiation
// *** A.4.1.1 Module instantiation
  module_instantiation: $ => prec('module_instantiation', seq(
    field('instance_type', $.module_identifier),
    optional($.parameter_value_assignment),
    sepBy1(',', $.hierarchical_instance),
    ';'
  )),

  parameter_value_assignment: $ => seq(
    '#', '(', optional($.list_of_parameter_value_assignments), ')'
  ),

  list_of_parameter_value_assignments: $ => choice(
    // INFO: ordered_parameter_assignment equivalent to: sepBy1(',', $.ordered_parameter_assignment)
    // But the line below also supports empty positional arguments
    seq(choice(',', $.ordered_parameter_assignment), repeat(choice(',', (seq(',', $.ordered_parameter_assignment))))),
    sepBy1(',', $.named_parameter_assignment),
  ),

  ordered_parameter_assignment: $ => $.param_expression,

  named_parameter_assignment: $ => seq(
    // INFO: optional directives out of LRM, supports e.g. ifdefs in parameter lists
    optional($._directives), '.', $.parameter_identifier, '(', optional($.param_expression), ')'
  ),

  hierarchical_instance: $ => prec('hierarchical_instance', seq(
    $.name_of_instance, '(', optional($.list_of_port_connections), ')'
  )),

  name_of_instance: $ => seq(
    field('instance_name', $.instance_identifier),
    repeat($.unpacked_dimension)
  ),

  // Reordered
  list_of_port_connections: $ => choice(
    // INFO: ordered_port equivalent to: sepBy1(',', $.ordered_port_connection)
    // But the line below also supports empty positional arguments
    seq(choice(',', $.ordered_port_connection), repeat(choice(',', (seq(',', $.ordered_port_connection))))),
    sepBy1(',', $.named_port_connection)
  ),

  ordered_port_connection: $ => seq(
    repeat($.attribute_instance),
    $.expression // INFO: Removed the optional so that it doesn't match the empty string
  ),

  // from spec:
  // named_port_connection: $ =>
  //   { attribute_instance } . port_identifier [ ( [ expression ] ) ]
  // | { attribute_instance } .*
  named_port_connection: $ => seq(
    repeat($.attribute_instance),
    choice(
      // INFO: optional directives out of LRM, supports e.g. ifdefs in parameter lists
      seq(optional($._directives), '.', field('port_name', $.port_identifier), optional(seq('(', optional(field('connection', $.expression)), ')'))),
      '.*'
    )
  ),

// *** A.4.1.2 Interface instantiation
  interface_instantiation: $ => prec('interface_instantiation', seq(
    $.interface_identifier,
    optional($.parameter_value_assignment),
    sepBy1(',', $.hierarchical_instance),
    ';'
  )),

// *** A.4.1.3 Program instantiation
  program_instantiation: $ => prec('program_instantiation', seq(
    $.program_identifier,
    optional($.parameter_value_assignment),
    sepBy1(',', $.hierarchical_instance),
    ';'
  )),

// *** A.4.1.4 Checker instantiation
  checker_instantiation: $ => prec('checker_instantiation', seq(
    $.ps_checker_identifier,
    $.name_of_instance,
    '(',
    optional($.list_of_checker_port_connections),
    ')',
    ';'
  )),

  list_of_checker_port_connections: $ => choice(
    sepBy1(',', $.ordered_checker_port_connection),
    sepBy1(',', $.named_checker_port_connection)
  ),

  ordered_checker_port_connection: $ => seq(
    repeat($.attribute_instance),
    $._property_actual_arg
  ),

  named_checker_port_connection: $ => choice( // TODO: Could be rewritten the same as named_port_connection, or even aliased
    seq(
      repeat($.attribute_instance), '.', $.formal_port_identifier,
      optseq('(', optional($._property_actual_arg), ')')
    ),
    seq(
      repeat($.attribute_instance), '.*'
    )
  ),

  //   choice(
  //     sep1(',', optseq(
  //       repeat($.attribute_instance),
  //       optional($._property_actual_arg)
  //     )),
  //     // sep1(',', $.named_checker_port_connection)
  //     sep1(',', choice(
  //       seq(
  //         repeat($.attribute_instance), '.', $.formal_port_identifier,
  //         optseq('(', optional($._property_actual_arg), ')')
  //       ),
  //       seq(
  //         repeat($.attribute_instance), '.*'
  //       )
  //     ))
  //   ),
  //   ')',
  //   ';'
  // ),



// ** A.4.2 Generated instantiation
  generate_region: $ => seq(
    'generate', repeat($._generate_item), 'endgenerate'
  ),

  loop_generate_construct: $ => seq(
    'for', '(',
    $.genvar_initialization, ';', $._genvar_expression, ';', $.genvar_iteration,
    ')',
    $.generate_block
  ),

  genvar_initialization: $ => seq(
    optional('genvar'),
    $.genvar_identifier,
    '=',
    $.constant_expression
  ),

  genvar_iteration: $ => choice(
    seq($.genvar_identifier, $.assignment_operator, $._genvar_expression),
    seq($.inc_or_dec_operator, $.genvar_identifier),
    seq($.genvar_identifier, $.inc_or_dec_operator)
  ),

  conditional_generate_construct: $ => choice(
    $.if_generate_construct,
    $.case_generate_construct
  ),

  // prec.right because:
  //
  // 'if'  '('  constant_expression  ')'  'if'  '('  constant_expression  ')'  generate_block  •  'else'  …
  // 1:  'if'  '('  constant_expression  ')'  (if_generate_construct  'if'  '('  constant_expression  ')'  generate_block  •  'else'  generate_block)
  // 2:  'if'  '('  constant_expression  ')'  (if_generate_construct  'if'  '('  constant_expression  ')'  generate_block)  •  'else'  …
  if_generate_construct: $ => prec.right(seq(
    'if', '(', $.constant_expression, ')', $.generate_block,
    optional(seq('else', $.generate_block))
  )),

  case_generate_construct: $ => seq(
    'case', '(', $.constant_expression, ')', $.case_generate_item,
    repeat($.case_generate_item),
    'endcase'
  ),

  case_generate_item: $ => choice(
    seq(sepBy1(',', $.constant_expression), ':', $.generate_block),
    seq('default', optional(':'), $.generate_block)
  ),

  generate_block: $ => choice(
    $._generate_item,
    seq(
      optional(seq($.generate_block_identifier, ':')),
      'begin',
      optional(seq(':', $.generate_block_identifier)),
      repeat($._generate_item),
      'end',
      optional(seq(':', $.generate_block_identifier))
    )
  ),

  _generate_item: $ => choice(
    $.module_or_generate_item,
    $.interface_or_generate_item,
    // $._checker_or_generate_item
  ),

// * A.5 UDP declaration and instantiation
// ** A.5.1 UDP declaration
  // udp_nonansi_declaration: $ => seq(
  //   repeat($.attribute_instance), 'primitive', $._udp_identifier, '(', $.udp_port_list, ')', ';'
  // ),

  // udp_ansi_declaration: $ => seq(
  //   repeat($.attribute_instance), 'primitive', $._udp_identifier, '(', $.udp_declaration_port_list, ')', ';'
  // ),

  // udp_declaration: $ => choice(
  //   seq(
  //     $.udp_nonansi_declaration, $.udp_port_declaration, repeat($.udp_port_declaration),
  //     $._udp_body,
  //     'endprimitive', optseq(':', $._udp_identifier)
  //   ),
  //   seq($.udp_ansi_declaration, $._udp_body, 'endprimitive', optseq(':', $._udp_identifier)),
  //   seq('extern', $.udp_nonansi_declaration),
  //   seq('extern', $.udp_ansi_declaration),
  //   seq(
  //     repeat($.attribute_instance), 'primitive', $._udp_identifier, '(', '.*', ')', ';',
  //     repeat($.udp_port_declaration),
  //     $._udp_body,
  //     'endprimitive', optseq(':', $._udp_identifier)
  //   )
  // ),

// ** A.5.2 UDP ports

  // udp_port_list: $ => seq(
  //   $.output_port_identifier, ',', sep1(',', $.input_port_identifier)
  // ),

  // udp_declaration_port_list: $ => seq(
  //   $.udp_output_declaration, ',', sep1(',', $.udp_input_declaration)
  // ),

  // udp_port_declaration: $ => seq(
  //   choice(
  //     $.udp_output_declaration,
  //     $.udp_input_declaration,
  //     $.udp_reg_declaration
  //   ),
  //   ';'
  // ),

  // udp_output_declaration: $ => seq(
  //   repeat($.attribute_instance),
  //   'output',
  //   choice(
  //     $.port_identifier,
  //     seq('reg', $.port_identifier, optseq('=', $.constant_expression))
  //   )
  // ),

  // udp_input_declaration: $ => seq(
  //   repeat($.attribute_instance), 'input', $.list_of_udp_port_identifiers
  // ),

  // udp_reg_declaration: $ => seq(
  //   repeat($.attribute_instance), 'reg', $._variable_identifier
  // ),

// ** A.5.3 UDP body
  // _udp_body: $ => choice($.combinational_body, $.sequential_body),

  // combinational_body: $ => seq(
  //   'table', repeat1($.combinational_entry), 'endtable'
  // ),

  // combinational_entry: $ => seq($.level_input_list, ':', $.output_symbol, ';'),

  // sequential_body: $ => seq(
  //   optional($.udp_initial_statement),
  //   'table', repeat1($.sequential_entry), 'endtable'
  // ),

  // udp_initial_statement: $ => seq(
  //   'initial', $.output_port_identifier, '=', $.init_val, ';'
  // ),

  // init_val: $ => choice(
  //   "1'b0", "1'b1", "1'bx", "1'bX", "1'B0", "1'B1", "1'Bx", "1'BX", "1", "0"
  // ),

  // sequential_entry: $ => seq(
  //   $._seq_input_list, ':', $._current_state, ':', $.next_state, ';'
  // ),

  // _seq_input_list: $ => choice($.level_input_list, $.edge_input_list),

  // level_input_list: $ => repeat1($.level_symbol),

  // edge_input_list: $ => seq(repeat($.level_symbol), $.edge_indicator, repeat($.level_symbol)),

  // edge_indicator: $ => choice(
  //   seq('(', $.level_symbol, $.level_symbol, ')'),
  //   $.edge_symbol
  // ),

  // _current_state: $ => $.level_symbol,

  // next_state: $ => choice($.output_symbol, '-'),

  // output_symbol: $ => /[01xX]/,

  // level_symbol: $ => /[01xX?bB]/,

  // edge_symbol: $ => /[rRfFpPnN*]/,

// ** A.5.4 UDP instantiation
  // udp_instantiation: $ => seq(
  //   $._udp_identifier,
  //   optional($.drive_strength),
  //   optional($.delay2),
  //   sep1(',', $.udp_instance),
  //   ';'
  // ),

  // udp_instance: $ => seq(
  //   optional($.name_of_instance),
  //   '(', $.output_terminal, ',', sep1(',', $.input_terminal), ')'
  // ),

// * A.6 Behavioral statements
// ** A.6.1 Continuous assignment and net alias statements
  continuous_assign: $ => seq(
    'assign',
    choice(
      seq(
        optional($.drive_strength),
        // optional($.delay3), // TODO: Add in the future
        $.list_of_net_assignments
      ),
      seq(
        optional($.delay_control),
        $.list_of_variable_assignments
      )
    ),
    ';'
  ),

  list_of_net_assignments: $ => sepBy1(',', $.net_assignment),

  list_of_variable_assignments: $ => sepBy1(',', $.variable_assignment),

  net_alias: $ => seq(
    'alias', $.net_lvalue, '=', sepBy1('=', $.net_lvalue), ';'
  ),

  // INFO: Drom's one
  // net_assignment: $ => prec.left(PREC.ASSIGN,
  //   seq($.net_lvalue, '=', $.expression)
  // ),
  // INFO: Mine without prec.left
  net_assignment: $ => seq($.net_lvalue, '=', $.expression),

// ** A.6.2 Procedural blocks and assignments
  initial_construct: $ => seq('initial', $.statement_or_null),

  always_construct: $ => seq($.always_keyword, $.statement),

  always_keyword: $ => choice(
    'always', 'always_comb', 'always_latch', 'always_ff'
  ),

  final_construct: $ => seq('final', $.function_statement),

  // TODO: Review, removed the prec.left(PREC.ASSIGN from choices
  blocking_assignment: $ => choice(
    seq($.variable_lvalue, '=', $.delay_or_event_control, $.expression),

    prec(PREC.ASSIGN, seq(
      $.nonrange_variable_lvalue, '=', $.dynamic_array_new
    )),

    // TODO: Is this the one for class_new?
    // // seq(
    // //   optional(choice(
    // //     seq($.implicit_class_handle, '.'),
    // //     $.class_scope,
    // //     $.package_scope
    // //   )),
    // //   $._hierarchical_variable_identifier
    // //   $.select,
    // //   '=',
    // //   $.class_new
    // // ),

    $.operator_assignment,
    $.inc_or_dec_expression, // INFO: New in 2023? Not in drom's
    seq($.class_variable_identifier, optional(seq('=', $.class_new))), // DANGER: Out of LRM explicitly, but should be (8.8) typed constructor
    $.shallow_copy, // DANGER: Not in LRM explicitly! 8.12
  ),

  // shallow_copy: $ => seq($.variable_lvalue, '=', 'new', $._identifier),
  shallow_copy: $ => seq($._identifier, '=', 'new', $._identifier),

  // INFO: Drom's one
  // operator_assignment: $ => prec.left(PREC.ASSIGN,
  //   seq($.variable_lvalue, $.assignment_operator, $.expression)
  // ),
  // INFO: Mine without prec.left
  operator_assignment: $ => seq($.variable_lvalue, $.assignment_operator, $.expression),

  assignment_operator: $ => choice(
    '=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=', '<<<=', '>>>='
  ),

  // nonblocking_assignment: $ => prec.left(PREC.ASSIGN, seq(
  //   $.variable_lvalue,
  //   '<=',
  //   optional($.delay_or_event_control),
  //   $.expression
  // )),
  nonblocking_assignment: $ => seq(
    $.variable_lvalue,
    '<=',
    optional($.delay_or_event_control),
    $.expression
  ),

  procedural_continuous_assignment: $ => choice(
    seq('assign', $.variable_assignment),
    seq('deassign', $.variable_lvalue),
    seq('force', $.variable_assignment),
    seq('force', $.net_assignment),
    seq('release', $.variable_lvalue),
    seq('release', $.net_lvalue)
  ),

  // INFO: drom's one
  // variable_assignment: $ => prec.left(PREC.ASSIGN, seq(
  //   $.variable_lvalue,
  //   '=',
  //   $.expression
  // )),
  // INFO: Mine
  variable_assignment: $ => seq($.variable_lvalue, '=', $.expression),

// ** A.6.3 Parallel and sequential blocks
  action_block: $ => prec('action_block', choice(
    $.statement_or_null,
    seq(optional($.statement), 'else', $.statement_or_null)
  )),

  seq_block: $ => seq(
    'begin', optional(seq(':', $._block_identifier)),
    repeat($.block_item_declaration),
    repeat($.statement_or_null),
    'end', optional(seq(':', $._block_identifier))
  ),

  par_block: $ => seq(
    'fork', optional(seq(':', $._block_identifier)),
    repeat($.block_item_declaration),
    repeat($.statement_or_null),
    $.join_keyword, optional(seq(':', $._block_identifier))
  ),

  join_keyword: $ => choice('join', 'join_any', 'join_none'),

// ** A.6.4 Statements
  statement_or_null: $ => prec('statement_or_null', choice(
    $.statement,
    seq(repeat($.attribute_instance), ';')
  )),

  statement: $ => prec('statement', choice(
    seq(
      optional(seq(field('block_name', $._block_identifier), ':')),
      repeat($.attribute_instance),
      $.statement_item
    ))),

  statement_item: $ => prec('statement_item', choice(
    seq($.blocking_assignment, ';'),
    seq($.nonblocking_assignment, ';'),
    seq($.procedural_continuous_assignment, ';'),
    $.case_statement,
    $.conditional_statement,
    $.subroutine_call_statement,
    $.disable_statement,
    $.event_trigger,
    $.loop_statement,
    $.jump_statement,
    $.par_block,
    $.seq_block,
    $.procedural_timing_control_statement,
    $.seq_block,
    $.wait_statement,
    $._procedural_assertion_statement,
    seq($.clocking_drive, ';'),
    $.randsequence_statement,
    $.randcase_statement,
    $.expect_property_statement,

    // $.text_macro_usage, // INFO: Out of LRM
    $._directives, // INFO: This one is not in the LRM but adds good support for lots of stuff
  )),

  function_statement: $ => $.statement,

  function_statement_or_null: $ => choice(
    $.function_statement,
    seq(repeat($.attribute_instance), ';')
  ),

  variable_identifier_list: $ => sepBy1(',', $._variable_identifier),


// ** A.6.5 Timing control statements
  procedural_timing_control_statement: $ => seq(
    $._procedural_timing_control,
    $.statement_or_null
  ),

  delay_or_event_control: $ => choice(
    $.delay_control,
    $.event_control,
    seq('repeat', '(', $.expression, ')', $.event_control)
  ),

  delay_control: $ => seq('#', choice(
    $.delay_value,
    seq('(', $.mintypmax_expression, ')')
  )),

  // TODO: Seems very different from the one by drom, probably
  // because of 2023 standard
  event_control: $ => choice(
    $.clocking_event,
    seq('@', '*'),
    seq('@', '(', '*', ")")
  ),
  // event_control: $ => choice(
  //   seq('@', $._hierarchical_event_identifier),
  //   seq('@', '(', $.event_expression, ')'),
  //   '@*',
  //   seq('@', '(', '*', ')'),
  //   seq('@', $.ps_or_hierarchical_sequence_identifier)
  // ),

  // INFO: Changed quite a lot from what Drom did
  event_expression: $ => prec.left('event_expression', choice(
    seq(optional($.edge_identifier), $.expression, optional(seq('iff', $.expression))),
    // seq($.sequence_instance, optional(seq('iff', $.expression))),
    seq($.event_expression, 'or', $.event_expression),
    seq($.event_expression, ',', $.event_expression),
    seq('(', $.event_expression, ')')
  )),

  // // event_expression_2: $ => choice( // reordered : help parser
  // //   seq($.edge_identifier, $.expression), // reordered : help parser
  // //   seq(
  // //     optional($.edge_identifier),
  // //     $.expression,
  // //     optseq('iff', $.expression)
  // //   ),
  // //   // seq(
  // //   //   $.sequence_instance,
  // //   //   optseq('iff', $.expression)
  // //   // ),
  // //   seq('(', $.event_expression, ')')
  // // ),

  _procedural_timing_control: $ => choice(
    $.delay_control,
    $.event_control,
    $.cycle_delay
  ),

  jump_statement: $ => seq(
    choice(
      seq('return', optional($.expression)),
      'break',
      'continue',
    ),
    ';'
  ),

  wait_statement: $ => choice(
    seq('wait', '(', $.expression, ')', $.statement_or_null),
    seq('wait', 'fork', ';'),
    seq('wait_order', '(', sepBy1(',', $.hierarchical_identifier), ')', $.action_block)
  ),

  event_trigger: $ => choice(
    seq('->', $._hierarchical_event_identifier, optional($.nonrange_select1), ';'),
    seq('->>', optional($.delay_or_event_control), $._hierarchical_event_identifier, optional($.nonrange_select1), ';')
  ),

  disable_statement: $ => choice(
    seq('disable', $._hierarchical_task_identifier, ';'),
    seq('disable', $._hierarchical_block_identifier, ';'),
    seq('disable', 'fork', ';')
  ),

// ** A.6.6 Conditional statements
  // conditional_statement: $ => prec.left(seq(
  //   optional($.unique_priority),
  //   'if', '(', $.cond_predicate, ')', $.statement_or_null,
  //   // repseq('else', 'if', '(', $.cond_predicate, ')', $.statement_or_null),
  //   optseq('else', $.statement_or_null)
  // )),

  // prec.right because of:
  // module_nonansi_header  always_keyword  'if'  '('  cond_predicate  ')'  'if'  '('  cond_predicate  ')'  statement_or_null  •  'else'  …
  // 1:  module_nonansi_header  always_keyword  'if'  '('  cond_predicate  ')'  (conditional_statement  'if'  '('  cond_predicate  ')'  statement_or_null  •  'else'  statement_or_null)
  // 2:  module_nonansi_header  always_keyword  'if'  '('  cond_predicate  ')'  (conditional_statement  'if'  '('  cond_predicate  ')'  statement_or_null  •  conditional_statement_repeat1  'else'  statement_or_null)
  // 3:  module_nonansi_header  always_keyword  'if'  '('  cond_predicate  ')'  (conditional_statement  'if'  '('  cond_predicate  ')'  statement_or_null  •  conditional_statement_repeat1)
  // 4:  module_nonansi_header  always_keyword  'if'  '('  cond_predicate  ')'  (conditional_statement  'if'  '('  cond_predicate  ')'  statement_or_null)  •  'else'  …
  // Trying to make cond_statement the whole if/else if/else block
  conditional_statement: $ => prec.right(seq(
    optional($.unique_priority),
    'if', '(', $.cond_predicate, ')', $.statement_or_null,
    repeat(seq('else', 'if', '(', $.cond_predicate, ')', $.statement_or_null)),
    optional(seq('else', $.statement_or_null))
  )),

  unique_priority: $ => choice('unique', 'unique0', 'priority'),

  cond_predicate: $ => prec(PREC.CONDITIONAL, sepBy1('&&&', $._expression_or_cond_pattern)),

  _expression_or_cond_pattern: $ => choice(
    $.expression,
    $.cond_pattern
  ),

  cond_pattern: $ => seq(
    $.expression,
    'matches',
    $.pattern
  ),

// ** A.6.7 Case statements
  // case_statement: $ => seq(
  //   optional($.unique_priority),
  //   seq(
  //     $.case_keyword,
  //     '(', $.case_expression, ')',
  //     choice(
  //       repeat1($.case_item),
  //       seq('matches', repeat1($.case_pattern_item)),
  //       seq('inside', repeat1($.case_inside_item)) // only case
  //     )
  //   ),
  //   'endcase'
  // ),

  case_statement: $ => seq(
    optional($.unique_priority),
    choice(
      seq(
        $.case_keyword,
        '(', $.case_expression, ')',
        choice(
          repeat1($.case_item),
          seq('matches', repeat1($.case_pattern_item))
        )
      ),
      seq(
        'case',
        '(', $.case_expression, ')',
        'inside',
        repeat1($.case_inside_item)
      )
    ),
    'endcase'
  ),

  case_keyword: $ => choice('case', 'casez', 'casex'),

  case_expression: $ => $.expression,

  case_item: $ => choice(
    seq(sepBy1(',', $.case_item_expression), ':', $.statement_or_null),
    seq('default', optional(':'), $.statement_or_null)
  ),

  case_pattern_item: $ => choice(
    seq($.pattern, optional(seq('&&&', $.expression)), ':', $.statement_or_null),
    seq('default', optional(':'), $.statement_or_null)
  ),

  case_inside_item: $ => choice(
    seq($.range_list, ':', $.statement_or_null),
    seq('default', optional(':'), $.statement_or_null)
  ),

  case_item_expression: $ => $.expression,

  randcase_statement: $ => seq(
    'randcase', $.randcase_item, repeat($.randcase_item), 'endcase'
  ),

  randcase_item: $ => seq($.expression, ':', $.statement_or_null),

  range_list: $ => sepBy1(',', $.value_range),


  // A.6.7.1 Patterns
  // INFO: Modified from Drom's one
  pattern: $ => prec('pattern', choice(
    seq('(', $.pattern, ')'),
    seq('.', $._variable_identifier),
    '.*',
    $.constant_expression,
    seq('tagged', $.member_identifier, optional($.pattern)),
    seq('\'{', sepBy1(',', $.pattern), '}'),
    seq('\'{', sepBy1(',', seq($.member_identifier, ':', $.pattern)), '}')
  )),

  assignment_pattern: $ => seq(
    '\'{',
    choice(
      sepBy1(',', $.expression),
      sepBy1(',', seq($._structure_pattern_key, ':', $.expression)),
      sepBy1(',', seq($._array_pattern_key, ':', $.expression)),
      seq($.constant_expression, '{', sepBy1(',', $.expression), '}')
    ),
    '}'
  ),

  _structure_pattern_key: $ => prec('_structure_pattern_key', choice(
    $.member_identifier,
    $.assignment_pattern_key
  )),

  _array_pattern_key: $ => prec('_array_pattern_key', choice(
    $.constant_expression,
    $.assignment_pattern_key
  )),

  assignment_pattern_key: $ => choice(
    $._simple_type,
    'default'
  ),

  assignment_pattern_expression: $ => seq(
    optional($._assignment_pattern_expression_type), $.assignment_pattern
  ),

  _assignment_pattern_expression_type: $ => choice(
    $.ps_type_identifier,
    $.ps_parameter_identifier,
    $.integer_atom_type,
    $.type_reference
  ),

  // _constant_assignment_pattern_expression: $ => prec('_constant_assignment_pattern_expression', $.assignment_pattern_expression),
  _constant_assignment_pattern_expression: $ => $.assignment_pattern_expression,

  assignment_pattern_net_lvalue: $ => seq('\'{', sepBy1(',', $.net_lvalue), '}'),

  assignment_pattern_variable_lvalue: $ => seq(
    '\'{', sepBy1(',', $.variable_lvalue), '}'
  ),

// ** A.6.8 Looping statements
  loop_statement: $ => choice(
    seq('forever', $.statement_or_null),
    seq('repeat', '(', $.expression, ')', $.statement_or_null),
    seq('while', '(', $.expression, ')', $.statement_or_null),
    seq(
      'for', '(',
      optional($.for_initialization), ';',
      optional($.expression), ';',
      optional($.for_step),
      ')',
      $.statement_or_null
    ),
    seq('do', $.statement_or_null, 'while', '(', $.expression, ')', ';'),
    seq(
      'foreach', '(',
      $.ps_or_hierarchical_array_identifier,
      '[',
      optional($.loop_variables1),
      ']',
      ')',
      $.statement
    )
  ),

  for_initialization: $ => choice(
    $.list_of_variable_assignments,
    sepBy1(',', $.for_variable_declaration)
  ),

  for_variable_declaration: $ => prec.left(seq(
    optional('var'), $.data_type,
    sepBy1(',', seq($._variable_identifier, '=', $.expression))
  )),

  for_step: $ => sepBy1(',', $._for_step_assignment),

  _for_step_assignment: $ => choice(
    $.operator_assignment,
    $.inc_or_dec_expression,
    $.function_subroutine_call
  ),

  loop_variables1: $ => seq( // Avoid matching empty string!
    $.index_variable_identifier,
    repeat(seq(',', optional($.index_variable_identifier)))
  ),

// ** A.6.9 Subroutine call statements
  subroutine_call_statement: $ => prec('subroutine_call_statement', choice(
    seq($.subroutine_call, ';'),
    seq('void\'', '(', $.function_subroutine_call, ')', ';'),
    $.severity_system_task,    // INFO: Out of LRM
    $.simulation_control_task, // INFO: Out of LRM
  )),

// ** A.6.10 Assertion statements
  _assertion_item: $ => choice(
    $.concurrent_assertion_item,
    $.deferred_immediate_assertion_item
  ),

  deferred_immediate_assertion_item: $ => seq(
    optional(seq($._block_identifier, ':')),
    $._deferred_immediate_assertion_statement
  ),

  _procedural_assertion_statement: $ => choice(
    $._concurrent_assertion_statement,
    $._immediate_assertion_statement,
    $.checker_instantiation
  ),

  _immediate_assertion_statement: $ => choice(
    $._simple_immediate_assertion_statement,
    $._deferred_immediate_assertion_statement
  ),

  _simple_immediate_assertion_statement: $ => choice(
    $.simple_immediate_assert_statement,
    $.simple_immediate_assume_statement,
    $.simple_immediate_cover_statement
  ),

  simple_immediate_assert_statement: $ => seq(
    'assert', '(', $.expression, ')', $.action_block
  ),

  simple_immediate_assume_statement: $ => seq(
    'assume', '(', $.expression, ')', $.action_block
  ),

  simple_immediate_cover_statement: $ => seq(
    'cover', '(', $.expression, ')', $.statement_or_null
  ),

  _deferred_immediate_assertion_statement: $ => choice(
    $.deferred_immediate_assert_statement,
    $.deferred_immediate_assume_statement,
    $.deferred_immediate_cover_statement
  ),

  deferred_immediate_assert_statement: $ => seq(
    'assert',
    choice('#0', 'final'),
    '(', $.expression, ')', $.action_block
  ),

  deferred_immediate_assume_statement: $ => seq(
    'assume',
    choice('#0', 'final'),
    '(', $.expression, ')', $.action_block
  ),

  deferred_immediate_cover_statement: $ => seq(
    'cover',
    choice('#0', 'final'),
    '(', $.expression, ')', $.statement_or_null
  ),

// ** A.6.11 Clocking block
  clocking_declaration: $ => choice(
    seq(
      optional('default'),
      'clocking', optional($.clocking_identifier), $.clocking_event, ';',
      repeat($.clocking_item),
      'endclocking', optional(seq(':', $.clocking_identifier))
    ),
    seq(
      'global',
      'clocking', optional($.clocking_identifier), $.clocking_event, ';',
      'endclocking', optional(seq(':', $.clocking_identifier))
    )
  ),

  // INFO: Changed substantially from Drom's implementation, adapted more to 1800-2023
  clocking_event: $ => prec('clocking_event', seq('@', choice(
    $.ps_identifier,
    $.hierarchical_identifier,
    seq('(', $.event_expression, ')')
  ))),

  clocking_item: $ => choice(
    seq('default', $.default_skew, ';'),
    seq($.clocking_direction, $.list_of_clocking_decl_assign, ';'),
    seq(repeat($.attribute_instance), $._assertion_item_declaration)
  ),

  default_skew: $ => choice(
    seq('input', $.clocking_skew),
    seq('output', $.clocking_skew),
    seq('input', $.clocking_skew, 'output', $.clocking_skew)
  ),

  clocking_direction: $ => choice(
    seq('input', optional($.clocking_skew)),
    seq('output', optional($.clocking_skew)),
    seq('input', optional($.clocking_skew), 'output', optional($.clocking_skew)),
    seq('inout')
  ),

  list_of_clocking_decl_assign: $ => sepBy1(',', $.clocking_decl_assign),

  clocking_decl_assign: $ => seq($._signal_identifier, optional(seq('=', $.expression))),

  clocking_skew: $ => choice(
    seq($.edge_identifier, optional($.delay_control)),
    $.delay_control
  ),

  // clocking_drive: $ => prec(PREC.ASSIGN, seq(
  //   $.clockvar_expression, '<=', optional($.cycle_delay), $.expression
  // )),
  clocking_drive: $ => seq(
    $.clockvar_expression, '<=', optional($.cycle_delay), $.expression
  ),

  // INFO: Original by drom
  // cycle_delay: $ => prec.left(seq('##', choice(
  //   $.integral_number,
  //   $._identifier,
  //   seq('(', $.expression, ')')
  // ))),
  // End of INFO

  // INFO: By Larumbe
  cycle_delay: $ => seq('##', choice(
    $.integral_number,
    $._identifier,
    seq('(', $.expression, ')')
  )),
  // End of INFO

  clockvar: $ => $.hierarchical_identifier,

  clockvar_expression: $ => seq(
    $.clockvar,
    optional($.select1)
  ),

// ** A.6.12 Randsequence
  randsequence_statement: $ => seq(
    'randsequence', '(', optional($.rs_production_identifier), ')',
    repeat1($.rs_production),
    'endsequence'
  ),

  rs_production: $ => seq(
    optional($.data_type_or_void), $.rs_production_identifier,
    optional(seq('(', $.tf_port_list, ')')), ':', sepBy1('|', $.rs_rule), ';'
  ),

  rs_rule: $ => seq($.rs_production_list, optional(seq(':=', $.rs_weight_specification, optional($.rs_code_block)))),

  rs_production_list: $ => choice(
    repeat1($.rs_prod),
    seq('rand', 'join', optional(seq('(', $.expression, ')')), $.rs_production_item, repeat1($.rs_production_item))
  ),

  rs_weight_specification: $ => choice(
    $.integral_number,
    $.ps_identifier,
    seq('(', $.expression, ')')
  ),

  rs_code_block: $ => seq('{', repeat($.data_declaration), repeat($.statement_or_null), '}'),

  rs_prod: $ => choice(
    $.rs_production_item,
    $.rs_code_block,
    $.rs_if_else,
    $.rs_repeat,
    $.rs_case
  ),

  rs_production_item: $ => seq(
    $.rs_production_identifier, optional(seq('(', optional($.list_of_arguments), ')'))
  ),

  rs_if_else: $ => seq(
    'if', '(', $.expression, ')', $.rs_production_item, optional(seq('else', $.rs_production_item))
  ),

  rs_repeat: $ => seq(
    'repeat', '(', $.expression, ')', $.rs_production_item
  ),

  rs_case: $ => seq(
    'case', '(', $.case_expression, ')', repeat1($.rs_case_item), 'endcase'
  ),

  rs_case_item: $ => choice(
    seq(sepBy1(',', $.case_item_expression), ":", $.rs_production_item, ';'),
    seq('default', optional(':'), $.rs_production_item, ';')
  ),


// * A.7 Specify section
// ** A.7.1 Specify block declaration
  // specify_block: $ => seq('specify', repeat($._specify_item), 'endspecify'),

  // _specify_item: $ => choice(
  //   $.specparam_declaration,
  //   $.pulsestyle_declaration,
  //   $.showcancelled_declaration,
  //   $.path_declaration,
  //   $._system_timing_check
  // ),

  // pulsestyle_declaration: $ => seq(
  //   choice('pulsestyle_onevent', 'pulsestyle_ondetect'),
  //   $.list_of_path_outputs,
  //   ';'
  // ),

  // showcancelled_declaration: $ => seq(
  //   choice('showcancelled', 'noshowcancelled'),
  //   $.list_of_path_outputs,
  //   ';'
  // ),

// ** A.7.2 Specify path declarations
  // path_declaration: $ => seq(
  //   choice(
  //     $.simple_path_declaration,
  //     $.edge_sensitive_path_declaration,
  //     $.state_dependent_path_declaration
  //   ),
  //   ';'
  // ),

  // simple_path_declaration: $ => seq(
  //   choice($.parallel_path_description, $.full_path_description),
  //   '=',
  //   $.path_delay_value
  // ),

  // parallel_path_description: $ => seq(
  //   '(',
  //   $.specify_input_terminal_descriptor,
  //   optional($.polarity_operator),
  //   '=>',
  //   $.specify_output_terminal_descriptor,
  //   ')'
  // ),

  // full_path_description: $ => seq(
  //   '(',
  //   $.list_of_path_inputs,
  //   optional($.polarity_operator),
  //   '*>',
  //   $.list_of_path_outputs,
  //   ')'
  // ),

  // list_of_path_inputs: $ => sep1(',', $.specify_input_terminal_descriptor),

  // list_of_path_outputs: $ => sep1(',', $.specify_output_terminal_descriptor),

// ** A.7.3 Specify block terminals
  // specify_input_terminal_descriptor: $ => seq(
  //   $.input_identifier, optseq('[', $._constant_range_expression, ']')
  // ),

  // specify_output_terminal_descriptor: $ => seq(
  //   $.output_identifier, optseq('[', $._constant_range_expression, ']')
  // ),

  // input_identifier: $ => choice(
  //   $.input_port_identifier,
  //   $.inout_port_identifier,
  //   seq($.interface_identifier, '.', $.port_identifier) // FIXME glue dot?
  // ),

  // output_identifier: $ => choice(
  //   $.output_port_identifier,
  //   $.inout_port_identifier,
  //   seq($.interface_identifier, '.', $.port_identifier)
  // ),

// ** A.7.4 Specify path delays
  // path_delay_value: $ => choice(
  //   $.list_of_path_delay_expressions,
  //   seq('(', $.list_of_path_delay_expressions, ')')
  // ),

  // list_of_path_delay_expressions: $ => sep1(',', $.path_delay_expression),

  // // list_of_path_delay_expressions: $ => choice(
  // //   $.t_path_delay_expression,
  // //   seq($.trise_path_delay_expression, ',', $.tfall_path_delay_expression),
  // //   seq(
  // //     $.trise_path_delay_expression, ',', $.tfall_path_delay_expression, ',',
  // //     $.tz_path_delay_expression
  // //   ),
  // //   seq(
  // //     $.t01_path_delay_expression, ',', $.t10_path_delay_expression, ',',
  // //     $.t0z_path_delay_expression, ',', $.tz1_path_delay_expression, ',',
  // //     $.t1z_path_delay_expression, ',', $.tz0_path_delay_expression
  // //   ),
  // //   seq(
  // //     $.t01_path_delay_expression, ',', $.t10_path_delay_expression, ',',
  // //     $.t0z_path_delay_expression, ',', $.tz1_path_delay_expression, ',',
  // //     $.t1z_path_delay_expression, ',', $.tz0_path_delay_expression, ',',
  // //     $.t0x_path_delay_expression, ',', $.tx1_path_delay_expression, ',',
  // //     $.t1x_path_delay_expression, ',', $.tx0_path_delay_expression, ',',
  // //     $.txz_path_delay_expression, ',', $.tzx_path_delay_expression
  // //   )
  // // ),
  // //
  // // t_path_delay_expression: $ => alias($.path_delay_expression, $.t_path_delay_expression),
  // // trise_path_delay_expression: $ => alias($.path_delay_expression, $.trise_path_delay_expression),
  // // tfall_path_delay_expression: $ => alias($.path_delay_expression, $.tfall_path_delay_expression),
  // // tz_path_delay_expression: $ => alias($.path_delay_expression, $.tz_path_delay_expression),
  // // t01_path_delay_expression: $ => alias($.path_delay_expression, $.t01_path_delay_expression),
  // // t10_path_delay_expression: $ => alias($.path_delay_expression, $.t10_path_delay_expression),
  // // t0z_path_delay_expression: $ => alias($.path_delay_expression, $.t0z_path_delay_expression),
  // // tz1_path_delay_expression: $ => alias($.path_delay_expression, $.tz1_path_delay_expression),
  // // t1z_path_delay_expression: $ => alias($.path_delay_expression, $.t1z_path_delay_expression),
  // // tz0_path_delay_expression: $ => alias($.path_delay_expression, $.tz0_path_delay_expression),
  // // t0x_path_delay_expression: $ => alias($.path_delay_expression, $.t0x_path_delay_expression),
  // // tx1_path_delay_expression: $ => alias($.path_delay_expression, $.tx1_path_delay_expression),
  // // t1x_path_delay_expression: $ => alias($.path_delay_expression, $.t1x_path_delay_expression),
  // // tx0_path_delay_expression: $ => alias($.path_delay_expression, $.tx0_path_delay_expression),
  // // txz_path_delay_expression: $ => alias($.path_delay_expression, $.txz_path_delay_expression),
  // // tzx_path_delay_expression: $ => alias($.path_delay_expression, $.tzx_path_delay_expression),

  // path_delay_expression: $ => $.constant_mintypmax_expression,

  // edge_sensitive_path_declaration: $ => seq(
  //   choice(
  //     $.parallel_edge_sensitive_path_description,
  //     $.full_edge_sensitive_path_description
  //   ),
  //   '=', $.path_delay_value
  // ),

  // parallel_edge_sensitive_path_description: $ => seq(
  //   '(',
  //   optional($.edge_identifier),
  //   $.specify_input_terminal_descriptor,
  //   optional($.polarity_operator),
  //   '=>',
  //   '(',
  //   $.specify_output_terminal_descriptor,
  //   optional($.polarity_operator),
  //   ':',
  //   $.data_source_expression,
  //   ')',
  //   ')'
  // ),

  // full_edge_sensitive_path_description: $ => seq(
  //   '(',
  //   optional($.edge_identifier),
  //   $.list_of_path_inputs,
  //   optional($.polarity_operator),
  //   '*>',
  //   '(',
  //   $.list_of_path_outputs,
  //   optional($.polarity_operator),
  //   ':',
  //   $.data_source_expression,
  //   ')',
  //   ')'
  // ),

  // data_source_expression: $ => $.expression,

  edge_identifier: $ => choice('posedge', 'negedge', 'edge'),

  // state_dependent_path_declaration: $ => choice(
  //   seq('if', '(', $.module_path_expression, ')', $.simple_path_declaration),
  //   seq('if', '(', $.module_path_expression, ')', $.edge_sensitive_path_declaration),
  //   seq('ifnone', $.simple_path_declaration)
  // ),

  // polarity_operator: $ => choice('+', '-'),

// ** A.7.5 System timing checks
// *** A.7.5.1 System timing check commands
  // _system_timing_check: $ => choice(
  //   $.$setup_timing_check,
  //   $.$hold_timing_check,
  //   $.$setuphold_timing_check,
  //   $.$recovery_timing_check,
  //   $.$removal_timing_check,
  //   $.$recrem_timing_check,
  //   $.$skew_timing_check,
  //   $.$timeskew_timing_check,
  //   $.$fullskew_timing_check,
  //   $.$period_timing_check,
  //   $.$width_timing_check,
  //   $.$nochange_timing_check
  // ),

  // $setup_timing_check: $ => seq(
  //   '$setup', '(',
  //   $.data_event, ',', $.reference_event, ',', $.timing_check_limit,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $hold_timing_check: $ => seq(
  //   '$hold', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $setuphold_timing_check: $ => seq(
  //   '$setuphold', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit, ',', $.timing_check_limit,
  //   optseq(
  //     ',',
  //     optional($.notifier),
  //     optseq(
  //       ',',
  //       optional($.timestamp_condition),
  //       optseq(
  //         ',',
  //         optional($.timecheck_condition),
  //         optseq(
  //           ',',
  //           optional($.delayed_reference),
  //           optseq(
  //             ',',
  //             optional($.delayed_data)
  //           )
  //         )
  //       )
  //     )
  //   ),
  //   ')', ';'
  // ),

  // $recovery_timing_check: $ => seq(
  //   '$recovery', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $removal_timing_check: $ => seq(
  //   '$removal', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $recrem_timing_check: $ => seq(
  //   '$recrem', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit, ',', $.timing_check_limit,
  //   optseq(
  //     ',',
  //     optional($.notifier),
  //     optseq(',',
  //       optional($.timestamp_condition),
  //       optseq(',', optional($.timecheck_condition)),
  //       optseq(
  //         ',',
  //         optional($.delayed_reference),
  //         optseq(',', optional($.delayed_data))
  //       )
  //     )
  //   ),
  //   ')', ';'
  // ),

  // $skew_timing_check: $ => seq(
  //   '$skew', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $timeskew_timing_check: $ => seq(
  //   '$timeskew', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit,
  //   optseq(',',
  //     optional($.notifier),
  //     optseq(',',
  //       optional($.event_based_flag),
  //       optseq(',', optional($.remain_active_flag))
  //     )
  //   ),
  //   ')', ';'
  // ),

  // $fullskew_timing_check: $ => seq(
  //   '$fullskew', '(',
  //   $.reference_event, ',', $.data_event, ',', $.timing_check_limit, ',', $.timing_check_limit,
  //   optseq(',',
  //     optional($.notifier),
  //     optseq(',',
  //       optional($.event_based_flag),
  //       optseq(',', optional($.remain_active_flag))
  //     )
  //   ),
  //   ')', ';'
  // ),

  // $period_timing_check: $ => seq(
  //   '$period', '(', $.controlled_reference_event, ',', $.timing_check_limit,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $width_timing_check: $ => seq(
  //   '$width', '(',
  //   $.controlled_reference_event, ',', $.timing_check_limit, ',', $.threshold,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

  // $nochange_timing_check: $ => seq(
  //   '$nochange', '(',
  //   $.reference_event, ',', $.data_event, ',', $.start_edge_offset, ',', $.end_edge_offset,
  //   optseq(',', optional($.notifier)),
  //   ')', ';'
  // ),

// *** A.7.5.2 System timing check command arguments
  // timecheck_condition: $ => $.mintypmax_expression,

  // controlled_reference_event: $ => alias($.controlled_timing_check_event, $.controlled_reference_event),

  // data_event: $ => $.timing_check_event,

  // delayed_data: $ => seq(
  //   $.terminal_identifier, optional($.constant_mintypmax_expression)
  // ),

  // delayed_reference: $ => seq(
  //   $.terminal_identifier, optional($.constant_mintypmax_expression)
  // ),

  // end_edge_offset: $ => $.mintypmax_expression,

  // event_based_flag: $ => $.constant_expression,

  // notifier: $ => $._variable_identifier,

  // reference_event: $ => $.timing_check_event,

  // remain_active_flag: $ => $.constant_mintypmax_expression,

  // timestamp_condition: $ => $.mintypmax_expression,

  // start_edge_offset: $ => $.mintypmax_expression,

  // threshold: $ => $.constant_expression,

  // timing_check_limit: $ => $.expression,

// *** A.7.5.3 System timing check event definitions
  // timing_check_event: $ => seq(
  //   optional($.timing_check_event_control),
  //   $._specify_terminal_descriptor,
  //   optseq('&&&', $.timing_check_condition)
  // ),

  // controlled_timing_check_event: $ => seq(
  //   $.timing_check_event_control,
  //   $._specify_terminal_descriptor,
  //   optseq('&&&', $.timing_check_condition)
  // ),

  // timing_check_event_control: $ => choice(
  //   'posedge', 'negedge', 'edge', $.edge_control_specifier
  // ),

  // _specify_terminal_descriptor: $ => choice(
  //   $.specify_input_terminal_descriptor,
  //   $.specify_output_terminal_descriptor
  // ),

  // edge_control_specifier: $ => seq(
  //   'edge', '[', sep1(',', $.edge_descriptor), ']'
  // ),

  // // Note: Embedded spaces are illegal.
  // edge_descriptor: $ => choice(
  //   '01',
  //   '10',
  //   /[xXzZ][01]/,
  //   /[01][xXzZ]/
  // ),

  // timing_check_condition: $ => choice(
  //   $.scalar_timing_check_condition,
  //   seq('(', $.scalar_timing_check_condition, ')')
  // ),

  // scalar_timing_check_condition: $ => choice(
  //   $.expression,
  //   seq('~', $.expression),
  //   seq($.expression, '==', $.scalar_constant),
  //   seq($.expression, '===', $.scalar_constant),
  //   seq($.expression, '!=', $.scalar_constant),
  //   seq($.expression, '!==', $.scalar_constant)
  // ),

  // scalar_constant: $ => choice(
  //   '1\'b0',
  //   '1\'b1',
  //   '1\'B0',
  //   '1\'B1',
  //   '\'b0',
  //   '\'b1',
  //   '\'B0',
  //   '\'B1',
  //   '1',
  //   '0'
  // ),

// * A.8 Expressions
// ** A.8.1 Concatenations
  // concatenation: $ => seq(
  //   '{', psep1(PREC.CONCAT, ',', $.expression), '}'
  // ),
  concatenation: $ => seq('{', sepBy1(',', $.expression), '}'),

  // TODO: What about the PREC.CONCAT?
  constant_concatenation: $ => seq(
    '{', sepBy1(',', $.constant_expression), '}'
  ),

  // constant_multiple_concatenation: $ => prec.left(PREC.CONCAT, seq(
  //   '{', $.constant_expression, $.constant_concatenation, '}'
  // )),
  constant_multiple_concatenation: $ => seq(
    '{', $.constant_expression, $.constant_concatenation, '}'
  ),

  // module_path_concatenation: $ => seq(
  //   '{', psep1(PREC.CONCAT, ',', $.module_path_expression), '}'
  // ),

  // module_path_multiple_concatenation: $ => prec.left(PREC.CONCAT, seq(
  //   '{', $.constant_expression, $.module_path_concatenation, '}'
  // )),

  // multiple_concatenation: $ => prec.left(PREC.CONCAT, seq(
  //   '{', $.expression, $.concatenation, '}'
  // )),
  multiple_concatenation: $ => seq(
    '{', $.expression, $.concatenation, '}'
  ),

  // streaming_concatenation: $ => prec.left(PREC.CONCAT, seq(
  //   '{', $.stream_operator, optional($.slice_size), $.stream_concatenation, '}'
  // )),
  streaming_concatenation: $ => seq(
    '{', $.stream_operator, optional($.slice_size), $.stream_concatenation, '}'
  ),
  // streaming_concatenation: $ => seq(
  //   '{', $.stream_operator, prec.dynamic(1, optional($.slice_size)), $.stream_concatenation, '}'
  // ),

  stream_operator: $ => choice('>>', '<<'),

  slice_size: $ => choice($._simple_type, $.constant_expression),
  // slice_size: $ => prec.left(choice($._simple_type, $.constant_expression)),
  // slice_size: $ => $._simple_type,

  // stream_concatenation: $ => prec.left(PREC.CONCAT, seq(
  //   '{', sepBy1(',', $.stream_expression), '}'
  // )),
  stream_concatenation: $ => seq(
    '{', sepBy1(',', $.stream_expression), '}'
  ),

  stream_expression: $ => seq($.expression, optional(seq('with', '[', $.array_range_expression, ']'))),

  array_range_expression: $ => seq(
    $.expression,
    optional(choice(
      seq( ':', $.expression),
      seq('+:', $.expression),
      seq('-:', $.expression)
    ))
  ),

  empty_unpacked_array_concatenation: $ => prec('empty_unpacked_array_concatenation', seq('{', '}')),

// ** A.8.2 Subroutine calls
  constant_function_call: $ => $.function_subroutine_call,

  // tf_call: $ => prec.left(seq(
  //   $._hierarchical_tf_identifier, // FIXME
  //   // $.ps_or_hierarchical_tf_identifier,
  //   repeat($.attribute_instance),
  //   optional($.list_of_arguments_parent)
  // )),
  tf_call: $ => prec('tf_call', seq(
    $.ps_or_hierarchical_tf_identifier,
    repeat($.attribute_instance),
    optional(seq('(', optional($.list_of_arguments), ')'))
  )),

  // system_tf_call: $ => prec.left(seq(
  //   $.system_tf_identifier,
  //   optional(choice(
  //     $.list_of_arguments_parent,
  //     seq(
  //       '(',
  //       choice(
  //         seq($.data_type, optseq(',', $.expression)),
  //         prec.left(seq(
  //           sep1(',', $.expression),
  //           optseq(',', optional($.clocking_event))
  //         ))
  //       ),
  //       ')'
  //     )
  //   ))
  // )),
  system_tf_call: $ => seq(
    $.system_tf_identifier,
    choice(
      optional(seq('(', optional($.list_of_arguments), ')')),
      seq('(',
          choice(
            seq($.data_type, optional(seq(',', $.expression))),
            seq(sepBy1(',', $.expression), optional(seq(',', $.clocking_event))),
          ),
          ')')
    )),

  subroutine_call: $ => choice(
    $.tf_call,
    $.system_tf_call,
    $.method_call,
    seq(optional(seq('std', '::')), $.randomize_call),
  ),

  function_subroutine_call: $ => $.subroutine_call,

  // list_of_arguments: $ => choice(
  //   // seq(
  //   //   sep1(',', optional($.expression)),
  //   //   repseq(',', '.', $._identifier, '(', optional($.expression), ')')
  //   // ),
  //   sep1(',', seq('.', $._identifier, '(', optional($.expression), ')'))
  // ),

  // list_of_arguments: $ => prec('list_of_arguments', choice(  // Reordered to avoid matching empty string
  list_of_arguments: $ => prec.left(PREC.PARENT, choice(  // Reordered to avoid matching empty string
    // First case: mixing positional and named arguments
    seq(
      $.expression,
      repeat(seq(',', optional($.expression))),
      repeat(seq(',', '.', $._identifier, '(', optional($.expression), ')'))
    ),
    seq(
      optional($.expression),
      repeat1(seq(',', optional($.expression))),
      repeat(seq(',', '.', $._identifier, '(', optional($.expression), ')'))
    ),
    seq(
      optional($.expression),
      repeat(seq(',', optional($.expression))),
      repeat1(seq(',', '.', $._identifier, '(', optional($.expression), ')'))
    ),
    // Second case: using only named arguments
    sepBy1(',', seq('.', $._identifier, '(', optional($.expression), ')'))
  )),

  // list_of_arguments_parent: $ => seq(
  //   '(',
  //   choice(
  //     sep1(',', $.expression),
  //     // sep1(',', optional($.expression)), // FIXME
  //     seq(
  //       repseq(',', '.', $._identifier, '(', optional($.expression), ')')
  //     ),
  //     sep1(',', seq(',', '.', $._identifier, '(', optional($.expression), ')'))
  //   ),
  //   ')'
  // ),

  method_call: $ => seq(
    $._method_call_root,
    choice(
      '.',
      '::'  // INFO Out of LRM: Needed to support static method calls
    ),
    $.method_call_body)
  ,

  method_call_body: $ => choice(
    seq(
      $.method_identifier,
      repeat($.attribute_instance),
      optional(seq('(', optional($.list_of_arguments), ')'))
    ),
    $._built_in_method_call
  ),

  _built_in_method_call: $ => choice(
    $.array_manipulation_call,
    $.randomize_call
  ),

  array_manipulation_call: $ => seq(
    $.array_method_name,
    repeat($.attribute_instance),
    optional(seq('(', optional($.list_of_arguments), ')')),
    optional(seq('with', '(', $.expression, ')'))
  ),

  // randomize_call: $ => prec.left(seq(
  //   'randomize',
  //   repeat($.attribute_instance),
  //   optseq(
  //     '(',
  //     optional(choice(
  //       $.variable_identifier_list,
  //       'null'
  //     )),
  //     ')'
  //   ),
  //   optseq(
  //     'with',
  //     optseq(
  //       '(',
  //       optional($.identifier_list),
  //       ')'
  //     ),
  //     $.constraint_block
  //   )
  // )),

  randomize_call: $ => seq(
    'randomize', repeat($.attribute_instance),
    optional(seq('(', optional(choice($.variable_identifier_list, 'null')), ')')),
    optional(seq('with', optional(seq('(', optional($.identifier_list), ')')), $.constraint_block))
  ),

  _method_call_root: $ => prec('_method_call_root', choice(
    prec.dynamic(0, $.primary),
    // INFO: Modified wrt LRM, the implicit_class_handle should be matched by the $.primary
    // second condition. However there must be some precedences that prevent this from being
    // detected. This workaround might complicate a bit more the parser but seems to work well.
    prec.dynamic(1, seq($.implicit_class_handle, optional($.select1))),
    // End of INFO
    $.class_type, // INFO: Out of LRM: Added to support calling parameterized static methods
    $.text_macro_usage,// INFO: Out of LRM, added to fix parsing errors in UVM
  )),

  array_method_name: $ => choice(
    $.method_identifier, 'unique', 'and', 'or', 'xor'
  ),

// ** A.8.3 Expressions
  inc_or_dec_expression: $ => choice(
    seq($.inc_or_dec_operator, repeat($.attribute_instance), $.variable_lvalue),
    seq($.variable_lvalue, repeat($.attribute_instance), $.inc_or_dec_operator)
  ),

  conditional_expression: $ => prec.right(PREC.CONDITIONAL, seq(
    $.cond_predicate,
    '?',
    repeat($.attribute_instance), $.expression,
    ':',
    $.expression
  )),

  constant_expression: $ => choice(
    $.constant_primary,

    prec.left(PREC.UNARY, seq(
      $.unary_operator, repeat($.attribute_instance), $.constant_primary
    )),

    // TODO: Review these expressions and precedences
    constExprOp($, PREC.ADD, choice('+', '-')),
    constExprOp($, PREC.MUL, choice('*', '/', '%')),
    constExprOp($, PREC.EQUAL, choice('==', '!=', '===', '!==', '==?', '!=?')),
    constExprOp($, PREC.LOGICAL_AND, '&&'),
    constExprOp($, PREC.LOGICAL_OR, '||'),
    constExprOp($, PREC.POW, '**'),
    constExprOp($, PREC.RELATIONAL, choice('<', '<=', '>', '>=')),
    constExprOp($, PREC.AND, '&'),
    constExprOp($, PREC.OR, '|'),
    constExprOp($, PREC.XOR, choice('^', '^~', '~^')),
    constExprOp($, PREC.SHIFT, choice('>>', '<<', '>>>', '<<<')),
    constExprOp($, PREC.IMPLICATION, choice('->', '<->')),

    prec.right(PREC.CONDITIONAL, seq(
      $.constant_expression,
      '?',
      repeat($.attribute_instance), $.constant_expression,
      ':',
      $.constant_expression
    )),

    $.text_macro_usage, // INFO: Out of LRM but needed for some basic preprocessing parsing
  ),

  constant_mintypmax_expression: $ => prec('constant_mintypmax_expression', seq(
    $.constant_expression,
    optional(seq(':', $.constant_expression, ':', $.constant_expression))
  )),

  constant_param_expression: $ => choice(
    prec.dynamic(1, $.constant_mintypmax_expression),
    prec.dynamic(0, $.data_type),
    '$'
  ),

  param_expression: $ => prec('param_expression', choice(
    $.mintypmax_expression,
    $.data_type,
    '$'
  )),

  _constant_range_expression: $ => choice(
    $.constant_expression,
    $._constant_part_select_range
  ),

  _constant_part_select_range: $ => prec('_constant_part_select_range', choice(
    $.constant_range,
    $.constant_indexed_range
  )),

  constant_range: $ => seq($.constant_expression, ':', $.constant_expression),

  constant_indexed_range: $ => seq(
    $.constant_expression, choice('+:', '-:'), $.constant_expression
  ),

  // TODO: Review precedences, and exprOp function, all this section in general
  expression: $ => choice(
    $.primary,

    prec.left(PREC.UNARY, seq(
      $.unary_operator, repeat($.attribute_instance), $.primary
    )),
    prec.left(PREC.UNARY, $.inc_or_dec_expression),
    prec.left(PREC.PARENT, seq('(', $.operator_assignment, ')')),

    // TODO: Review precedences and operators, but they look good overall
    exprOp($, PREC.ADD, choice('+', '-')),
    exprOp($, PREC.MUL, choice('*', '/', '%')),
    exprOp($, PREC.EQUAL, choice('==', '!=', '===', '!==', '==?', '!=?')),
    exprOp($, PREC.LOGICAL_AND, '&&'),
    exprOp($, PREC.LOGICAL_OR, '||'),
    exprOp($, PREC.POW, '**'),
    exprOp($, PREC.RELATIONAL, choice('<', '<=', '>', '>=')),
    exprOp($, PREC.AND, '&'),
    exprOp($, PREC.OR, '|'),
    exprOp($, PREC.XOR, choice('^', '^~', '~^')),
    exprOp($, PREC.SHIFT, choice('>>', '<<', '>>>', '<<<')),
    exprOp($, PREC.IMPLICATION, choice('->', '<->')),

    $.conditional_expression,
    $.inside_expression,
    $.tagged_union_expression,

    $.type_reference,// DANGER: Out of LRM explicitly, but should be (6.23)
    $.text_macro_usage, // DANGER: Out of LRM
  ),

  tagged_union_expression: $ => seq(
    'tagged',
    $.member_identifier,
    optional($.primary)
  ),

  inside_expression: $ => prec.left(PREC.RELATIONAL, seq(
    $.expression, 'inside', '{', $.range_list, '}'
  )),

  value_range: $ => prec('value_range', choice(
    $.expression,
    seq('[', $.expression, ':', $.expression, ']'),
    seq('[', '$', ':', $.expression, ']'),
    seq('[', $.expression, ':', '$', ']'),
    seq('[', $.expression, '+', '/', '-', $.expression, ']'),
    seq('[', $.expression, '+', '%', '-', $.expression, ']'),
  )),

  mintypmax_expression: $ => prec('mintypmax_expression', seq(
    $.expression,
    optional(seq(':', $.expression, ':', $.expression))
  )),

  // module_path_conditional_expression: $ => seq(
  //   $.module_path_expression,
  //   '?',
  //   repeat($.attribute_instance), $.module_path_expression,
  //   ':',
  //   $.module_path_expression
  // ),

  // module_path_expression: $ => choice(
  //   $.module_path_primary
  //   // seq($.unary_module_path_operator, repeat($.attribute_instance), $.module_path_primary),
  //   // seq(
  //   //   $.module_path_expression,
  //   //   $.binary_module_path_operator,
  //   //   repeat($.attribute_instance),
  //   //   $.module_path_expression
  //   // ),
  //   // $.module_path_conditional_expression
  // ),

  // module_path_mintypmax_expression: $ => seq(
  //   $.module_path_expression,
  //   optseq(
  //     ':', $.module_path_expression,
  //     ':', $.module_path_expression
  //   )
  // ),

  _part_select_range: $ => prec('_part_select_range', choice(
    $.constant_range,
    $.indexed_range
  )),

  indexed_range: $ => seq(
    $.expression, choice('+:', '-:'), $.constant_expression
  ),

  _genvar_expression: $ => $.constant_expression,

// ** A.8.4 Primaries
  // TODO: Probably the ones with prec.dynamic below can be grouped with some aliases/inlining or whatever
  // option, since they match the same path as the ps_parameter_identifier, but in different contexts (and
  // tree-sitter is not aware of them )
  constant_primary: $ => prec('constant_primary', choice(
    $.primary_literal,
    seq($.ps_parameter_identifier, optional($.constant_select1)),
    // // seq($.specparam_identifier, optseq('[', $._constant_range_expression, ']')),
    // prec.dynamic(-1, $.genvar_identifier), // TODO: No need to add, matched by the ps_parameter [constant_select] above
    // prec.dynamic(-1, seq($.formal_port_identifier, optional($.constant_select1))), // TODO: No need to add, same syntax as the ps_parameter_identifier constant_select1 above
    // seq(optional(choice($.package_scope, $.class_scope)), $.enum_identifier), // TODO: No need to add, also matched by the ps_parameter_identifier branch above
    seq($.constant_concatenation, optional(seq('[', $._constant_range_expression, ']'))),
    seq($.constant_multiple_concatenation, optional(seq('[', $._constant_range_expression, ']'))),
    seq($.constant_function_call, optional(seq('[', $._constant_range_expression, ']'))),
    // $._constant_let_expression, // TODO: No need to add since it's syntax is the same as a tf_call (true ambiguity)
    seq('(', $.constant_mintypmax_expression, ')'),
    $.constant_cast,
    $._constant_assignment_pattern_expression,
    $.type_reference,

    '$', // DANGER: Out of LRM explicitly, but required for 7.10.4 (bullet point 47): The $ primary shall be legal only in a select for a queue variable.
    'null'
  )),

  // module_path_primary: $ => choice(
  //   $._number,
  //   $._identifier,
  //   $.module_path_concatenation,
  //   $.module_path_multiple_concatenation,
  //   $.function_subroutine_call,
  //   seq('(', $.module_path_mintypmax_expression, ')')
  // ),

  primary: $ => prec('primary', choice(
    $.primary_literal,
    choice(
      seq( // INFO: This is the one in the LRM
        optional(choice($.class_qualifier, $.package_scope)),
        $.hierarchical_identifier,
        optional($.select1)
      ),
      // INFO: The one below should be included in the one above, however it doesn't work well
      // possibly because of some bad specified precedence/conflict. For the time being, adding
      // the option below fixes things and seems to work well (at the expense of some more complexity
      // in the parser)
      seq($.implicit_class_handle, optional($.select1)), // INFO: Out of LRM, but used as a workaround
      // seq(choice($.class_qualifier, $.package_scope), optional($.select1)), // Tried this instead of the one above, but broke things and didn't add anything new
    ),
    $.empty_unpacked_array_concatenation,
    seq($.concatenation, optional(seq('[', $.range_expression, ']'))),
    seq($.multiple_concatenation, optional(seq('[', $.range_expression, ']'))),
    $.function_subroutine_call,
    // $.let_expression, // TODO: No need to add since it's syntax is the same as a tf_call (true ambiguity)
    seq('(', $.mintypmax_expression, ')'),
    $.cast,
    $.assignment_pattern_expression,
    $.streaming_concatenation,
    // $.sequence_method_call, // TODO: Remove temporarily to narrow conflicts
    'this',
    '$',
    'null',
    '$root', // DANGER: Out of LRM but needed for sv-tests/chapter-20/20.14--coverage
    '\'{}',  // DANGER: Out of LRM but fixes errors in some UVM files
  )),

  class_qualifier: $ => prec('class_qualifier', choice( // Reordered to avoid matching empty string
    seq('local', '::'),
    seq(optional(seq('local', '::')), choice(seq($.implicit_class_handle, '.'), $.class_scope))
  )),

  range_expression: $ => choice(
    $.expression,
    $._part_select_range
  ),

  primary_literal: $ => choice(
    $._number,
    $.time_literal,
    $.unbased_unsized_literal,
    $.string_literal,
  ),

  time_literal: $ => choice(
    seq($.unsigned_number, $.time_unit),
    seq($.fixed_point_number, $.time_unit)
  ),

  time_unit: $ => choice('s', 'ms', 'us', 'ns', 'ps', 'fs'),

  string_literal: $ => seq(
    '"',
    repeat(choice(
      token.immediate(/[^\\"]+/),
      // EXTENDS Verilog spec with escape sequences
      token.immediate(seq('\\', /./)),
      token.immediate(seq('\\', '\n'))
    )),
    '"'
  ),

  implicit_class_handle: $ => prec('implicit_class_handle', choice(
    seq('this', optional(seq('.', 'super'))),
    'super'
  )),

  bit_select1: $ => repeat1( // reordered -> non empty
    seq('[', $.expression, ']')
  ),

  // TODO: Review
  select1: $ => choice( // reordered -> non empty
    seq( // 1xx
      // INFO: First line overlaps a lot with $.hierarchical_identifier, but that one uses constant_bit_select
      repeat(seq('.', $.member_identifier, optional($.bit_select1))), '.', $.member_identifier,
      optional($.bit_select1),
      optional(seq('[', $._part_select_range, ']'))
    ),
    seq( // 01x
      //
      $.bit_select1,
      optional(seq('[', $._part_select_range, ']'))
    ),
    seq( // 001
      //
      //
      seq('[', $._part_select_range, ']')
    )
  ),

  // nonrange_select1: $ => choice( // reordered -> non empty
  //   prec.left(PREC.PARENT, seq( // 1x
  //     repseq('.', $.member_identifier, optional($.bit_select1)), '.', $.member_identifier,
  //     optional($.bit_select1)
  //   )),
  //   $.bit_select1
  // ),
  nonrange_select1: $ => choice(  // reordered -> non empty
    seq( // 1x
      repeat(seq('.', $.member_identifier, optional($.bit_select1))), '.', $.member_identifier,
      optional($.bit_select1)
    ),
    $.bit_select1
  ),

  constant_bit_select1: $ => repeat1(prec('constant_bit_select1', seq( // reordered -> non empty
    '[', $.constant_expression, ']'
  ))),

  // TODO: Review with range tests
  constant_select1: $ => prec('constant_select1', choice( // reordered -> non empty
    seq(
      repeat(prec('constant_select1', seq('.', $.member_identifier, optional($.constant_bit_select1)))), '.', $.member_identifier,
      optional($.constant_bit_select1),
      optional(seq('[', $._constant_part_select_range, ']'))
    ),
    seq(
      $.constant_bit_select1,
      optional(seq('[', $._constant_part_select_range, ']'))
    ),
    seq('[', $._constant_part_select_range, ']'),
  )),

  constant_cast: $ => seq($.casting_type, '\'', '(', $.constant_expression, ')'),

  _constant_let_expression: $ => $.let_expression,

  cast: $ => prec('cast', seq($.casting_type, '\'', '(', $.expression, ')')),


// ** A.8.5 Expression left-side values
  // INFO: drom's one
  // net_lvalue: $ => choice(
  //   seq(
  //     $.ps_or_hierarchical_net_identifier,
  //     optional($.constant_select1)
  //   ),
  //   prec.left(PREC.CONCAT, seq('{', sep1(',', $.net_lvalue), '}')),
  //   seq(
  //     optional($._assignment_pattern_expression_type),
  //     $.assignment_pattern_net_lvalue
  //   )
  // ),
  // INFO: Mine
  net_lvalue: $ => choice(
    seq(
      $.ps_or_hierarchical_net_identifier,
      optional($.constant_select1)
    ),
    seq('{', sepBy1(',', $.net_lvalue), '}'),
    // seq(
    //   optional($._assignment_pattern_expression_type),
    //   $.assignment_pattern_net_lvalue
    // )
  ),

  // TODO: Compare with original and develop
  variable_lvalue: $ => prec('variable_lvalue', choice(
    seq(
      optional(choice(
        seq($.implicit_class_handle, '.'),
        $.package_scope,
        $.class_qualifier // INFO: Out of LRM, needed for static class access in LHS
      )),
      $._hierarchical_variable_identifier,
      optional($.select1)
    ),

    seq('{', sepBy1(',', $.variable_lvalue), '}'),

    seq(
      optional($._assignment_pattern_expression_type),
      $.assignment_pattern_variable_lvalue
    ),

    $.streaming_concatenation
  )),

  // variable_lvalue: $ => choice(
  //   prec.left(PREC.PARENT, seq(
  //     optional(choice(
  //       seq($.implicit_class_handle, '.'),
  //       $.package_scope
  //     )),
  //     $._hierarchical_variable_identifier,
  //     optional($.select1)
  //   )),
  //   prec.left(PREC.CONCAT, seq('{', sep1(',', $.variable_lvalue), '}')),
  //   prec.left(PREC.ASSIGN, seq(
  //     optional($._assignment_pattern_expression_type),
  //     $.assignment_pattern_variable_lvalue
  //   )),
  //   $.streaming_concatenation
  // ),

  nonrange_variable_lvalue: $ => seq(
    optional(choice(
      seq($.implicit_class_handle, '.'),
      $.package_scope
    )),
    $._hierarchical_variable_identifier,
    optional($.nonrange_select1)
  ),

// ** A.8.6 Operators
  unary_operator: $ => choice(
    '+', '-', '!', '~', '&', '~&', '|', '~|', '^', '~^', '^~'
  ),

  inc_or_dec_operator: $ => choice('++', '--'),

  // // unary_module_path_operator = '~&' /
  // //   '~|' /
  // //   '~^' /
  // //   '^~' /
  // //   $('!'![ != ]) /
  // //   $('~'!'=') /
  // //   $('&'!'=') /
  // //   $('|'!'=') /
  // //   $('^'!'=')
  // //
  // // binary_module_path_operator = $('=='!'=') /
  // //   $('!='!'=') /
  // //   '&&' /
  // //   '||' /
  // //   $('&'!'=') /
  // //   $('|'!'=') /
  // //   $('^'!'=') /
  // //   '^~' /
  // //   '~^'

// ** A.8.7 Numbers
  _number: $ => choice($.integral_number, $.real_number),

  integral_number: $ => choice(
    $.decimal_number,
    $.octal_number,
    $.binary_number,
    $.hex_number
  ),

  decimal_number: $ => choice(
    $.unsigned_number,
    token(seq(
      optional(seq(/[1-9][0-9_]*/, /\s*/)),
      /'[sS]?[dD]/,
      /\s*/,
      /[0-9][0-9_]*/
    )),
    token(seq(
      optional(seq(/[1-9][0-9_]*/, /\s*/)),
      /'[sS]?[dD]/,
      /\s*/,
      /[xXzZ?][_]*/
    ))
  ),

  binary_number: $ => token(seq(
    optional(seq(/[1-9][0-9_]*/, /\s*/)),
    /'[sS]?[bB]/,
    /\s*/,
    /[01xXzZ?][01xXzZ?_]*/
  )),

  octal_number: $ => token(seq(
    optional(seq(/[1-9][0-9_]*/, /\s*/)),
    /'[sS]?[oO]/,
    /\s*/,
    /[0-7xXzZ?][0-7xXzZ?_]*/
  )),

  hex_number: $ => token(seq(
    optional(seq(/[1-9][0-9_]*/, /\s*/)),
    /'[sS]?[hH]/,
    /\s*/,
    /[0-9a-fA-FxXzZ?][0-9a-fA-FxXzZ?_]*/
  )),

  // // NOTE: Embedded spaces are illegal.
  // non_zero_unsigned_number: $ => token(/[1-9][0-9_]*/),

  real_number: $ => choice(
    $.fixed_point_number,
    token(/[0-9][0-9_]*(\.[0-9][0-9_]*)?[eE][+-]?[0-9][0-9_]*/)
  ),

  fixed_point_number: $ => token(/[0-9][0-9_]*\.[0-9][0-9_]*/),

  unsigned_number: $ => token(/[0-9][0-9_]*/),

  // // The apostrophe ( ' ) in unbased_unsized_literal shall not be followed by white_space.
  unbased_unsized_literal: $ => choice('\'0', '\'1', /'[xXzZ]/),

// * A.9 General
// ** A.9.1 Attributes
  attribute_instance: $ => seq('(*', sepBy1(',', $.attr_spec), '*)'),

  attr_spec: $ => seq($._attr_name, optional(seq('=', $.constant_expression))),

  _attr_name: $ => $._identifier,

// ** A.9.2 Comments
  // comment: $ => one_line_comment | block_comment
  // one_line_comment: $ => // comment_text \n
  // block_comment: $ => /* comment_text */
  // comment_text: $ => { Any_ASCII_character }

  // http://stackoverflow.com/questions/13014947/regex-to-match-a-c-style-multiline-comment/36328890#36328890
  // from: https://github.com/tree-sitter/tree-sitter-c/blob/master/grammar.js
  comment: $ => token(choice(
    seq('//', /.*/),
    seq(
      '/*',
      /[^*]*\*+([^/*][^*]*\*+)*/,
      '/'
    )
  )),

// ** A.9.3 Identifiers
  // _array_identifier: $ => $._identifier,
  _block_identifier: $ => $._identifier,
  _bin_identifier: $ => $._identifier,
  // INFO: Set properly: Tried with both options but didn't work to recognize DPI properly
  c_identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,
  // c_identifier: $ => token(/[a-zA-Z_][a-zA-Z0-9_]*/),
  // End of INFO
  // cell_identifier: $ => alias($._identifier, $.cell_identifier),
  checker_identifier: $ => $._identifier,
  class_identifier: $ => $._identifier,
  class_variable_identifier: $ => $._variable_identifier,
  clocking_identifier: $ => alias($._identifier, $.clocking_identifier),
  // config_identifier: $ => alias($._identifier, $.config_identifier),
  const_identifier: $ => alias($._identifier, $.const_identifier),
  constraint_identifier: $ => alias($._identifier, $.constraint_identifier),

  covergroup_identifier: $ => alias($._identifier, $.covergroup_identifier),

  // // covergroup_variable_identifier = _variable_identifier
  cover_point_identifier: $ => alias($._identifier, $.cover_point_identifier),
  cross_identifier: $ => alias($._identifier, $.cross_identifier),
  dynamic_array_variable_identifier: $ => alias($._variable_identifier, $.dynamic_array_variable_identifier),
  enum_identifier: $ => alias($._identifier, $.enum_identifier),
  escaped_identifier: $ => seq('\\', /[^\s]*/),
  // formal_identifier: $ => alias($._identifier, $.formal_identifier),
  formal_port_identifier: $ => alias($._identifier, $.formal_port_identifier),
  function_identifier: $ => alias($._identifier, $.function_identifier),
  generate_block_identifier: $ => alias($._identifier, $.generate_block_identifier),
  genvar_identifier: $ => alias($._identifier, $.genvar_identifier),
  _hierarchical_array_identifier: $ => $.hierarchical_identifier,
  _hierarchical_block_identifier: $ => $.hierarchical_identifier,
  _hierarchical_event_identifier: $ => $.hierarchical_identifier,

  // prec.left because of:
  // module_nonansi_header  'var'  _identifier  '='  _identifier  •  '.'  …
  //   1:  module_nonansi_header  'var'  _identifier  '='  (hierarchical_identifier  _identifier)  •  '.'  …
  //   2:  module_nonansi_header  'var'  _identifier  '='  (hierarchical_identifier_repeat1  _identifier  •  '.')
  // hierarchical_identifier: $ => prec.left('hierarchical_identifier', seq( // TODO: Not sure if it's prec.left
  // hierarchical_identifier: $ => prec.left('hierarchical_identifier', seq( // TODO: Not sure if it's prec.left
  // hierarchical_identifier: $ => prec.right('hierarchical_identifier', seq( // TODO: Not sure if it's prec.left
  // hierarchical_identifier: $ => seq( // TODO: Not sure if it's prec.left
  hierarchical_identifier: $ => prec('hierarchical_identifier', seq( // TODO: Not sure if it's prec.left
    optional(seq('$root', '.')),
    // INFO: Slightly out of LRM to support use of macros as part of hierarchical identifiers
    repeat(prec('hierarchical_identifier', seq(choice($._identifier, $.text_macro_usage), optional($.constant_bit_select1), '.'))),
    // repeat(prec('hierarchical_identifier', seq($._identifier, optional($.constant_bit_select1), '.'))),
    // End of INFO
    $._identifier
  )),
  // INFO: After removin the prec.left it allowed the ['constant_primary', 'primary'] conflict in precedences!!

  _hierarchical_net_identifier: $ => $.hierarchical_identifier,
  _hierarchical_parameter_identifier: $ => $.hierarchical_identifier,
  _hierarchical_property_identifier: $ => $.hierarchical_identifier,
  _hierarchical_sequence_identifier: $ => $.hierarchical_identifier,
  _hierarchical_task_identifier: $ => $.hierarchical_identifier,
  _hierarchical_tf_identifier: $ => $.hierarchical_identifier,
  _hierarchical_variable_identifier: $ => $.hierarchical_identifier,

  _identifier: $ => choice(
    $.simple_identifier,
    $.escaped_identifier
  ),

  index_variable_identifier: $ => alias($._identifier, $.index_variable_identifier),
  interface_identifier: $ => $._identifier,
  // interface_instance_identifier: $ => alias($._identifier, $.interface_instance_identifier),
  interface_port_identifier: $ => alias($._identifier, $.interface_port_identifier),
  // inout_port_identifier: $ => alias($._identifier, $.inout_port_identifier),
  // input_port_identifier: $ => alias($._identifier, $.input_port_identifier),
  instance_identifier: $ => alias($._identifier, $.instance_identifier),
  // library_identifier: $ => alias($._identifier, $.library_identifier),
  member_identifier: $ => alias($._identifier, $.member_identifier),
  method_identifier: $ => alias($._identifier, $.method_identifier),
  modport_identifier: $ => alias($._identifier, $.modport_identifier),
  module_identifier: $ => $._identifier,
  _net_identifier: $ => $._identifier,
  _net_type_identifier: $ => $._identifier,
  // output_port_identifier: $ => alias($._identifier, $.output_port_identifier),
  package_identifier: $ => $._identifier,

  package_scope: $ => prec('package_scope', choice(
    seq($.package_identifier, '::'),
    seq('$unit', '::')
  )),

  parameter_identifier: $ => alias($._identifier, $.parameter_identifier),
  port_identifier: $ => $._identifier,
  // production_identifier: $ => alias($._identifier, $.production_identifier),
  program_identifier: $ => $._identifier,
  property_identifier: $ => alias($._identifier, $.property_identifier),

  // Set prec.left because of:
  // module_nonansi_header  'var'  _identifier  '='  _identifier  •  '::'  …
  //   1:  module_nonansi_header  'var'  _identifier  '='  (package_scope  _identifier  •  '::')
  //   2:  module_nonansi_header  'var'  _identifier  '='  (ps_class_identifier  _identifier)  •  '::'  …
  // ps_class_identifier: $ => prec.left(seq(
  ps_class_identifier: $ => seq(
    optional($.package_scope), $.class_identifier
  ),

  // ps_covergroup_identifier: $ => seq(
  //   optional($.package_scope), $.covergroup_identifier
  // ),

  ps_checker_identifier: $ => seq(
    optional($.package_scope), $.checker_identifier
  ),

  ps_identifier: $ => prec('ps_identifier', seq(
    optional($.package_scope), $._identifier
  )),

  ps_or_hierarchical_array_identifier: $ => seq(
    optional(choice(
      seq($.implicit_class_handle, '.'),
      $.class_scope,
      $.package_scope
    )),
    $._hierarchical_array_identifier
  ),

  // ps_or_hierarchical_net_identifier: $ => choice(
  //   prec.left(PREC.PARENT, seq(optional($.package_scope), $._net_identifier)),
  //   $._hierarchical_net_identifier
  // ),
  ps_or_hierarchical_net_identifier: $ => choice(
    seq(optional($.package_scope), $._net_identifier),
    $._hierarchical_net_identifier
  ),

  ps_or_hierarchical_property_identifier: $ => choice(
    seq(optional($.package_scope), $.property_identifier),
    $._hierarchical_property_identifier
  ),

  ps_or_hierarchical_sequence_identifier: $ => choice(
    seq(optional($.package_scope), $._sequence_identifier),
    $._hierarchical_sequence_identifier
  ),

  ps_or_hierarchical_tf_identifier: $ => choice(
    seq(optional($.package_scope), $.tf_identifier),
    $._hierarchical_tf_identifier
  ),

  // TODO: Fill and set all the cases
  ps_parameter_identifier: $ => prec('ps_parameter_identifier', choice(
    seq(
      optional(choice(
        $.package_scope,
        $.class_scope
      )),
      $.parameter_identifier
    ),
    // seq(
    //   repseq(
    //     $.generate_block_identifier,
    //     optseq('[', $.constant_expression, ']'),
    //     '.'
    //   ),
    //   $.parameter_identifier
    // )
  )),

  ps_type_identifier: $ => prec('ps_type_identifier', seq(
    optional(choice(
      seq('local', '::'),
      $.package_scope,
      $.class_scope
    )),
    $._type_identifier
  )),

  rs_production_identifier: $ => $._identifier,

  _sequence_identifier: $ => $._identifier,

  _signal_identifier: $ => $._identifier,

  // // A simple_identifier or c_identifier shall
  // // start with an alpha or underscore ( _ ) character,
  // // shall have at least one character, and shall not have any spaces.
  simple_identifier: $ => /[a-zA-Z_][a-zA-Z0-9_$]*/,

  // specparam_identifier: $ => alias($._identifier, $.specparam_identifier),

  // // The $ character in a system_tf_identifier shall
  // // not be followed by white_space. A system_tf_identifier shall not be escaped.
  system_tf_identifier: $ => /\$[a-zA-Z0-9_$]+/,

  task_identifier: $ => alias($._identifier, $.task_identifier),
  tf_identifier: $ => alias($._identifier, $.tf_identifier),
  // terminal_identifier: $ => alias($._identifier, $.terminal_identifier),
  // topmodule_identifier: $ => alias($._identifier, $.topmodule_identifier),
  _type_identifier: $ => $._identifier,
  // _udp_identifier: $ => $._identifier,
  _variable_identifier: $ => $._identifier,

// ** A.9.4 White space

  // // white_space: $ => space | tab | newline | eof};



// * 20. Utility system tasks and system functions
// ** 20.2 Simulation control system tasks
  simulation_control_task: $ => seq(
    choice('$stop', '$finish', '$exit'),
    optional(seq('(', optional($.list_of_arguments), ')')),
    ';'
  ),

// * 22. Compiler directives
  // `__FILE__ [22.13]
  // `__LINE__ [22.13]
  // `begin_keywords [22.14]
  // `celldefine [22.10]
  // `default_nettype [22.8]
  // `define [22.5.1]
  // `else [22.6]
  // `elsif [22.6]
  // `end_keywords [22.14]
  // `endcelldefine [22.10]
  // `endif [22.6]
  // `ifdef [22.6]
  // `ifndef [22.6]
  // `include [22.4]
  // `line [22.12]
  // `nounconnected_drive [22.9]
  // `pragma [22.11]
  // `resetall [22.3]
  // `timescale [22.7]
  // `unconnected_drive [22.9]
  // `undef [22.5.2]
  // `undefineall [22.5.3]

  _directives: $ => prec('_directives', choice(
    $.resetall_compiler_directive,
    $.include_compiler_directive,
    $.text_macro_definition,
    $.text_macro_usage,
    $.undefine_compiler_directive,
    $.undefineall_compiler_directive,
    $.conditional_compilation_directive,
    $.timescale_compiler_directive,
    $.default_nettype_compiler_directive,
    $.unconnected_drive_compiler_directive,
    $.celldefine_compiler_directive,
    $.endcelldefine_compiler_directive,
    $.pragma,
    $.line_compiler_directive,
    $.file_or_line_compiler_directive,
    $.keywords_directive,
    $.endkeywords_directive
  )),

// ** 22-3 `resetall
  resetall_compiler_directive: $ => directive('resetall'),


// ** 22-4 `include
  double_quoted_string: $ => seq(
    '"', token.immediate(prec(1, /[^\\"\n]+/)), '"'
  ),

  include_compiler_directive_standard: $ => seq(
    '<', token.immediate(prec(1, /[^\\>\n]+/)), '>'
  ),

  include_compiler_directive: $ => seq(
    directive('include'),
    choice(
      $.double_quoted_string,
      $.include_compiler_directive_standard,
      $.text_macro_usage,// INFO: Out of LRM (test sv-tests/chapter-22/22.5.1--include-define-expansion)
    )
  ),


// ** 22.5 `define, `undef, and `undefineall
  default_text: $ => /\w+/,

  macro_text: $ => /(\\(.|\r?\n)|[^\\\n])*/,

  text_macro_definition: $ => seq(
    directive('define'),
    $.text_macro_name,
    optional($.macro_text),
    '\n'
  ),

  text_macro_name: $ => seq(
    $.text_macro_identifier,
    optional(seq('(', $.text_macro_list_of_formal_arguments, ')'))
  ),

  text_macro_list_of_formal_arguments: $ => sepBy1(',', $.text_macro_formal_argument),

  text_macro_formal_argument: $ => seq(
    $.simple_identifier,
    optional(seq('=', $.default_text))
  ),

  text_macro_identifier: $ => $._identifier,

  text_macro_usage: $ => prec.right('text_macro_usage', seq(
    '`',
    $.text_macro_identifier,
    optional(seq('(', optional($.text_macro_list_of_actual_arguments), ')'))
  )),

  // text_macro_list_of_actual_arguments: $ => sepBy1(',', $.text_macro_actual_argument),
  // text_macro_list_of_actual_arguments: $ => $.list_of_arguments, // INFO: Out of LRM, but needed to support empty actual argument between commas in macros
  text_macro_list_of_actual_arguments: $ => prec.left(PREC.PARENT, choice(  // INFO: Out of LRM, but needed to support empty actual argument between commas in macros, and to support data_types as arguments
    // First case: mixing positional and named arguments
    seq(
      $.text_macro_actual_argument,
      repeat(seq(',', optional($.text_macro_actual_argument))),
      repeat(seq(',', '.', $._identifier, '(', optional($.text_macro_actual_argument), ')'))
    ),
    seq(
      optional($.text_macro_actual_argument),
      repeat1(seq(',', optional($.text_macro_actual_argument))),
      repeat(seq(',', '.', $._identifier, '(', optional($.text_macro_actual_argument), ')'))
    ),
    seq(
      optional($.text_macro_actual_argument),
      repeat(seq(',', optional($.text_macro_actual_argument))),
      repeat1(seq(',', '.', $._identifier, '(', optional($.text_macro_actual_argument), ')'))
    ),
    // Second case: using only named arguments
    sepBy1(',', seq('.', $._identifier, '(', optional($.text_macro_actual_argument), ')'))
  )),

  // text_macro_actual_argument: $ => $.expression,
  text_macro_actual_argument: $ => $.param_expression, // INFO: Out of LRM, but needed to support parameterized data types as macro args (used in the UVM)

  undefine_compiler_directive: $ => seq(directive('undef'), $.text_macro_identifier),

  undefineall_compiler_directive: $ => directive('undefineall'),


  // DANGER: Remove this?
  // TODO missing arguments, empty list of arguments

  // To use a macro defined with arguments, the name of the text macro shall be
  // followed by a list of actual arguments in parentheses, separated by
  // commas. Actual arguments and defaults shall not contain comma or right
  // parenthesis characters outside matched pairs of left and right parentheses
  // (), square brackets [], braces {}, double quotes "", or an escaped
  // identifier.
  // End of DANGER

  // _actual_argument: $ => choice(
  //   // $.expression, // TODO: Comment to avoid parsing syntax of macros as it might make things more complicated for the time being
  //   // $.data_type // INFO: Many UVM macros require a class type as an argument
  //   // $.macro_text // TODO: Gave many conflicts and errors, but should be the correct one,  or at least an option (with less precedence)?
  // ),


// ** 22.6 `ifdef, `else, `elsif, `endif, `ifndef
  // conditional_compilation_directive ::=
  //   ifdef_or_ifndef ifdef_condition block_of_text
  //   { `elsif ifdef_condition block_of_text }
  //   [ `else block_of_text ]
  //   `endif

  conditional_compilation_directive: $ => choice( // Rearranged, don't parse preprocessed code
    seq($.ifdef_or_ifndef, $.ifdef_condition),
    seq(directive('elsif'), $.ifdef_condition),
    directive('else'),
    directive('endif')
  ),

  ifdef_or_ifndef: $ => choice(directive('ifdef'), directive('ifndef')),

  ifdef_condition: $ => choice(
    $.text_macro_identifier,
    seq('(', $.ifdef_macro_expression, ')')
  ),

  ifdef_macro_expression: $ => prec.left(choice(
    $.text_macro_identifier,
    seq($.ifdef_macro_expression, $.binary_logical_operator, $.ifdef_macro_expression),
    seq('!', $.ifdef_macro_expression),
    seq('(', $.ifdef_macro_expression, ')')
  )),

  binary_logical_operator: $ => choice('&&', '||', '->', '<->'),

// ** 22-7 timescale
  timescale_compiler_directive: $ => seq(
    directive('timescale'),
    $.time_literal, // time_unit,
    '/',
    $.time_literal, // time_precision
    '\n' // TODO: Are newlines required?
  ),

// ** 22-8 default_nettype
  default_nettype_compiler_directive: $ => seq(
    directive('default_nettype'),
    $.default_nettype_value,
    // '\n' ; DANGER:
  ),

  default_nettype_value: $ => choice('wire', 'tri', 'tri0', 'tri1', 'wand', 'triand', 'wor', 'trior', 'trireg', 'uwire', 'none'),

// ** 22-9
  unconnected_drive_compiler_directive: $ => seq(
    directive('unconnected_drive'),
    choice('pull0', 'pull1'),
    '\n'
  ),

// ** 22.10 `celldefine and `endcelldefine
  celldefine_compiler_directive: $ => directive('celldefine'),
  endcelldefine_compiler_directive: $ => directive('endcelldefine'),


// ** 22.11 `pragma
  pragma: $ => prec.right(seq(
    directive('pragma'),
    $.pragma_name,
    sepBy(',', $.pragma_expression),
  )),

  pragma_name: $ => $.simple_identifier,

  pragma_expression: $ => choice(
    $.pragma_keyword,
    seq($.pragma_keyword, '=', $.pragma_value),
    $.pragma_value,
  ),

  pragma_value: $ => choice(
    seq('(', sepBy1(',', $.pragma_expression) , ')'),
    $._number,
    $.string_literal,
    $._identifier,
  ),

  pragma_keyword: $ => $.simple_identifier,

// ** 22-12 `line
  line_compiler_directive: $ => seq(
    directive('line'),
    $.unsigned_number,
    $.double_quoted_string,
    token(/[0-2]/),
    // $.unsigned_number,
    '\n'
  ),

// ** 22.13 `__FILE__ and `__LINE__
  file_or_line_compiler_directive: $ => choice(
    directive('__FILE__'),
    directive('__LINE__'),
  ),

// ** 22.14 `begin_keywords, `end_keywords
  keywords_directive: $ => seq(
    directive('begin_keywords'),
    '\"', $.version_specifier, '\"'
  ),

  version_specifier: $ => choice(
    '1800-2023',
    '1800-2017',
    '1800-2012',
    '1800-2009',
    '1800-2005',
    '1364-2005',
    '1364-2001',
    '1364-2001-noconfig',
    '1364-1995',
  ),

  endkeywords_directive: $ => directive('end_keywords'),

};


// * Tree-sitter
// ** Module exports
module.exports = grammar({
  name: 'verilog',
  word: $ => $.simple_identifier,
  rules: rules,
  extras: $ => [/\s/, $.comment],

// ** Inline
  inline: $ => [
    // Reviewed
    $.module_identifier,
    $.interface_identifier,
    $.program_identifier,
    $.checker_identifier,
    $.class_identifier,
    $.package_identifier,

    $.port_identifier,

    $.any_parameter_declaration,

    // $._port_expression,


    // TODO: Not reviewed

    // $.hierarchical_identifier, // DANGER:  Deinlined on purpose!
    $._hierarchical_net_identifier,
    $._hierarchical_variable_identifier,
    $._hierarchical_tf_identifier,
    $._hierarchical_sequence_identifier,
    $._hierarchical_property_identifier,
    $._hierarchical_block_identifier,
    $._hierarchical_task_identifier,

  //   $.ps_or_hierarchical_net_identifier,
    $.ps_or_hierarchical_tf_identifier,
  //   $.ps_or_hierarchical_sequence_identifier,
  //   $.ps_or_hierarchical_property_identifier,

    $.ps_class_identifier,
  //   $.ps_covergroup_identifier,
    $.ps_parameter_identifier,
    $.ps_type_identifier,
    $.ps_checker_identifier,

    $.parameter_identifier,
    $.covergroup_identifier,
    $.enum_identifier,
    $.formal_port_identifier,
    $.genvar_identifier,
  //   $.specparam_identifier,
    $.tf_identifier,
    $._type_identifier,
    $._net_type_identifier,
    $._variable_identifier,
  //   $._udp_identifier,
    $.dynamic_array_variable_identifier,
    $.class_variable_identifier,
  //   $.interface_instance_identifier,
    $.let_identifier,
  //   $.sequence_identifier,
    $._net_identifier,
    $.member_identifier,
    $._block_identifier,
    $.instance_identifier,
    $.property_identifier,
  //   // $.input_port_identifier,
  //   // $.output_port_identifier,
  //   // $.inout_port_identifier,
  //   // $.input_identifier,
  //   // $.output_identifier,
    $.cover_point_identifier,
    $.cross_identifier,

    $._expression_or_cond_pattern,
    // $.pragma_keyword,
    // $.incomplete_class_scoped_type,
    $._constant_assignment_pattern_expression,
    $._elaboration_severity_system_task,
  ],

// ** Precedences
  precedences: () => [
    // Top level precedence
    // Used when declarations and/or statements are outside of sequential statements,
    // modules, classes, packages or checkers
    // Use case: snippets of code on web, include files...
    ['statement_or_null', 'package_or_generate_item_declaration'],
    // ['_description', 'statement'],
    ['_non_port_module_item', 'package_or_generate_item_declaration', '_description'],
    ['statement_item', 'package_or_generate_item_declaration', '_description'],
    ['_package_item', '_module_or_generate_item_declaration'],
    ['_module_common_item', '_description'],


    // module_nonansi_header  'input'  data_type  •  simple_identifier  …
    //   1:  module_nonansi_header  'input'  (_var_data_type  data_type)  •  simple_identifier  …
    //   2:  module_nonansi_header  'input'  (data_type_or_implicit1  data_type)  •  simple_identifier  …  (precedence: 'data_type_or_implicit1')
    ['_var_data_type', 'data_type_or_implicit1'],


    // module_nonansi_header  'input'  _identifier  •  ';'  …
    //   1:  module_nonansi_header  'input'  _identifier  (_variable_dimension  unpacked_dimension)  •  ';'  …
    //   2:  module_nonansi_header  'input'  _identifier  (list_of_port_identifiers_repeat1  unpacked_dimension)  •  ';'  …
    // ['list_of_port_identifiers_repeat', '_variable_dimension'],
    ['list_of_port_identifiers', '_variable_dimension'],


    // LRM 6.10: Implicit declarations:
    //   If an identifier is used in a port expression declaration, then an implicit net
    //   of default net type shall be assumed, with the vector width of the port expression declaration.
    //
    // module_nonansi_header  'input'  _identifier  •  ';'  …
    //   1:  module_nonansi_header  'input'  (list_of_port_identifiers  _identifier)  •  ';'  …
    //   2:  module_nonansi_header  'input'  (list_of_variable_identifiers  _identifier)  •  ';'  …
    ['list_of_port_identifiers', 'list_of_variable_identifiers'],
    // module_nonansi_header  'output'  _identifier  •  ';'  …
    //   1:  module_nonansi_header  'output'  (list_of_port_identifiers  _identifier)  •  ';'  …
    //   2:  module_nonansi_header  'output'  (list_of_variable_port_identifiers  _identifier)  •  ';'  …
    ['list_of_port_identifiers', 'list_of_variable_port_identifiers'],


    // module_keyword  module_identifier  '('  _identifier  •  ')'  …
    //   1:  module_keyword  module_identifier  '('  (ansi_port_declaration  _identifier)  •  ')'  …
    //   2:  module_keyword  module_identifier  '('  (port_reference  _identifier)  •  ')'  …
    ['port_reference', 'ansi_port_declaration'],


    // For ANSI port declaration, if there is no builtin net type assume it's an interface identifier and not a net
    // module_keyword  module_identifier  '('  _identifier  •  simple_identifier  …
    //   1:  module_keyword  module_identifier  '('  (interface_port_header  _identifier)  •  simple_identifier  …
    //   2:  module_keyword  module_identifier  '('  (net_port_type1  _identifier)  •  simple_identifier  …
    ['interface_port_header', 'net_port_type1'],


    // This one doesn't make much sense, but prioritize ansi_port_declaration
    // module_keyword  module_identifier  '('  _identifier  unpacked_dimension  •  ')'  …
    //   1:  module_keyword  module_identifier  '('  _identifier  (_variable_dimension  unpacked_dimension)  •  ')'  …            (precedence: '_variable_dimension')
    //   2:  module_keyword  module_identifier  '('  _identifier  (ansi_port_declaration_repeat1  unpacked_dimension)  •  ')'  …
    ['ansi_port_declaration', '_variable_dimension'],


    // This one doesn't seem to make much sense for module declarations, but port
    // will be used in module instantiation with unconnected ports, so prioritize it.
    // module_keyword  module_identifier  '('  '.'  _identifier  '('  ')'  •  ')'  …
    //   1:  module_keyword  module_identifier  '('  (ansi_port_declaration  '.'  _identifier  '('  ')')  •  ')'  …  (precedence: 'ansi_port_declaration')
    //   2:  module_keyword  module_identifier  '('  (port  '.'  _identifier  '('  ')')  •  ')'  …
    // ['port', 'ansi_port_declaration'],


    // TODO: Review this one after deinlining hierarchical_identifier
    // Set higher precedence to hierarchical_identifier than to select1/constant_select1 since
    // the latter is optional (according to LRM can match the empty string).
    // INFO: However, take into account that there should be a conflict below for the case
    // when there is actually a select1 besides the hierarchical_identifier
    //
    // module_nonansi_header  'var'  _identifier  '='  _identifier  '.'  •  simple_identifier  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  (hierarchical_identifier_repeat1  _identifier  '.')  •  simple_identifier  …
    //   2:  module_nonansi_header  'var'  _identifier  '='  _identifier  (select1  '.'  •  _identifier  '['  _part_select_range  ']')
    //   3:  module_nonansi_header  'var'  _identifier  '='  _identifier  (select1  '.'  •  _identifier  bit_select1  '['  _part_select_range  ']')
    //   4:  module_nonansi_header  'var'  _identifier  '='  _identifier  (select1  '.'  •  _identifier  bit_select1)
    //   5:  module_nonansi_header  'var'  _identifier  '='  _identifier  (select1  '.'  •  _identifier)
    //   6:  module_nonansi_header  'var'  _identifier  '='  _identifier  (select1_repeat1  '.'  •  _identifier  bit_select1)
    //   7:  module_nonansi_header  'var'  _identifier  '='  _identifier  (select1_repeat1  '.'  •  _identifier)
    // ['hierarchical_identifier', 'select1'], // INFO: I think this one is redundant or not needed anymore
    ['hierarchical_identifier', 'constant_select1'],


    // TODO: Removed to fix the expressions with primaries inside a bit_select1!!
    //
    // INFO: constant_primary has precedence since it refers to hierarchical_identifier instead of to select1, which in theory should simplify things quite a lot
    // module_nonansi_header  'var'  _identifier  '='  _identifier  '['  primary_literal  •  '/'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (constant_primary  primary_literal)  •  '/'  …
    //   2:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (primary  primary_literal)  •  '/'  …
    // ['constant_primary', 'primary'],
    // module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  •  '/'  …
    // 1:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (constant_primary  _identifier)  •  '/'  …  (precedence: 'ps_parameter_identifier')
    // 2:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (primary  _identifier)  •  '/'  …           (precedence: 'primary')
    // ['ps_parameter_identifier', 'primary'],


    // Case 1 is for non-ansi port with constant_part_select.
    // Case 2 is for first ansi-port (interface type or net_type) with unpacked array.
    //
    //   module_keyword  module_identifier  '('  _identifier  '['  constant_range  •  ']'  …
    //     1:  module_keyword  module_identifier  '('  _identifier  '['  (_constant_part_select_range  constant_range)  •  ']'  …
    //     2:  module_keyword  module_identifier  '('  _identifier  (unpacked_dimension  '['  constant_range  •  ']')
    ['unpacked_dimension', '_constant_part_select_range'],
    //   module_keyword  module_identifier  '('  _identifier  '['  constant_expression  ']'  •  ')'  …
    //     1:  module_keyword  module_identifier  '('  _identifier  (constant_bit_select1_repeat1  '['  constant_expression  ']')  •  ')'  …
    //     2:  module_keyword  module_identifier  '('  _identifier  (unpacked_dimension  '['  constant_expression  ']')  •  ')'  …            (precedence: 'unpacked_dimension')
    ['unpacked_dimension', 'constant_bit_select1'],


    // module_nonansi_header  always_keyword  '@'  _identifier  •  ';'  …
    // 1:  module_nonansi_header  always_keyword  '@'  (ps_identifier  _identifier)  •  ';'  …
    // 2:  module_nonansi_header  always_keyword  (clocking_event  '@'  _identifier)  •  ';'  …  (precedence: 0, associativity: Left)
    ['clocking_event', 'ps_identifier'],


    // module_keyword  module_identifier  '('  '.'  _identifier  '('  _identifier  •  ')'  …
    //   1:  module_keyword  module_identifier  '('  '.'  _identifier  '('  (port_reference  _identifier)  •  ')'  …  (precedence: 'port_reference')
    //   2:  module_keyword  module_identifier  '('  '.'  _identifier  '('  (primary  _identifier)  •  ')'  …         (precedence: 0, associativity: Left)
    ['port_reference', 'primary'],


    // module_nonansi_header  'var'  _identifier  '='  _identifier  '['  class_scope  •  simple_identifier  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (class_qualifier  class_scope)  •  simple_identifier  …
    //   2:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (constant_primary  class_scope  •  _identifier  constant_select1)
    //   3:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  (constant_primary  class_scope  •  _identifier)
    ['class_qualifier', 'ps_parameter_identifier'],


    // TODO: Removed to fix the expressions with primaries inside a bit_select1!!
    //
    // module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  '.'  _identifier  •  '/'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  (constant_select1  '.'  _identifier)  •  '/'  …  (precedence: 'constant_select1')
    //   2:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  (select1  '.'  _identifier)  •  '/'  …           (precedence: 'select1')
    // ['constant_select1', 'select1'],


    // module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  '['  constant_range  •  ']'  …
    // 1:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  '['  (_constant_part_select_range  constant_range)  •  ']'  …  (precedence: '_constant_part_select_range')
    // 2:  module_nonansi_header  'var'  _identifier  '='  _identifier  '['  _identifier  '['  (_part_select_range  constant_range)  •  ']'  …
    ['_constant_part_select_range', '_part_select_range'],


    //   module_nonansi_header  always_keyword  'if'  '('  expression  'matches'  '('  constant_expression  •  ')'  …
    //   1:  module_nonansi_header  always_keyword  'if'  '('  expression  'matches'  '('  (constant_mintypmax_expression  constant_expression)  •  ')'  …
    //   2:  module_nonansi_header  always_keyword  'if'  '('  expression  'matches'  '('  (pattern  constant_expression)  •  ')'  …
    ['pattern', 'constant_mintypmax_expression'],


    // For regular identifiers, assume that they are always hierarchical if they have no package scope or hierarchical path
    //
    //   module_nonansi_header  'initial'  '@'  _identifier  •  ';'  …
    //     1:  module_nonansi_header  'initial'  '@'  (hierarchical_identifier  _identifier)  •  ';'  …  (precedence: 'hierarchical_identifier', associativity: Right)
    //     2:  module_nonansi_header  'initial'  '@'  (ps_identifier  _identifier)  •  ';'  …            (precedence: 'ps_identifier')
    ['hierarchical_identifier', 'ps_identifier'],


    // For this case, in a module header, only the port_reference makes sense:
    //
    //   _module_header1  '('  '.'  _identifier  '('  _identifier  •  ')'  …
    //   1:  _module_header1  '('  '.'  _identifier  '('  (hierarchical_identifier  _identifier)  •  ')'  …  (precedence: 'hierarchical_identifier')
    //   2:  _module_header1  '('  '.'  _identifier  '('  (port_reference  _identifier)  •  ')'  …           (precedence: 'port_reference')
    ['port_reference', 'hierarchical_identifier'],


    // TODO: Not sure about this one either.
    // Set higher precedence on constant_primary than on another hierarchical_identifier for dimension/select expressions of hierarchical identifiers
    //
    //   module_nonansi_header  'initial'  hierarchical_identifier  '['  _identifier  •  '/'  …
    //     1:  module_nonansi_header  'initial'  hierarchical_identifier  '['  (constant_primary  _identifier)  •  '/'  …         (precedence: 'ps_parameter_identifier')
    //     2:  module_nonansi_header  'initial'  hierarchical_identifier  '['  (hierarchical_identifier  _identifier)  •  '/'  …  (precedence: 'hierarchical_identifier')
    // ['ps_parameter_identifier', 'hierarchical_identifier'],


    // module_nonansi_header  'initial'  '@'  '('  '('  expression  •  ')'  …
    // 1:  module_nonansi_header  'initial'  '@'  '('  '('  (event_expression  expression)  •  ')'  …      (precedence: 'event_expression', associativity: Left)
    // 2:  module_nonansi_header  'initial'  '@'  '('  '('  (mintypmax_expression  expression)  •  ')'  …  (precedence: 'mintypmax_expression')
    ['event_expression', 'mintypmax_expression'],


    // First one doesn't really make much sense:
    //
    //   module_nonansi_header  'var'  _identifier  '='  implicit_class_handle  '.'  •  '$root'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  (class_qualifier  implicit_class_handle  '.')  •  '$root'  …                        (precedence: 'class_qualifier')
    //   2:  module_nonansi_header  'var'  _identifier  '='  (variable_lvalue  implicit_class_handle  '.'  •  hierarchical_identifier  select1)  (precedence: 'variable_lvalue')
    //   3:  module_nonansi_header  'var'  _identifier  '='  (variable_lvalue  implicit_class_handle  '.'  •  hierarchical_identifier)           (precedence: 'variable_lvalue')
    ['variable_lvalue', 'class_qualifier'],

    // tf_port_direction is in a higher level in the tree, for the 'ref' conflict
    //
    //   'function'  function_identifier  '('  'ref'  •  'var'  …
    //   1:  'function'  function_identifier  '('  (port_direction  'ref')  •  'var'  …
    //   2:  'function'  function_identifier  '('  (tf_port_direction  'ref')  •  'var'  …
    ['tf_port_direction', 'port_direction'],


    // First option follows the path: data_type_or_implicit1 -> data_type -> seq($._type_identifier, repeat($.packed_dimension))
    // Second option follows the path: data_type_or_implicit1 -> implicit_data_type1 -> repeat1($.packed_dimension)
    // In theory this is not a legal case since a packed array should be set for vector types, like bit/logic, not for the
    // implicit one (which is int). Set to the first one for potential future conflicts and because it is not 'completely implicit'
    // if setting the packed dimension.
    //
    //
    //   'localparam'  _identifier  unsized_dimension  •  '['  …
    //   1:  'localparam'  _identifier  (_variable_dimension  unsized_dimension)  •  '['  …  (precedence: '_variable_dimension')
    //   2:  'localparam'  _identifier  (packed_dimension  unsized_dimension)  •  '['  …
    ['_variable_dimension', 'packed_dimension'],


    // Set higher precedence on data_types (variables) than on interfaces or user defined nets, since it would be necessary
    // to parse other files/units to know exactly what they are, and this simplifies the parser.
    // TODO: Can be moved together with another up very similar upwards!
    //
    //   _module_header1  '('  _identifier  •  simple_identifier  …
    //   1:  _module_header1  '('  (data_type  _identifier)  •  simple_identifier  …              (precedence: 'data_type')
    //   2:  _module_header1  '('  (interface_port_header  _identifier)  •  simple_identifier  …  (precedence: 'interface_port_header')
    //   3:  _module_header1  '('  (net_port_type1  _identifier)  •  simple_identifier  …         (precedence: 'net_port_type1')
    ['data_type', 'interface_port_header', 'net_port_type1'],


    // Identify as a constant_mintypmax_expression -> constant_expression on the RHS instead of a data_type (since it's a declaration)
    //
    //   'localparam'  _identifier  '='  _identifier  •  ';'  …
    //   1:  'localparam'  _identifier  '='  (constant_primary  _identifier)  •  ';'  …  (precedence: 'ps_parameter_identifier')
    //   2:  'localparam'  _identifier  '='  (data_type  _identifier)  •  ';'  …         (precedence: 'data_type')
    ['ps_parameter_identifier', 'data_type'],


    // tf_port_item1 seems more generic, so resolve it to this node for this particular case
    //
    //   'function'  function_identifier  '('  _identifier  •  ')'  …
    //   1:  'function'  function_identifier  '('  (data_type  _identifier)  •  ')'  …      (precedence: 'data_type')
    //   2:  'function'  function_identifier  '('  (tf_port_item1  _identifier)  •  ')'  …n
    ['tf_port_item1', 'data_type'],


    // Even though the class_scope is implicitly a data_type, it should not be needed to set it as a node
    //
    //   _identifier  '#'  '('  class_scope  •  simple_identifier  …
    //   1:  _identifier  '#'  '('  (class_qualifier  class_scope)  •  simple_identifier  …      (precedence: 'class_qualifier')
    //   2:  _identifier  '#'  '('  (data_type  class_scope  •  _identifier  data_type_repeat1)  (precedence: 'data_type')
    //   3:  _identifier  '#'  '('  (data_type  class_scope  •  _identifier)                     (precedence: 'data_type')
    ['class_qualifier', 'data_type'],


    // Since it's a declaration, it's not a part select but a packed dimension for a localparam
    //
    //   'localparam'  _identifier  '='  _identifier  '['  constant_range  •  ']'  …
    //   1:  'localparam'  _identifier  '='  _identifier  '['  (_constant_part_select_range  constant_range)  •  ']'  …  (precedence: '_constant_part_select_range')
    //   2:  'localparam'  _identifier  '='  _identifier  (packed_dimension  '['  constant_range  •  ']')                (precedence: 'packed_dimension')
    ['packed_dimension', '_constant_part_select_range'],


    // If there is only one identifier, without package scope, consider it a hierarchical identifier with one level of nesting
    //
    //   module_nonansi_header  'initial'  _identifier  •  '('  …
    //   1:  module_nonansi_header  'initial'  (hierarchical_identifier  _identifier)  •  '('  …  (precedence: 'hierarchical_identifier')
    //   2:  module_nonansi_header  'initial'  (tf_call  _identifier  •  list_of_arguments)       (precedence: 'tf_call')
    ['hierarchical_identifier', 'tf_call'],


    // If there are no parenthesis prioritize the hierarchical identifier
    //
    //   'var'  _identifier  '='  hierarchical_identifier  •  ';'  …
    //   1:  'var'  _identifier  '='  (primary  hierarchical_identifier)  •  ';'  …  (precedence: 'primary')
    //   2:  'var'  _identifier  '='  (tf_call  hierarchical_identifier)  •  ';'  …  (precedence: 'tf_call')
    ['primary', 'tf_call'],
    //   'var'  _identifier  '='  hierarchical_identifier  •  '++'  …
    //   1:  'var'  _identifier  '='  (tf_call  hierarchical_identifier  •  list_of_arguments)  (precedence: 'tf_call')
    //   2:  'var'  _identifier  '='  (variable_lvalue  hierarchical_identifier)  •  '++'  …    (precedence: 'variable_lvalue')
    ['variable_lvalue', 'tf_call'],


    // Do not allow calling functions inside brackets (maybe only system functions like $sizeof)
    // INFO: This one generalizes one that appeared above!
    //
    //   module_nonansi_header  'initial'  hierarchical_identifier  '['  _identifier  •  '/'  …
    //   1:  module_nonansi_header  'initial'  hierarchical_identifier  '['  (constant_primary  _identifier)  •  '/'  …         (precedence: 'ps_parameter_identifier')
    //   2:  module_nonansi_header  'initial'  hierarchical_identifier  '['  (hierarchical_identifier  _identifier)  •  '/'  …  (precedence: 'hierarchical_identifier')
    //   3:  module_nonansi_header  'initial'  hierarchical_identifier  '['  (tf_call  _identifier)  •  '/'  …                  (precedence: 'tf_call')
    // ['ps_parameter_identifier', 'hierarchical_identifier', 'tf_call'],

    //   module_nonansi_header  'initial'  _identifier  '.'  •  simple_identifier  …
    //   1:  module_nonansi_header  'initial'  (hierarchical_identifier_repeat1  _identifier  '.')  •  simple_identifier  …                            (precedence: 'hierarchical_identifier')
    //   2:  module_nonansi_header  'initial'  _identifier  (list_of_arguments  '.'  •  _identifier  '('  ')'  list_of_arguments_repeat3)              (precedence: 'list_of_arguments')
    //   3:  module_nonansi_header  'initial'  _identifier  (list_of_arguments  '.'  •  _identifier  '('  ')')                                         (precedence: 'list_of_arguments')
    //   4:  module_nonansi_header  'initial'  _identifier  (list_of_arguments  '.'  •  _identifier  '('  expression  ')'  list_of_arguments_repeat3)  (precedence: 'list_of_arguments')
    //   5:  module_nonansi_header  'initial'  _identifier  (list_of_arguments  '.'  •  _identifier  '('  expression  ')')                             (precedence: 'list_of_arguments')
    // ['hierarchical_identifier', 'list_of_arguments'],


    // If it's inside a class, consider it a class_item_qualifier since it seems more generic
    //
    //   'class'  _identifier  ';'  'static'  •  'string'  …
    //   1:  'class'  _identifier  ';'  (class_item_qualifier  'static')  •  'string'  …  (precedence: 'class_item_qualifier')
    //   2:  'class'  _identifier  ';'  (lifetime  'static')  •  'string'  …              (precedence: 'lifetime')
    ['class_item_qualifier', 'lifetime'],


    // Consider the super.new after declaration as part of the declaration and not as a statement:
    //
    // 'function'  'new'  ';'  'super'  •  '.'  …
    // 1:  'function'  'new'  ';'  (implicit_class_handle  'super')  •  '.'  …                                                                                                                  (precedence: 'implicit_class_handle')
    // 2:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  '('  list_of_arguments  ')'  ';'  'endfunction'  ':'  'new')                                         (precedence: 'class_constructor_declaration')
    // 3:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  '('  list_of_arguments  ')'  ';'  'endfunction')                                                     (precedence: 'class_constructor_declaration')
    // 4:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  '('  list_of_arguments  ')'  ';'  class_constructor_declaration_repeat2  'endfunction'  ':'  'new')  (precedence: 'class_constructor_declaration')
    // 5:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  '('  list_of_arguments  ')'  ';'  class_constructor_declaration_repeat2  'endfunction')              (precedence: 'class_constructor_declaration')
    // 6:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  ';'  'endfunction'  ':'  'new')                                                                      (precedence: 'class_constructor_declaration')
    // 7:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  ';'  'endfunction')                                                                                  (precedence: 'class_constructor_declaration')
    // 8:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  ';'  class_constructor_declaration_repeat2  'endfunction'  ':'  'new')                               (precedence: 'class_constructor_declaration')
    // 9:  (class_constructor_declaration  'function'  'new'  ';'  'super'  •  '.'  'new'  ';'  class_constructor_declaration_repeat2  'endfunction')                                           (precedence: 'class_constructor_declaration')
    ['class_constructor_declaration', 'implicit_class_handle'],


    // Since it comes after a class declaration, consider it a class property
    //
    //   'class'  _identifier  ';'  'const'  data_type  •  simple_identifier  …
    //   1:  'class'  _identifier  ';'  'const'  (data_type_or_implicit1  data_type)  •  simple_identifier  …                     (precedence: 'data_type_or_implicit1')
    //   2:  'class'  _identifier  ';'  (class_property  'const'  data_type  •  const_identifier  ';')                            (precedence: 'class_property')
    //   3:  'class'  _identifier  ';'  (class_property  'const'  data_type  •  const_identifier  '='  constant_expression  ';')  (precedence: 'class_property')
    ['class_property', 'data_type_or_implicit1'],


    // pure virtual function will always be a function prototype overriden in the extended class
    //
    // 'class'  _identifier  ';'  'pure'  'virtual'  •  'function'  …
    // 1:  'class'  _identifier  ';'  (class_method  'pure'  'virtual'  •  _method_prototype  ';')
    // 2:  'class'  _identifier  ';'  (method_qualifier  'pure'  'virtual')  •  'function'  …
    ['class_method', 'method_qualifier'],


    // 'typedef'  incomplete_class_scoped_type  •  '\'  …
    // 1:  'typedef'  (data_type_or_incomplete_class_scoped_type  incomplete_class_scoped_type)  •  '\'  …
    // 2:  'typedef'  (incomplete_class_scoped_type  incomplete_class_scoped_type)  •  '\'  …
    ['data_type_or_incomplete_class_scoped_type', 'incomplete_class_scoped_type'],


    // With struct array initializations:
    // Consider higher priority a structure pattern even though it could be an assignment to an array,
    // but the parser cannot know that...
    //
    //   ''{'  assignment_pattern_key  •  ':'  …
    //   1:  ''{'  (_array_pattern_key  assignment_pattern_key)  •  ':'  …
    //   2:  ''{'  (_structure_pattern_key  assignment_pattern_key)  •  ':'  …
    ['_structure_pattern_key', '_array_pattern_key'],


    // In this case, set this order to simplify precedences that yield the same result
    //   ''{'  _identifier  •  ':'  …
    //   1:  ''{'  (_simple_type  _identifier)  •  ':'  …
    //   2:  ''{'  (_simple_type  _identifier)  •  ':'  …            (precedence: 'ps_parameter_identifier')
    //   3:  ''{'  (_structure_pattern_key  _identifier)  •  ':'  …  (precedence: '_structure_pattern_key')
    //   4:  ''{'  (constant_primary  _identifier)  •  ':'  …        (precedence: 'ps_parameter_identifier')
    //
    // ''{'  class_scope  _identifier  •  ':'  …
    // 1:  ''{'  (_simple_type  class_scope  _identifier)  •  ':'  …
    // 2:  ''{'  (_simple_type  class_scope  _identifier)  •  ':'  …      (precedence: 'ps_parameter_identifier')
    // 3:  ''{'  (constant_primary  class_scope  _identifier)  •  ':'  …  (precedence: 'ps_parameter_identifier')
    ['ps_parameter_identifier', 'ps_type_identifier', '_structure_pattern_key'],


    // Cast in primary related conflicts
    //
    //   _module_header1  '('  '.'  _identifier  '('  '{'  _identifier  constant_select1  •  ','  …
    //   1:  _module_header1  '('  '.'  _identifier  '('  '{'  (constant_primary  _identifier  constant_select1)  •  ','  …  (precedence: 'constant_primary')
    //   2:  _module_header1  '('  '.'  _identifier  '('  '{'  (port_reference  _identifier  constant_select1)  •  ','  …    (precedence: 'port_reference')
    ['port_reference', 'constant_primary'],


    // 'nettype'  _identifier  •  '\'  …
    // 1:  'nettype'  (data_type  _identifier)  •  '\'  …                      (precedence: 'data_type')
    // 2:  (nettype_declaration  'nettype'  _identifier  •  _identifier  ';')
    ['nettype_declaration', 'data_type'],


    // On action block, else must be related to it
    //
    //   'wait_order'  '('  hierarchical_identifier  ')'  'wait_order'  '('  hierarchical_identifier  ')'  statement  •  'else'  …
    //   1:  'wait_order'  '('  hierarchical_identifier  ')'  'wait_order'  '('  hierarchical_identifier  ')'  (action_block  statement  •  'else'  statement_or_null)  (precedence: 'action_block')
    //   2:  'wait_order'  '('  hierarchical_identifier  ')'  'wait_order'  '('  hierarchical_identifier  ')'  (statement_or_null  statement)  •  'else'  …             (precedence: 'statement_or_null')
    ['action_block', 'statement_or_null'],


    // Conflict exclusive to sequence declarations:
    //
    //   'sequence'  _sequence_identifier  '('  _identifier  '='  '$'  •  ')'  …
    //   1:  'sequence'  _sequence_identifier  '('  _identifier  '='  (_sequence_actual_arg  '$')  •  ')'  …
    //   2:  'sequence'  _sequence_identifier  '('  _identifier  '='  (primary  '$')  •  ')'  …               (precedence: 'primary')
    ['_sequence_actual_arg', 'primary'],
    ['_sequence_actual_arg', 'event_expression'],


    // 'sequence'  _sequence_identifier  ';'  '##'  '['  constant_expression  ':'  '$'  •  ']'  …
    // 1:  'sequence'  _sequence_identifier  ';'  '##'  '['  (cycle_delay_const_range_expression  constant_expression  ':'  '$')  •  ']'  …  (precedence: 'cycle_delay_const_range_expression')
    // 2:  'sequence'  _sequence_identifier  ';'  '##'  '['  constant_expression  ':'  (constant_primary  '$')  •  ']'  …                    (precedence: 'constant_primary')
    ['cycle_delay_const_range_expression', 'constant_primary'],


    // After adding $root as a primary
    // '$root'  •  '.'  …
    // 1:  (hierarchical_identifier  '$root'  •  '.'  _identifier)                                   (precedence: 'hierarchical_identifier')
    // 2:  (hierarchical_identifier  '$root'  •  '.'  hierarchical_identifier_repeat1  _identifier)  (precedence: 'hierarchical_identifier')
    // 3:  (primary  '$root')  •  '.'  …                                                             (precedence: 'primary')
    ['hierarchical_identifier', 'primary'],


    //   module_nonansi_header  'generate'  _module_common_item  •  'resetall_compiler_directive_token1'  …
    //   1:  module_nonansi_header  'generate'  (interface_or_generate_item  _module_common_item)  •  'resetall_compiler_directive_token1'  …
    //   2:  module_nonansi_header  'generate'  (module_or_generate_item  _module_common_item)  •  'resetall_compiler_directive_token1'  …
    ['module_or_generate_item', 'interface_or_generate_item'],


    // text_macro_usage  •  'resetall_compiler_directive_token1'  …
    // 1:  (_directives  text_macro_usage)  •  'resetall_compiler_directive_token1'  …
    // 2:  (statement_item  text_macro_usage)  •  'resetall_compiler_directive_token1'  …
    ['statement_item', '_directives'],


    // module_nonansi_header  timeunits_declaration  •  'resetall_compiler_directive_token1'  …
    // 1:  (module_declaration  module_nonansi_header  timeunits_declaration  •  module_declaration_repeat1  'endmodule'  ':'  module_identifier)  (precedence: 'module_declaration')
    // 2:  (module_declaration  module_nonansi_header  timeunits_declaration  •  module_declaration_repeat1  'endmodule')                           (precedence: 'module_declaration')
    // 3:  module_nonansi_header  (_non_port_module_item  timeunits_declaration)  •  'resetall_compiler_directive_token1'  …                        (precedence: '_non_port_module_item')
    ['module_declaration', '_non_port_module_item'],


    // 'randomize'  'with'  '{'  expression  '–>'  '{'  '}'  •  '+'  …
    // 1:  'randomize'  'with'  '{'  expression  '–>'  (constraint_set  '{'  '}')  •  '+'  …
    // 2:  'randomize'  'with'  '{'  expression  '–>'  (empty_unpacked_array_concatenation  '{'  '}')  •  '+'  …
    ['constraint_set', 'empty_unpacked_array_concatenation'],


    // INFO: After adding text_macro support for hierarchical identifiers
    // text_macro_usage  •  '['  …
    // 1:  (_directives  text_macro_usage)  •  '['  …                                         (precedence: '_directives')
    // 2:  (hierarchical_identifier_repeat1  text_macro_usage  •  constant_bit_select1  '.')  (precedence: 'hierarchical_identifier')
    ['hierarchical_identifier', '_directives'],
    ['_method_call_root', '_directives'],


    // severity_system_task  •  'resetall_compiler_directive_token1'  …
    // 1:  (_module_common_item  severity_system_task)  •  'resetall_compiler_directive_token1'  …        (precedence: '_module_common_item')
    // 2:  (subroutine_call_statement  severity_system_task)  •  'resetall_compiler_directive_token1'  …
    ['subroutine_call_statement', '_module_common_item'],


    // Make checkers less important
    ['hierarchical_instance', 'checker_instantiation'],
    ['module_instantiation', 'concurrent_assertion_item'],

    // Real conflict after adding the $ as a constant_primary, needed to index queues (e.g. a[0:$-1])
    //
    // 'input'  _identifier  '['  '$'  •  ':'  …
    // 1:  'input'  _identifier  '['  (constant_primary  '$')  •  ':'  …                        (precedence: 'constant_primary')
    // 2:  'input'  _identifier  (queue_dimension  '['  '$'  •  ':'  constant_expression  ']')
    ['queue_dimension', 'constant_primary'],


    ///////////////////////////////////////////////////
    ///////////////////////////////////////////////////
    ['net_port_header1'],
    ['variable_port_header'],
    ['net_declaration'],
    ['module_instantiation'],
    ['tf_call'],
    ['list_of_arguments'],
    ['lifetime'],
    ['class_item_qualifier'],
    ['class_constructor_declaration'],
    ['implicit_class_handle'],
    ['class_property'],
    ['_method_call_root'],
    ['class_type'],
    ['package_scope'],
    ['_description'],
    ['statement'],
    ['_simple_type'],
    ['ps_type_identifier'],
    ['cast'],
    ['casting_type'],
    ['constant_primary'],
    ['_constant_assignment_pattern_expression'],
    ['nettype_declaration'],
    ['param_expression'],
    ['value_range'],
    ['action_block'],
    ['cycle_delay_const_range_expression'],
    ['_sequence_actual_arg'],
    ['expression_or_dist'],
    ['text_macro_usage'],
    ['constant_select1'],
    ['select1'],

    ['module_declaration'],
    ['checker_instantiation'],
    ['program_instantiation'],
    ['interface_instantiation'],
    ['hierarchical_instance'],
    ['concurrent_assertion_item'],
    ['interface_port_declaration'],

    ['port'],
    ///////////////////////////////////////////////////
    ///////////////////////////////////////////////////
  ],

// ** Conflicts
  conflicts: $ => [
    // Help differentiate between many parameters and list of parameters:
    //
    //   module_keyword  module_identifier  '#'  '('  param_assignment  •  ','  …
    //   1:  module_keyword  module_identifier  '#'  '('  (list_of_param_assignments  param_assignment  •  list_of_param_assignments_repeat1)
    //   2:  module_keyword  module_identifier  '#'  '('  (list_of_param_assignments  param_assignment)  •  ','  …
    [$.list_of_param_assignments],


    // Help differentiate between many types and list of types:
    //
    //   module_keyword  module_identifier  '#'  '('  'type'  type_assignment  •  ','  …
    //   1:  module_keyword  module_identifier  '#'  '('  'type'  (list_of_type_assignments  type_assignment  •  list_of_type_assignments_repeat1)
    //   2:  module_keyword  module_identifier  '#'  '('  'type'  (list_of_type_assignments  type_assignment)  •  ','  …
    [$.list_of_type_assignments],


    // Differentiate between nonANSI/ANSI header for empty port list with parenthesis:
    //
    //   module_keyword  module_identifier  '('  ')'  •  ';'  …
    //     1:  module_keyword  module_identifier  (list_of_port_declarations  '('  ')')  •  ';'  …
    //     2:  module_keyword  module_identifier  (list_of_ports  '('  ')')  •  ';'  …
    [$.list_of_ports, $.list_of_port_declarations],


    // This one had no option if setting right associativity on conditional_statement to handle recursion
    //
    //   module_nonansi_header  'initial'  'if'  '('  cond_predicate  ')'  statement_or_null  'else'  'if'  '('  cond_predicate  ')'  statement_or_null  •  'endmodule'  …
    //     1:  module_nonansi_header  'initial'  'if'  '('  cond_predicate  ')'  statement_or_null  'else'  (conditional_statement  'if'  '('  cond_predicate  ')'  statement_or_null)  •  'endmodule'  …          (precedence: 0, associativity: Right)
    //     2:  module_nonansi_header  'initial'  'if'  '('  cond_predicate  ')'  statement_or_null  (conditional_statement_repeat1  'else'  'if'  '('  cond_predicate  ')'  statement_or_null)  •  'endmodule'  …
    [$.conditional_statement],


    // This is a real conflict, since it needs more lookeahead to distinguish between a hierarchical identifier
    // and a select1 construct, that might have some members with non-constant expressions
    //
    //   module_nonansi_header  'initial'  _identifier  •  '.'  …
    //   1:  module_nonansi_header  'initial'  (hierarchical_identifier  _identifier)  •  '.'  …       (precedence: 'hierarchical_identifier')
    //   2:  module_nonansi_header  'initial'  (hierarchical_identifier_repeat1  _identifier  •  '.')  (precedence: 'hierarchical_identifier')
    [$.hierarchical_identifier],


    // SystemVerilog allows continuous assignment both to nets and logic variables:
    //
    // module_nonansi_header  'assign'  hierarchical_identifier  •  '.'  …
    // 1:  module_nonansi_header  'assign'  (ps_or_hierarchical_net_identifier  hierarchical_identifier)  •  '.'  …
    // 2:  module_nonansi_header  'assign'  (variable_lvalue  hierarchical_identifier  •  select1)
    [$.variable_lvalue, $.ps_or_hierarchical_net_identifier],


    // This one doesn't seem very important, since it should only refer to identifiers
    // when hierarchical only have 1 level of nesting
    //
    //   module_nonansi_header  'assign'  _identifier  •  '.'  …
    //     1:  module_nonansi_header  'assign'  (hierarchical_identifier  _identifier)  •  '.'  …            (precedence: 'hierarchical_identifier')
    //     2:  module_nonansi_header  'assign'  (hierarchical_identifier_repeat1  _identifier  •  '.')       (precedence: 'hierarchical_identifier')
    //     3:  module_nonansi_header  'assign'  (ps_or_hierarchical_net_identifier  _identifier)  •  '.'  …
    [$.hierarchical_identifier, $.ps_or_hierarchical_net_identifier],


    // No way to fix this conflict in the precedences array since the constant_expression has numeric precedence,
    // and the pattern one has a string precedence. It should occur rarely in the language.
    //
    // module_nonansi_header  'var'  _identifier  '='  expression  'matches'  constant_expression  •  '?'  …
    // 1:  module_nonansi_header  'var'  _identifier  '='  expression  'matches'  (constant_expression  constant_expression  •  '?'  constant_expression  ':'  constant_expression)                              (precedence: 23, associativity: Right)
    // 2:  module_nonansi_header  'var'  _identifier  '='  expression  'matches'  (constant_expression  constant_expression  •  '?'  module_declaration_repeat3  constant_expression  ':'  constant_expression)  (precedence: 23, associativity: Right)
    // 3:  module_nonansi_header  'var'  _identifier  '='  expression  'matches'  (pattern  constant_expression)  •  '?'  …                                                                                      (precedence: 'pattern')
    [$.pattern, $.constant_expression],


    // Don't really understand this one well but it's a consequence of having PREC.CONDITIONAL on both
    // $.cond_predicate and $.conditional_expression, and seems needed to make nested conditional expressions work well
    //
    //   module_nonansi_header  'var'  _identifier  '='  cond_predicate  '?'  expression  ':'  expression  •  '?'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  (conditional_expression  cond_predicate  '?'  expression  ':'  expression)  •  '?'  …  (precedence: 23, associativity: Right)
    //   2:  module_nonansi_header  'var'  _identifier  '='  cond_predicate  '?'  expression  ':'  (cond_predicate  expression)  •  '?'  …          (precedence: 23)
    [$.cond_predicate, $.conditional_expression],


    //  Declaration of net/type in the unit scope, true conflict
    //
    //   _identifier  •  simple_identifier  …
    //   1:  (data_type  _identifier)  •  simple_identifier  …
    //   2:  (net_declaration  _identifier  •  list_of_net_decl_assignments  ';')
    // [$.net_declaration, $.data_type],


    // Setting prec.left prevented having more than 1 bit_select dimension:
    //
    // module_nonansi_header  'var'  _identifier  '='  hierarchical_identifier  bit_select1_repeat1  •  '['  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  hierarchical_identifier  (bit_select1  bit_select1_repeat1)  •  '['  …
    //   2:  module_nonansi_header  'var'  _identifier  '='  hierarchical_identifier  (bit_select1_repeat1  bit_select1_repeat1  •  bit_select1_repeat1)
    [$.bit_select1],
    // Same case below
    //
    //   '['  _identifier  constant_bit_select1_repeat1  •  '['  …
    //   1:  '['  _identifier  (constant_bit_select1  constant_bit_select1_repeat1)  •  '['  …
    //   2:  '['  _identifier  (constant_bit_select1_repeat1  constant_bit_select1_repeat1  •  constant_bit_select1_repeat1)
    [$.constant_bit_select1],


    // Parser needs more information to know which of these possibiliies is the correct one:
    //   1) Variable (or user defined) type declaration
    //   2, 3) Module instantiation
    //   4) User defined nettype assignments (less likely) but still possible
    // INFO: This one is settled with dynamic precedences for data_type vs net_declaration
    //
    //   module_nonansi_header  _identifier  •  simple_identifier  …
    //     1:  module_nonansi_header  (data_type  _identifier)  •  simple_identifier  …                                                 (precedence: 'data_type')
    //     2:  module_nonansi_header  (module_instantiation  _identifier  •  hierarchical_instance  ';')                                (precedence: 'module_instantiation')
    //     3:  module_nonansi_header  (module_instantiation  _identifier  •  hierarchical_instance  module_instantiation_repeat1  ';')  (precedence: 'module_instantiation')
    //     4:  module_nonansi_header  (net_declaration  _identifier  •  list_of_net_decl_assignments  ';')                              (precedence: 'net_declaration')
    // [$.net_declaration, $.data_type, $.module_instantiation],


    // This is derived from the LRM:
    // In a data_declaration, it shall be illegal to omit the explicit data_type
    // before a list_of_variable_decl_assignments unless the var keyword is used.
    //
    //   _module_header1  '('  'var'  •  simple_identifier  …
    //   1:  _module_header1  '('  (_var_data_type  'var'  •  data_type_or_implicit1)  (precedence: '_var_data_type')
    //   2:  _module_header1  '('  (_var_data_type  'var')  •  simple_identifier  …    (precedence: '_var_data_type')
    [$._var_data_type],


    // Examples:
    //   input my_custom_nettype_identifier ... my_signal (user defined net)
    //   input my_signal ... (net)
    //   input my_type_t ... my_signal (variable)
    //
    // Even though we do not aim to support user defined nets (example 1), there is a conflict between examples 2 and 3
    //
    //   _module_header1  '('  port_direction  •  simple_identifier  …
    //   1:  _module_header1  '('  (net_port_header1  port_direction  •  net_port_type1)           (precedence: 'net_port_header1')
    //   2:  _module_header1  '('  (net_port_header1  port_direction)  •  simple_identifier  …     (precedence: 'net_port_header1')
    //   3:  _module_header1  '('  (variable_port_header  port_direction  •  _variable_port_type)  (precedence: 'variable_port_header')
    [$.net_port_header1, $.variable_port_header],


    // It seems the more general option 1 would be the correct, but adding associativity would probably cause some
    // errors in the parsing of some file, so set as a conflict to increase lookahead 1 token
    //
    //   _module_header1  '('  net_type  •  simple_identifier  …
    //   1:  _module_header1  '('  (net_port_type1  net_type  •  data_type_or_implicit1)  (precedence: 'net_port_type1')
    //   2:  _module_header1  '('  (net_port_type1  net_type)  •  simple_identifier  …    (precedence: 'net_port_type1')
    [$.net_port_type1],


    // This is not that obvious, and seems better to create a conflict since bit_select and brackets are involved
    //
    //   'function'  function_identifier  ';'  _identifier  •  '['  …
    //   1:  'function'  function_identifier  ';'  (data_type  _identifier  •  data_type_repeat1)                                (precedence: 'data_type')
    //   2:  'function'  function_identifier  ';'  (hierarchical_identifier  _identifier)  •  '['  …                             (precedence: 'hierarchical_identifier')
    //   3:  'function'  function_identifier  ';'  (hierarchical_identifier_repeat1  _identifier  •  constant_bit_select1  '.')  (precedence: 'hierarchical_identifier')
    [$.data_type, $.hierarchical_identifier],


    // INFO: Even though localparams set only constants for vector types, and it would need to be packed,
    // specify a conflict for some other potential cases where the parser cannot differentiate between these two
    //
    //   'localparam'  _identifier  '['  constant_range  ']'  •  '['  …
    //   1:  'localparam'  _identifier  (packed_dimension  '['  constant_range  ']')  •  '['  …    (precedence: 'packed_dimension')
    //   2:  'localparam'  _identifier  (unpacked_dimension  '['  constant_range  ']')  •  '['  …  (precedence: 'unpacked_dimension')
    [$.unpacked_dimension, $.packed_dimension],


    // Avoid adding right associativity in data_type so that it can differentiate between data_types/net_types
    //
    //   'function'  function_identifier  '('  class_scope  _identifier  •  '['  …
    //   1:  'function'  function_identifier  '('  (data_type  class_scope  _identifier  •  data_type_repeat1)  (precedence: 'data_type')
    //   2:  'function'  function_identifier  '('  (data_type  class_scope  _identifier)  •  '['  …             (precedence: 'data_type')
    [$.data_type],


    // case inside does not accept casex/casez expressions
    //
    // module_nonansi_header  'initial'  'case'  •  '('  …
    // 1:  module_nonansi_header  'initial'  (case_keyword  'case')  •  '('  …
    // 2:  module_nonansi_header  'initial'  (case_statement  'case'  •  '('  case_expression  ')'  'inside'  case_statement_repeat3  'endcase')
    [$.case_statement, $.case_keyword],


    // 2nd option is for the case when there is a clocking event, so it needs to check further.
    //
    //   module_nonansi_header  'initial'  system_tf_identifier  '('  expression  •  ')'  …
    //   1:  module_nonansi_header  'initial'  (system_tf_call  system_tf_identifier  '('  expression  •  ')')
    //   2:  module_nonansi_header  'initial'  system_tf_identifier  '('  (list_of_arguments  expression)  •  ')'  …
    [$.system_tf_call, $.list_of_arguments],


    // This one is required and adds up to another one existing before without the tf_call
    //
    //   _identifier  '#'  '('  package_scope  _identifier  •  ')'  …
    //   1:  _identifier  '#'  '('  (data_type  package_scope  _identifier)  •  ')'  …                (precedence: 'data_type')
    //   2:  _identifier  '#'  '('  (tf_call  package_scope  _identifier)  •  ')'  …                  (precedence: 'tf_call')
    //   3:  _identifier  '#'  '('  package_scope  (hierarchical_identifier  _identifier)  •  ')'  …  (precedence: 'hierarchical_identifier')
    // ['data_type', 'hierarchical_identifier', 'tf_call'],
    // [$.data_type, $.tf_call, $.hierarchical_identifier],


    // It's not possible to know after 'local static' (e.g) if it's a property or a method:
    //
    //   'class'  _identifier  ';'  class_item_qualifier  •  'static'  …
    //   1:  'class'  _identifier  ';'  (_property_qualifier  class_item_qualifier)  •  'static'  …
    //   2:  'class'  _identifier  ';'  (method_qualifier  class_item_qualifier)  •  'static'  …
    [$._property_qualifier, $.method_qualifier],


    // Implicit can be both options depending on the context. Tried with right associativity but didn't work well.
    //
    //   module_nonansi_header  'initial'  'this'  •  '.'  …
    //   1:  module_nonansi_header  'initial'  (implicit_class_handle  'this'  •  '.'  'super')  (precedence: 'implicit_class_handle')
    //   2:  module_nonansi_header  'initial'  (implicit_class_handle  'this')  •  '.'  …        (precedence: 'implicit_class_handle')
    [$.implicit_class_handle],


    // Assumes that since this comes from statement_item, it could be in many places and therefore
    // it's a better idea to set a conflict (it could be inside a forever block inside a class for a method_call_root)
    //
    //   module_nonansi_header  'initial'  implicit_class_handle  •  '.'  …
    //   1:  module_nonansi_header  'initial'  (_method_call_root  implicit_class_handle)  •  '.'  …                                         (precedence: '_method_call_root')
    //   2:  module_nonansi_header  'initial'  (class_qualifier  implicit_class_handle  •  '.')                                              (precedence: 'class_qualifier')
    //   3:  module_nonansi_header  'initial'  (variable_lvalue  implicit_class_handle  •  '.'  _hierarchical_variable_identifier  select1)  (precedence: 'variable_lvalue')
    //   4:  module_nonansi_header  'initial'  (variable_lvalue  implicit_class_handle  •  '.'  _hierarchical_variable_identifier)           (precedence: 'variable_lvalue')
    [$._method_call_root, $.class_qualifier, $.variable_lvalue],


    // Same as before, this case could be all the options inside the initial, need more lookahead
    //
    // module_nonansi_header  'initial'  hierarchical_identifier  •  '.'  …
    // 1:  module_nonansi_header  'initial'  (primary  hierarchical_identifier  •  select1)          (precedence: 'primary')
    // 2:  module_nonansi_header  'initial'  (primary  hierarchical_identifier)  •  '.'  …           (precedence: 'primary')
    // 3:  module_nonansi_header  'initial'  (tf_call  hierarchical_identifier)  •  '.'  …           (precedence: 'tf_call')
    // 4:  module_nonansi_header  'initial'  (variable_lvalue  hierarchical_identifier  •  select1)  (precedence: 'variable_lvalue')
    [$.tf_call, $.primary, $.variable_lvalue],


    // All of these also seemed needed after implementing method calls, external methods and static methods
    [$.tf_call, $.hierarchical_identifier],
    [$.primary],
    [$.primary, $.variable_lvalue],
    [$._method_call_root, $.class_qualifier],
    [$.tf_call, $.primary],
    [$.method_call_body, $.array_method_name],
    [$.select1],


    // Need to set these to allow correct parsing of external methods and static methods
    //
    // module_nonansi_header  'var'  _identifier  '='  _identifier  parameter_value_assignment  •  '::'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  (class_type  _identifier  parameter_value_assignment  •  class_type_repeat1)
    //   2:  module_nonansi_header  'var'  _identifier  '='  (class_type  _identifier  parameter_value_assignment)  •  '::'  …
    [$.class_type],
    // _identifier  •  '::'  …
    // 1:  (class_type  _identifier  •  class_type_repeat1)
    // 2:  (class_type  _identifier)  •  '::'  …
    // 3:  (package_scope  _identifier  •  '::')             (precedence: 'package_scope')
    [$.class_type, $.package_scope],


    // Directives conflicts
    [$.pragma_keyword, $._identifier],


    // TODO: Typedef conflicts
    // 'typedef'  _identifier  •  '::'  …
    // 1:  'typedef'  (class_type  _identifier  •  class_type_repeat1)                                     (precedence: 'class_type')
    // 2:  'typedef'  (class_type  _identifier)  •  '::'  …                                                (precedence: 'class_type')
    // 3:  'typedef'  (incomplete_class_scoped_type  _identifier  •  '::'  type_identifier_or_class_type)  (precedence: 'incomplete_class_scoped_type')
    // 4:  'typedef'  (package_scope  _identifier  •  '::')                                                (precedence: 'package_scope')
    [$.incomplete_class_scoped_type, $.class_type, $.package_scope],


    // In this case, _forward_type would refer to the type of declaration
    // that is done at the beginning of a file so that the enum is known to be declared
    // (e.g.what is done with classes on the UVM)
    //
    // 'typedef'  'enum'  •  '\'  …
    // 1:  'typedef'  (_forward_type  'enum')  •  '\'  …
    // 2:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  '}'  data_type_repeat1)                     (precedence: 'data_type')
    // 3:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  '}')                                        (precedence: 'data_type')
    // 4:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  data_type_repeat3  '}'  data_type_repeat1)  (precedence: 'data_type')
    // 5:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  data_type_repeat3  '}')                     (precedence: 'data_type')
    [$._forward_type, $.data_type],


    // interface_port_identifier would be of the form:
    //  typedef if_port_id[5].member my_type_t (not sure if it's correct syntax)
    // While the data_type branch could end with a _variable_dimension
    //
    // 'typedef'  _identifier  •  '['  …
    // 1:  'typedef'  (data_type  _identifier  •  data_type_repeat1)       (precedence: 'data_type')
    // 2:  'typedef'  (interface_port_identifier  _identifier)  •  '['  …
    [$.data_type, $.interface_port_identifier],


    // 'typedef'  _identifier  •  '\'  …
    // 1:  'typedef'  (class_type  _identifier)  •  '\'  …                     (precedence: 'class_type')
    // 2:  'typedef'  (data_type  _identifier)  •  '\'  …                      (precedence: 'data_type')
    // 3:  'typedef'  (type_identifier_or_class_type  _identifier)  •  '\'  …
    [$.type_identifier_or_class_type, $.data_type, $.class_type],


    // 'typedef'  package_scope  _identifier  •  '\'  …
    // 1:  'typedef'  (class_type  package_scope  _identifier)  •  '\'  …  (precedence: 'class_type')
    // 2:  'typedef'  (data_type  package_scope  _identifier)  •  '\'  …   (precedence: 'data_type')
    [$.data_type, $.class_type],


    // Seems that any could be valid. Also incomplete_class_scoped_type could be recursive
    // so more tokens of lookahead could help
    //
    // 'typedef'  _identifier  '::'  _identifier  •  '\'  …
    // 1:  'typedef'  _identifier  '::'  (class_type  _identifier)  •  '\'  …                     (precedence: 'class_type')
    // 2:  'typedef'  _identifier  '::'  (type_identifier_or_class_type  _identifier)  •  '\'  …
    // 3:  'typedef'  _identifier  (class_type_repeat1  '::'  _identifier)  •  '\'  …             (precedence: 'class_type')
    [$.type_identifier_or_class_type, $.class_type],


    // Casting
    [$._simple_type, $.constant_primary],
    [$._simple_type, $._structure_pattern_key, $.constant_primary],


    // Big conflict after inlining constant assignment pattern expression
    //
    // '('  expression  'matches'  ''{'  _identifier  •  ':'  …
    // 1:  '('  expression  'matches'  ''{'  (_simple_type  _identifier)  •  ':'  …                         (precedence: 'ps_parameter_identifier')
    // 2:  '('  expression  'matches'  ''{'  (_simple_type  _identifier)  •  ':'  …                         (precedence: 'ps_type_identifier')
    // 3:  '('  expression  'matches'  ''{'  (_structure_pattern_key  _identifier)  •  ':'  …               (precedence: '_structure_pattern_key')
    // 4:  '('  expression  'matches'  ''{'  (constant_primary  _identifier)  •  ':'  …                     (precedence: 'ps_parameter_identifier')
    // 5:  '('  expression  'matches'  (pattern  ''{'  _identifier  •  ':'  pattern  '}')                   (precedence: 'pattern')
    // 6:  '('  expression  'matches'  (pattern  ''{'  _identifier  •  ':'  pattern  pattern_repeat2  '}')  (precedence: 'pattern')
    [$._simple_type, $.pattern, $._structure_pattern_key, $.constant_primary],

    // Type-reference
    [$.data_type, $.class_type, $.tf_call, $.hierarchical_identifier],
    [$.data_type, $.constant_primary],
    [$.expression, $.constant_primary],
    [$.data_type, $.expression],

    // Queue dimensions
    [$.primary, $.implicit_class_handle],
    [$.param_expression, $.primary],
    [$.value_range, $.primary],
    [$.constant_param_expression, $.constant_primary],

    // Tagged union
    [$.tagged_union_expression],
    [$.pattern, $.tagged_union_expression],

    // Class_type as data_type
    [$.net_declaration, $.data_type, $.class_type],
    [$.type_identifier_or_class_type, $.data_type],
    [$.nettype_declaration, $.data_type, $.class_type],
    [$.net_declaration, $.data_type, $.class_type, $.module_instantiation],
    [$.interface_port_header, $.data_type, $.class_type, $.net_port_type1],
    [$.data_type, $.class_type, $.net_port_type1],
    [$.class_type, $.module_instantiation],
    [$.data_type, $.class_type, $.tf_port_item1],
    [$.data_type, $.class_type, $.constant_primary],

    [$.ansi_port_declaration],

    // Class new
    [$.list_of_arguments, $.mintypmax_expression],

    // Typed constructor
    [$.blocking_assignment, $.shallow_copy, $.hierarchical_identifier],
    [$.shallow_copy, $.tf_call, $.hierarchical_identifier],

    // Sequences
    [$.sequence_expr],
    [$._assignment_pattern_expression_type, $.constant_primary],
    [$.expression_or_dist, $.event_expression],

    // Net declaration delay
    //   _identifier  '#'  '('  mintypmax_expression  •  ')'  …
    //   1:  _identifier  '#'  '('  (param_expression  mintypmax_expression)  •  ')'  …  (precedence: 'param_expression')
    //   2:  _identifier  (delay_control  '#'  '('  mintypmax_expression  •  ')')
    [$.delay_control, $.param_expression],

    // delay3
    [$.randomize_call],
    [$.system_tf_call],
    [$._assignment_pattern_expression_type, $.expression],
    [$.expression, $.mintypmax_expression],
    [$.tf_call],
    [$.array_manipulation_call],
    [$.method_call_body],

    // Constant function call (13.4.3)
    [$.constant_function_call, $.primary],
    [$._simple_type, $._structure_pattern_key, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._simple_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._simple_type, $.tf_call, $.constant_primary],
    [$.concatenation, $.stream_expression],
    [$._simple_type, $.pattern, $._structure_pattern_key, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._assignment_pattern_expression_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._assignment_pattern_expression_type, $.tf_call, $.constant_primary],


    [$.constant_expression, $.expression],

    // Interface (TODO: don't understand these two below)
    [$.interface_declaration, $._non_port_interface_item],
    [$.timeunits_declaration],

    // Program (TODO: don't understand these two below)
    [$.program_declaration, $.non_port_program_item],


    // Inout/ref/interface ports
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type, $.module_instantiation],
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type],
    [$.list_of_interface_identifiers, $.net_decl_assignment],

    // Dynamic array new
    [$.variable_decl_assignment, $._variable_dimension],
    [$.variable_decl_assignment, $.packed_dimension, $._variable_dimension],

    [$._method_call_root, $.class_qualifier, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.variable_lvalue, $.nonrange_variable_lvalue],
    [$.tf_call, $.primary, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.select1, $.nonrange_select1],
    [$.primary, $.variable_lvalue, $.nonrange_variable_lvalue],


    [$.constant_primary, $.primary],


    // TODO: Remove!
    [$.select1, $.variable_lvalue],


    // INFO: Added to fix issue with expressions inside bit_select1
    [$.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.tf_call, $.constant_primary],
    [$.data_type, $.class_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.data_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.data_type, $.class_type, $.tf_call, $.constant_primary],
    [$._assignment_pattern_expression_type, $.hierarchical_identifier],
    [$._assignment_pattern_expression_type, $.tf_call, $.hierarchical_identifier],

    // Modports
    // INFO: Not sure about this...
    // interface_nonansi_header  'modport'  modport_identifier  '('  port_direction  modport_simple_port  •  ','  …
    // 1:  interface_nonansi_header  'modport'  modport_identifier  '('  (modport_simple_ports_declaration  port_direction  modport_simple_port  •  modport_simple_ports_declaration_repeat1)
    // 2:  interface_nonansi_header  'modport'  modport_identifier  '('  (modport_simple_ports_declaration  port_direction  modport_simple_port)  •  ','  …
    [$.modport_simple_ports_declaration],
    [$.modport_tf_ports_declaration],


    // Support for static method calls
    [$.class_type, $.tf_call, $.hierarchical_identifier, $.package_scope],
    [$.class_type, $.tf_call, $.hierarchical_identifier],
    [$.incomplete_class_scoped_type, $.class_type, $.tf_call, $.hierarchical_identifier, $.package_scope],
    [$.class_scope, $._method_call_root],
    [$.class_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],


    // Needed to parse standalone module_items (snippets)
    [$.interface_port_declaration, $.class_type, $.tf_call, $.hierarchical_identifier],
    [$.list_of_variable_assignments, $.procedural_continuous_assignment],
    [$.interface_port_declaration, $.hierarchical_identifier],

    // Conditional generate
    // 'case'  •  '('  …
    // 1:  (case_generate_construct  'case'  •  '('  constant_expression  ')'  case_generate_item  'endcase')
    // 2:  (case_generate_construct  'case'  •  '('  constant_expression  ')'  case_generate_item  case_generate_construct_repeat1  'endcase')
    // 3:  (case_keyword  'case')  •  '('  …
    // 4:  (case_statement  'case'  •  '('  case_expression  ')'  'inside'  case_statement_repeat3  'endcase')
    [$.case_generate_construct, $.case_statement, $.case_keyword],

    // Loop generate (true conflict)
    // 'for'  '('  _identifier  •  '='  …
    // 1:  'for'  '('  (genvar_initialization  _identifier  •  '='  constant_expression)
    // 2:  'for'  '('  (hierarchical_identifier  _identifier)  •  '='  …                  (precedence: 'hierarchical_identifier')
    [$.genvar_initialization, $.hierarchical_identifier],


    // After adding support for directives in packages,
    [$.interface_or_generate_item, $.package_or_generate_item_declaration],
    [$._description, $._non_port_module_item, $.package_or_generate_item_declaration, $.statement_item],

    // After adding text_macro_usage to _method_call_root
    [$._directives, $._method_call_root],


    // Fix error with method call with bit_select
    [$.class_qualifier, $.select1],
    [$.select1, $.hierarchical_identifier],
    [$.constant_select1, $.hierarchical_identifier],
    [$._method_call_root, $.primary, $.class_qualifier, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$._method_call_root, $.primary],
    [$._method_call_root, $.primary, $.class_qualifier, $.variable_lvalue],
    [$._method_call_root, $.primary, $.class_qualifier],

    // Constraints
    [$.class_method, $.constraint_prototype_qualifier],

    // DPI
    // 'import'  dpi_spec_string  'context'  •  c_identifier  …
    // 1:  'import'  dpi_spec_string  (dpi_function_import_property  'context')  •  c_identifier  …
    // 2:  'import'  dpi_spec_string  (dpi_task_import_property  'context')  •  c_identifier  …
    [$.dpi_function_import_property, $.dpi_task_import_property],


    // Text macros on hierarchical identifiers
    // INFO: Seems that after this, hierarchical_identifier has a higher dynamic precedence over _method_call_root
    [$._method_call_root, $.hierarchical_identifier],
    [$._directives, $._method_call_root, $.hierarchical_identifier],


    // Coverage: TODO
    [$._cross_item],
    [$.hierarchical_identifier, $.method_identifier],
    [$._covergroup_expression, $.cond_pattern],
    [$._covergroup_expression, $.mintypmax_expression],
    [$._covergroup_expression, $.concatenation],
    [$.covergroup_value_range, $.primary],
    [$.bins_expression],
    [$._integer_covergroup_expression, $.primary],


    // TODO: sequences/properties/assertions
    [$.concurrent_assertion_item, $.deferred_immediate_assertion_item, $.generate_block_identifier],
    [$.expression_or_dist, $.mintypmax_expression],
    [$.property_expr, $.sequence_expr],
    [$.cover_sequence_statement, $.sequence_expr],
    [$.property_spec, $.property_expr],
    [$.property_expr, $._sequence_actual_arg],
    [$.expression_or_dist, $.event_expression, $.mintypmax_expression],

    [$.tf_call, $.ps_or_hierarchical_property_identifier],
    [$.tf_call, $.primary, $.ps_or_hierarchical_property_identifier],
    [$.tf_call, $.hierarchical_identifier, $.ps_or_hierarchical_property_identifier],
    [$.property_list_of_arguments, $.expression_or_dist, $.event_expression],

    [$.tf_call, $.ps_or_hierarchical_property_identifier, $.ps_or_hierarchical_sequence_identifier],
    [$.tf_call, $.primary, $.ps_or_hierarchical_property_identifier, $.ps_or_hierarchical_sequence_identifier],
    [$.tf_call, $.primary, $.ps_or_hierarchical_sequence_identifier],
    [$.tf_call, $.hierarchical_identifier, $.ps_or_hierarchical_property_identifier, $._sequence_identifier],
    [$.tf_call, $.hierarchical_identifier, $._sequence_identifier],
    [$.tf_call, $.ps_or_hierarchical_sequence_identifier],
    [$.tf_call, $.ps_or_hierarchical_property_identifier, $._sequence_identifier],
    [$.tf_call, $._sequence_identifier],

    // TODO: Add procedural assertion item probably these could be removed by inlining
    [$.concurrent_assertion_item, $._procedural_assertion_statement],
    [$.deferred_immediate_assertion_item, $._immediate_assertion_statement],

    // TODO: Add clocking_drive to statement_item
    [$.clockvar, $.tf_call, $.primary, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.clockvar, $.primary, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.clockvar, $.variable_lvalue],

    // TODO: Fixing the local:: class_qualifier
    [$._simple_type, $._assignment_pattern_expression_type, $.class_qualifier],

    // TODO: Randsequence conflicts
    [$.rs_production_list],
    [$.rs_rule],

    // TODO: bind
    [$.bind_target_scope],
    [$.bind_target_scope, $.hierarchical_identifier],

    // INFO: These ones need to be here:
    // module_declaration conflict, needed to detect extern module overrides
    [$.module_declaration, $._module_header],
    [$.interface_declaration, $._interface_header],
    [$.program_declaration, $._program_header],

    // TODO: Adding branches on constant_primary
    [$.constant_primary],

    // TODO: After adding nested static class access on LHS
    [$._assignment_pattern_expression_type, $.class_qualifier],

    // TODO: Fixing constant_primary on casting_type
    [$.interface_port_declaration, $.class_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.tf_call, $.constant_primary, $.hierarchical_identifier, $.ps_or_hierarchical_property_identifier, $._sequence_identifier],
    [$.tf_call, $.constant_primary, $.hierarchical_identifier, $._sequence_identifier],
    [$.port_reference, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.select_expression, $.tf_call, $.constant_primary, $.hierarchical_identifier],


    // TODO: After adding checkers
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type, $.module_instantiation, $.checker_instantiation],
    [$.data_type, $.class_type, $.checker_instantiation],
    [$.named_port_connection, $.named_checker_port_connection],
    [$.expression_or_dist, $.ordered_port_connection, $.event_expression],
    [$.expression_or_dist, $.named_port_connection, $.event_expression],
  ],

});


