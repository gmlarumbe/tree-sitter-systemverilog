/* eslint-disable arrow-parens */
/* eslint-disable camelcase */
/* eslint-disable-next-line spaced-comment */
/* eslint-disable-no-undef */
/* eslint-disable-no-unused-vars */
/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

'use strict';

const PREC = {
  // Table 11-2—Operator precedence and associativity
  PARENTHESIS: 37,         // () [] :: .                                          Left
  UNARY: 36,               // + - ! ~ & ~& | ~| ^ ~^ ^~ ++ -- (unary)
  POWER: 35,               // **                                                  Left
  MULTIPLY: 34,            // * / %                                               Left
  ADD: 33,                 // + - (binary)                                        Left
  SHIFT: 32,               // << >> <<< >>>                                       Left
  RELATIONAL: 31,          // < <= > >= inside dist                               Left
  EQUAL: 30,               // == != === !== ==? !=?                               Left
  BITWISE_AND: 29,         // & (binary)                                          Left
  EXCLUSIVE_OR: 28,        // ^ ~^ ^~ (binary)                                    Left
  BITWISE_OR: 27,          // | (binary)                                          Left
  MATCHES: 26,             // A.10.30: The matches operator shall have higher
                           // precedence than the && and || operators
  LOGICAL_AND: 25,         // &&                                                  Left
  LOGICAL_OR: 24,          // ||                                                  Left
  CONDITIONAL: 23,         // ?: (conditional operator)                           Right
  IMPLICATION: 22,         // -> <->                                              Right
  ASSIGN: 21,              // = += -= *= /= %= &= ^= |= <<= >>= <<<=              None
                           // >>>= := :/ <=
  CONCAT: 20,              // {} {{}}                                             Concatenation

  // Table 16-3—Sequence and property operator precedence and associativity
  SEQ_PARENTHESIS: 19,     // [* ] [= ] [-> ]
  SEQ_SHARP2: 18,          // ##                                                  Left
  SEQ_THROUGHOUT: 17,      // throughout                                          Right
  SEQ_WITHIN: 16,          // within                                              Left
  SEQ_INTERSECT: 15,       // intersect                                           Left
  PROP_NEXTTIME: 14,       // not, nexttime, s_nexttime                           —
  PROP_SEQ_AND: 13,        // and                                                 Left
  PROP_SEQ_OR: 12,         // or                                                  Left
  PROP_IFF: 11,            // iff                                                 Right
  PROP_UNTIL: 10,          // until, s_until, until_with, s_until_with, implies   Right
  PROP_INCIDENCE: 9,       // |->, |=>, #-#, #=#                                  Right
  PROP_ALWAYS: 8           // always, s_always, eventually, s_eventually,          —
                           // if-else, case , accept_on, reject_on,
                           // sync_accept_on, sync_reject_on
};

const BINARY_OP_TABLE = [
  ['+',   PREC.ADD],
  ['-',   PREC.ADD],
  ['*',   PREC.MULTIPLY],
  ['/',   PREC.MULTIPLY],
  ['%',   PREC.MULTIPLY],
  ['==',  PREC.EQUAL],
  ['!=',  PREC.EQUAL],
  ['===', PREC.EQUAL],
  ['!==', PREC.EQUAL],
  ['==?', PREC.EQUAL],
  ['!=?', PREC.EQUAL],
  ['&&',  PREC.LOGICAL_AND],
  ['||',  PREC.LOGICAL_OR],
  ['**',  PREC.POWER],
  ['>',   PREC.RELATIONAL],
  ['<',   PREC.RELATIONAL],
  ['>=',  PREC.RELATIONAL],
  ['<=',  PREC.RELATIONAL],
  ['&',   PREC.BITWISE_AND],
  ['|',   PREC.BITWISE_OR],
  ['^',   PREC.EXCLUSIVE_OR],
  ['^~',  PREC.EXCLUSIVE_OR],
  ['~^',  PREC.EXCLUSIVE_OR],
  ['>>',  PREC.SHIFT],
  ['<<',  PREC.SHIFT],
  ['>>>', PREC.SHIFT],
  ['<<<', PREC.SHIFT],
  ['->',  PREC.IMPLICATION],
  ['<->', PREC.IMPLICATION],
]

const BINARY_MOD_PATH_OP_TABLE = [
  ['==', PREC.EQUAL],
  ['!=', PREC.EQUAL],
  ['&&', PREC.LOGICAL_AND],
  ['||', PREC.LOGICAL_OR],
  ['&',  PREC.BITWISE_AND],
  ['|',  PREC.BITWISE_OR],
  ['^',  PREC.EXCLUSIVE_OR],
  ['^~', PREC.EXCLUSIVE_OR],
  ['~^', PREC.EXCLUSIVE_OR],
]

const BINARY_MACRO_OP_TABLE = [
  ['&&',  PREC.LOGICAL_AND],
  ['||',  PREC.LOGICAL_OR],
  ['->',  PREC.IMPLICATION],
  ['<->', PREC.IMPLICATION],
]


function sepBy1(sep, rule) {
  return seq(rule, repeat(seq(sep, rule)))
}

function sepBy(sep, rule) {
  return optional(sepBy1(sep, rule))
}

function sepBy1prec(sep, precedence, rule) {
  return seq(rule, repeat(prec(precedence, seq(sep, rule))))
}

function commaSep1(rule) {
  return sepBy1(',', rule)
}

function commaSep(rule) {
  return sepBy(',', rule)
}

function optseq(...rules) {
  return optional(seq(...rules));
}

function optchoice(...rules) {
  return optional(choice(...rules));
}

function enclosing(keyword, identifier) {
  return seq(keyword, optseq(':', identifier));
}

function repseq(...rules) {
  return repeat(seq(...rules));
}

function repseq1(...rules) {
  return repeat1(seq(...rules));
}

function repseqprec(precedence, ...rules) {
  return repeat(prec(precedence, seq(...rules)));
}

function repseq1prec(precedence, ...rules) {
  return repeat1(prec(precedence, seq(...rules)));
}


// Written according to $.list_of_arguments and modified to avoid
// matching the empty string
function list_of_args($, precedence, arg) {
  return prec(precedence, choice(
    // First case: mixing positional and named arguments
    seq(
      arg,
      repseq(',', optional(arg)),
      repseq(',', '.', $._identifier, '(', optional(arg), ')')
    ),
    seq(
      optional(arg),
      repseq1(',', optional(arg)),
      repseq(',', '.', $._identifier, '(', optional(arg), ')')
    ),
    seq(
      optional(arg),
      repseq(',', optional(arg)),
      repseq1(',', '.', $._identifier, '(', optional(arg), ')')
    ),
    // Second case: using only named arguments
    commaSep1(seq('.', $._identifier, '(', optional(arg), ')'))
  ))
}

function binary_expr($, table, expr) {
  return choice(...table.map(([operator, precedence]) => {
    return prec.left(precedence, seq(
      field('left', expr),
      // @ts-ignore
      field('operator', operator),
      repeat($.attribute_instance),
      field('right', expr),
    ));
  }));
}

function unary_expr($, operator, arg) {
  return prec.left(PREC.UNARY, seq(
    field('operator', operator),
    repeat($.attribute_instance),
    field('argument', arg)
  ));
}

function conditional_expr($, pred, expr) {
  return prec.right(PREC.CONDITIONAL, seq(
    pred,
    '?',
    repeat($.attribute_instance), expr,
    ':',
    expr
  ));
}

function paren_expr(expr) {
  return prec.left(PREC.PARENTHESIS, seq(
    '(', expr, ')'
  ));
}

function directive(command) {
  return alias(new RegExp('`' + command), 'directive_' + command);
}


/*
    Verilog parser grammar based on IEEE Std 1800-2023.
*/

const rules = {

  // LRM includes optional $.timeunits_declaration. but having it creates
  // unnecessary conflicts with the $.snippets children which already cover it.
  source_file: $ => repeat($._description),

  snippets: $ => choice(
    $._directives,
    $._module_item,
    $.statement,
    $.package_import_declaration,
  ),

// * A.1 Source text
// ** A.1.1 Library source text
  _library_text: $ => $._library_description, // Modified to avoid matching empty string

  _library_description: $ => prec('_library_description', choice(
    $.library_declaration,
    $.include_statement,
    $.config_declaration,
    ';'
  )),

  library_declaration: $ => seq(
    'library',
    $.library_identifier,
    commaSep1($.file_path_spec),
    optseq('-incdir', commaSep1($.file_path_spec)),
    ';'
  ),

  include_statement: $ => seq('include', $.file_path_spec, ';'),

  file_path_spec: $ => /[^;\n]+/,


// ** A.1.2 SystemVerilog source text
  _description: $ => prec('_description', choice(
    $.module_declaration,
    $.udp_declaration,
    $.interface_declaration,
    $.program_declaration,
    $.package_declaration,
    seq(repeat($.attribute_instance), choice($._package_item, $.bind_directive)),
    $._library_text, // Includes $.config_declaration as one of its branches
    $.snippets, // Out of LRM (inlined)
  )),

  _module_header: $ => seq( // Out of LRM, groups common tokens of module headers
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
      repeat(alias($._module_item, $.module_item)),
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
      repeat(alias($._module_item, $.module_item)),
      enclosing('endmodule', $.module_identifier)
    ),
    seq('extern', $.module_nonansi_header),
    seq('extern', $.module_ansi_header)
  )),

  module_keyword: $ => choice('module', 'macromodule'),

  interface_declaration: $ => prec('interface_declaration', choice(
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
  )),

  // Out of LRM, groups common tokens of interface headers
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

  program_declaration: $ => prec('program_declaration', choice(
    seq(
      $.program_nonansi_header,
      optional($.timeunits_declaration),
      repeat($.program_item),
      enclosing('endprogram', $.program_identifier)
    ),
    seq(
      $.program_ansi_header,
      optional($.timeunits_declaration),
      repeat($._non_port_program_item),
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
  )),

  // Out of LRM, groups common tokens of program headers
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
    repseq(repeat($.attribute_instance), alias($.checker_or_generate_item, $.checker_item)),
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
    optseq('implements', commaSep1($.interface_class_type)),
    ';',
    repeat($.class_item),
    enclosing('endclass', $.class_identifier)
  ),

  interface_class_declaration: $ => seq(
    'interface', 'class',
    field('name', $.class_identifier),
    optional($.parameter_port_list),
    optseq('extends', optional(commaSep1($.interface_class_type)), ';'),
    repeat($.interface_class_item),
    enclosing('endclass',$.class_identifier)
  ),

  package_declaration: $ => prec('package_declaration', seq(
    repeat($.attribute_instance),
    'package', optional($.lifetime),
    field('name', $.package_identifier), ';',
    optional($.timeunits_declaration),
    repseq(repeat($.attribute_instance), alias($._package_item, $.package_item)),
    enclosing('endpackage',$.package_identifier)
  )),

  timeunits_declaration: $ => prec.right(choice(
    seq('timeunit', $.time_literal, optseq('/', $.time_literal), ';'),
    seq('timeprecision', $.time_literal, ';'),
    seq('timeunit', $.time_literal, ';', 'timeprecision', $.time_literal, ';'),
    seq('timeprecision', $.time_literal, ';', 'timeunit', $.time_literal, ';')
  )),


// ** A.1.3 Module parameters and ports
  parameter_port_list: $ => seq(
    '#', '(',
    optchoice(
      seq($.list_of_param_assignments, repseq(',', $.parameter_port_declaration)),
      commaSep1($.parameter_port_declaration)
    ),
    ')'
  ),

  parameter_port_declaration: $ => choice(
    $.any_parameter_declaration,
    seq($.data_type, $.list_of_param_assignments),
    $.type_parameter_declaration,
  ),

  // Only the $.port_reference branch should be legal in a nonansi declaration
  list_of_ports: $ => seq('(', commaSep(alias($.port_reference, $.port)), ')'),

  list_of_port_declarations: $ => seq(
    '(',
    commaSep(seq(
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
      prec.dynamic(-1, $.interface_port_declaration) // Give higher priority to data declaration
    )
  ),

  // Modified to avoid matching empty string
  port: $ => choice(
    $._port_expression,
    seq('.', $.port_identifier, '(', optional($._port_expression), ')')
  ),

  _port_expression: $ => choice(
    $.port_reference,
    seq('{', commaSep1($.port_reference), '}')
  ),

  port_reference: $ => prec('port_reference', seq(
    $.port_identifier,
    optional($.constant_select)
  )),

  port_direction: $ => prec('port_direction', choice(
    'input', 'output', 'inout', 'ref'
  )),

  // Modified to avoid matching empty string, ($.net_port_type could match empty string)
  net_port_header: $ => choice(
    seq(optional($.port_direction), $.net_port_type),
    $.port_direction
  ),

  variable_port_header: $ => seq(optional($.port_direction), $.variable_port_type),

  interface_port_header: $ => seq(
    choice(field('interface_name', $.interface_identifier), 'interface'),
    optseq('.', field('modport_name', $.modport_identifier))
  ),

  ansi_port_declaration: $ => prec('ansi_port_declaration', choice(
    prec.dynamic(0, seq(
      optchoice($.net_port_header, $.interface_port_header),
      field('port_name', $.port_identifier),
      repeat(prec('ansi_port_declaration', $.unpacked_dimension)),
      optseq('=', $.constant_expression)
    )),
    prec.dynamic(1, seq(
      optional($.variable_port_header),
      field('port_name', $.port_identifier),
      repeat($._variable_dimension),
      optseq('=', $.constant_expression)
    )),
    seq(
      optional($.port_direction), '.',
      field('port_name', $.port_identifier),
      '(', optional($.expression), ')'
    )
  )),


// ** A.1.4 Module items
  severity_system_task: $ => choice(
    seq(
      '$fatal',
      // LRM makes $.finish_number mandatory but seems tool specific (relax requirement)
      optseq('(', optseq($.finish_number, ','), optional($.list_of_arguments), ')'),
      ';'
    ),
    seq(choice('$error', '$warning', '$info'), optseq('(', optional($.list_of_arguments), ')'), ';')
  ),

  finish_number: $ => choice('0', '1', '2'),

  elaboration_severity_system_task: $ => $.severity_system_task,

  _module_common_item: $ => prec('_module_common_item', choice(
    $._module_or_generate_item_declaration,
    $.interface_instantiation,
    $.program_instantiation,
    $._assertion_item,
    $.bind_directive,
    $.continuous_assign,
    $.net_alias,
    $.initial_construct,
    $.final_construct,
    $.always_construct,
    $.loop_generate_construct,
    $.conditional_generate_construct,
    $.elaboration_severity_system_task
  )),

  _module_item: $ => choice(
    seq($.port_declaration, ';'),
    $._non_port_module_item
  ),

  _module_or_generate_item: $ => prec('_module_or_generate_item', seq(
    repeat($.attribute_instance),
    choice(
      $.parameter_override,
      $.gate_instantiation,
      $.module_instantiation,
      $.udp_instantiation,
      $._module_common_item
    )
  )),

  _module_or_generate_item_declaration: $ => prec('_module_or_generate_item_declaration', choice(
    $._package_or_generate_item_declaration,
    $.genvar_declaration,
    $.clocking_declaration,
    seq('default', 'clocking', $.clocking_identifier, ';'),     // INFO: Could be possible to group these two below
    seq('default', 'disable', 'iff', $.expression_or_dist, ';') //       with the ones in $._checker_or_generate_item_declaration
  )),

  _non_port_module_item: $ => prec('_non_port_module_item', choice(
    $.generate_region,
    $._module_or_generate_item,
    $.specify_block,
    seq(repeat($.attribute_instance), $.specparam_declaration),
    $.program_declaration,
    $.module_declaration,
    $.interface_declaration,
    $.timeunits_declaration, // A.10.3
    $._directives, // Out of LRM
  )),

  parameter_override: $ => seq('defparam', $.list_of_defparam_assignments, ';'),

  bind_directive: $ => seq(
    'bind',
    choice(
      seq($.bind_target_scope, optseq(':', $.bind_target_instance_list)),
      $.bind_target_instance
    ),
    $._bind_instantiation,
    // ';' // INFO: bug in spec, colon already included in $._bind_instantiation
  ),

  bind_target_scope: $ => prec('bind_target_scope', choice(
    $.module_identifier,
    $.interface_identifier
  )),

  bind_target_instance: $ => seq(
    $.hierarchical_identifier,
    optional($.constant_bit_select)
  ),

  bind_target_instance_list: $ => commaSep1($.bind_target_instance),

  _bind_instantiation: $ => prec('_bind_instantiation', choice(
    $.program_instantiation,
    $.module_instantiation,
    $.interface_instantiation,
    // $.checker_instantiation
  )),


// ** A.1.5 Configuration source text
  config_declaration: $ => seq(
    'config', field('name', $.config_identifier), ';',
    repseq($.local_parameter_declaration, ';'),
    $.design_statement,
    repeat($.config_rule_statement),
    enclosing('endconfig', $.config_identifier)
  ),

  design_statement: $ => seq(
    'design', repseq(optseq($.library_identifier, '.'), $.cell_identifier), ';'
  ),

  config_rule_statement: $ => seq(
    choice(
      seq(choice($.default_clause, $.inst_clause, $.cell_clause), $.liblist_clause),
      seq(choice($.inst_clause, $.cell_clause), $.use_clause),
    ),
    ';'
  ),

  default_clause: $ => 'default',

  inst_clause: $ => seq('instance', $.inst_name),

  inst_name: $ => seq($.topmodule_identifier, repseq('.', $.instance_identifier)),

  cell_clause: $ => seq('cell', optseq($.library_identifier, '.'), $.cell_identifier),

  liblist_clause: $ => seq('liblist', repeat($.library_identifier)),

  use_clause: $ => seq(
    'use',
    choice(
      // The LRM does not include the #() in the $.named_parameter_assignment branches, but that seems
      // necessary to parse the examples of chapter 33.4.2 successfully
      seq(optseq($.library_identifier, '.'), $.cell_identifier, optseq('#', '(', commaSep1($.named_parameter_assignment), ')')),
      optseq('#', '(', commaSep1($.named_parameter_assignment), ')')
    ),
    optseq(':', 'config')
  ),


// ** A.1.6 Interface items
  _interface_or_generate_item: $ => prec('_interface_or_generate_item', choice(
    seq(repeat($.attribute_instance), choice($._module_common_item, $.extern_tf_declaration)),
    $._directives // Out of LRM
  )),

  extern_tf_declaration: $ => seq(
    'extern',
    choice(
      $._method_prototype,
      seq('forkjoin', $.task_prototype)
    ),
    ";"
  ),

  interface_item: $ => choice(
    seq($.port_declaration, ';'),
    $._non_port_interface_item
  ),

  _non_port_interface_item: $ => prec('_non_port_interface_item', choice(
    $.generate_region,
    $._interface_or_generate_item,
    $.program_declaration,
    $.modport_declaration,
    $.interface_declaration,
    $.timeunits_declaration // A.10.3
  )),


// ** A.1.7 Program items
  program_item: $ => choice(
    seq($.port_declaration, ';'),
    $._non_port_program_item
  ),

  _non_port_program_item: $ => prec('_non_port_program_item', choice(
    seq(repeat($.attribute_instance), choice(
      $.continuous_assign,
      $._module_or_generate_item_declaration,
      $.initial_construct,
      $.final_construct,
      $.concurrent_assertion_item,
    )),
    $.timeunits_declaration, // A.10.3
    $._program_generate_item
  )),

  _program_generate_item: $ => choice(
    $.loop_generate_construct,
    $.conditional_generate_construct,
    $.generate_region,
    $.elaboration_severity_system_task
  ),


// ** A.1.8 Checker items
  checker_port_list: $ => commaSep1($.checker_port_item),

  checker_port_item: $ => seq(
    repeat($.attribute_instance),
    optional($.checker_port_direction),
    optional($.property_formal_type), // Contains empty string branch $.data_type_or_implicit
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optseq('=', $._property_actual_arg)
  ),

  checker_port_direction: $ => choice('input', 'output'),

  checker_or_generate_item: $ => prec('checker_or_generate_item', choice(
    $._checker_or_generate_item_declaration,
    $.initial_construct,
    $.always_construct,
    $.final_construct,
    $._assertion_item,
    $.continuous_assign,
    $._checker_generate_item,
    // INFO: Out of LRM: This is a workaround to support checker_instantiations
    // and avoid multiple conflicts with module/interface/program instantiations.
    // The proper way to do it would be uncommenting the $.checker_instantiation
    // in $.concurrent_assertion_item and removing the one below.
    $.checker_instantiation
  )),

  _checker_or_generate_item_declaration: $ => prec('_checker_or_generate_item_declaration', choice(
    seq(optional('rand'), $.data_declaration),
    $.function_declaration,
    $.checker_declaration,
    $._assertion_item_declaration,
    $.covergroup_declaration,
    $.genvar_declaration,
    $.clocking_declaration,
    seq('default', choice(
      seq('clocking', $.clocking_identifier),
      seq('disable', 'iff', $.expression_or_dist)
    ), ';'),
    ';'
  )),

  _checker_generate_item: $ => prec('_checker_generate_item', choice(
    $.loop_generate_construct,
    $.conditional_generate_construct,
    $.generate_region,
    $.elaboration_severity_system_task
  )),


// ** A.1.9 Class items
  class_item: $ => choice(
    seq(repeat($.attribute_instance), choice(
      $.class_property,
      $.class_method,
      $._class_constraint,
      $.class_declaration,
      $.interface_class_declaration,
      $.covergroup_declaration,
    )),
    seq($.any_parameter_declaration, ';'),
    ';',
    $._directives, // Out of LRM
  ),

  class_property: $ => prec('class_property', choice(
    seq(repeat($._property_qualifier), $.data_declaration),
    seq(
      'const',
      repeat($.class_item_qualifier),
      $.data_type,
      $.const_identifier,
      optseq('=', $.constant_expression),
      ';'
    )
  )),

  class_method: $ => prec('class_method', choice(
    seq(repeat($.method_qualifier), choice(
      $.task_declaration,
      $.function_declaration,
      $.class_constructor_declaration
    )),
    seq('extern', repeat($.method_qualifier), choice(
      seq($._method_prototype, ';'),
      $.class_constructor_prototype,
    )),
    seq('pure', 'virtual', repeat($.class_item_qualifier), $._method_prototype, ';'),
  )),

  class_constructor_declaration: $ => prec('class_constructor_declaration', seq(
    'function', optional($.class_scope), 'new',
    optseq('(', optional($.class_constructor_arg_list), ')'), ';',
    repeat($.block_item_declaration),
    optseq('super', '.', 'new', optseq('(', optional($.list_of_arguments), ')'), ';'),
    repeat($.function_statement_or_null),
    enclosing('endfunction', 'new')
  )),

  class_constructor_prototype: $ => seq(
    'function', 'new',
    optseq('(', optional($.class_constructor_arg_list), ')'), ';'
  ),

  class_constructor_arg_list: $ => commaSep1($.class_constructor_arg),

  class_constructor_arg: $ => choice($.tf_port_item, 'default'),

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


// ** A.1.10 Constraints
  constraint_declaration: $ => seq(
    choice(
      // A.10.11: It shall be illegal to use the dynamic_override_specifiers with static constraints
      seq('static', 'constraint'),
      seq('constraint', optional($.dynamic_override_specifiers)),
    ),
    $.constraint_identifier,
    $.constraint_block
  ),

  constraint_block: $ => seq('{', repeat($.constraint_block_item), '}'),

  constraint_block_item: $ => choice(
    seq('solve', $.solve_before_list, 'before', $.solve_before_list, ';'),
    $.constraint_expression
  ),

  solve_before_list: $ => commaSep1($.constraint_primary),

  constraint_primary: $ => seq(
    optchoice(seq($.implicit_class_handle, '.'), $.class_scope),
    $.hierarchical_identifier,
    optional($.select),
    optseq('(', ')')
  ),

  constraint_expression: $ => choice(
    seq(optional('soft'), $.expression_or_dist, ';'),
    seq($.uniqueness_constraint, ';'),
    prec.right(PREC.IMPLICATION, seq($.expression, '->', $.constraint_set)),
    prec.right(seq('if', '(', $.expression, ')', $.constraint_set, optseq('else', $.constraint_set))),
    seq('foreach', '(', $.ps_or_hierarchical_array_identifier, '[', optional($.loop_variables), ']', ')', $.constraint_set),
    seq('disable', 'soft', $.constraint_primary, ';')
  ),

  uniqueness_constraint: $ => seq(
    'unique', '{', $.range_list, '}'
  ),

  constraint_set: $ => prec('constraint_set', choice(
    $.constraint_expression,
    seq('{', repeat($.constraint_expression), '}')
  )),

  expression_or_dist: $ => prec('expression_or_dist', seq(
    $.expression,
    optional(prec.left(PREC.RELATIONAL, seq('dist', '{', $.dist_list, '}')))
  )),

  dist_list: $ => commaSep1($.dist_item),

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
    choice(
      // A.10.11: It shall be illegal to use the dynamic_override_specifiers with static constraints
      seq('static', 'constraint'),
      seq('constraint', optional($.dynamic_override_specifiers)),
    ),
    $.class_scope,
    $.constraint_identifier,
    $.constraint_block
  ),


// ** A.1.11 Package items
  _package_item: $ => prec('_package_item', choice(
    $._package_or_generate_item_declaration,
    $.anonymous_program,
    $.package_export_declaration,
    $.timeunits_declaration // A.10.3
  )),

  _package_or_generate_item_declaration: $ => prec('_package_or_generate_item_declaration', choice(
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
    $._directives // Out of LRM
  )),

  anonymous_program: $ => seq(
    'program', ';', repeat($.anonymous_program_item), 'endprogram'
  ),

  anonymous_program_item: $ => choice(
    $.task_declaration,
    $.function_declaration,
    $.class_declaration,
    $.covergroup_declaration,
    $.class_constructor_declaration,
    ';'
  ),


// * A.2 Declarations
// ** A.2.1 Declaration types
// *** A.2.1.1 Module parameter declarations
  local_parameter_declaration: $ => seq(
    'localparam',
    choice(
      seq(optional($.data_type_or_implicit), $.list_of_param_assignments),
      $.type_parameter_declaration,
    )),

  parameter_declaration: $ => seq(
    'parameter',
    choice(
      seq(optional($.data_type_or_implicit), $.list_of_param_assignments),
      $.type_parameter_declaration,
    )),

  type_parameter_declaration: $ => seq('type', optional($._forward_type), $.list_of_type_assignments),

  any_parameter_declaration: $ => choice($.local_parameter_declaration, $.parameter_declaration),

  specparam_declaration: $ => seq('specparam', optional($.packed_dimension), $.list_of_specparam_assignments, ';'),


// *** A.2.1.2 Port declarations
  inout_declaration: $ => seq('inout', optional($.net_port_type), $.list_of_port_identifiers),

  input_declaration: $ => seq(
    'input', choice(
      prec.dynamic(0, seq(optional($.net_port_type), $.list_of_port_identifiers)),         // For non-builtin types, give typedef types (variables) higher precedence
      prec.dynamic(1, seq(optional($.variable_port_type), $.list_of_variable_identifiers)) // than netttype types (nets) (check core/module/nonansi_1)
    )
  ),

  output_declaration: $ => seq(
    'output', choice(
      prec.dynamic(0, seq(optional($.net_port_type), $.list_of_port_identifiers)),              // For non-builtin types, give typedef types (variables) higher precedence
      prec.dynamic(1, seq(optional($.variable_port_type), $.list_of_variable_port_identifiers)) // than netttype types (nets) (check core/module/nonansi_1)
    )
  ),

  interface_port_declaration: $ => seq(
    $.interface_identifier,
    optseq('.', $.modport_identifier),
    $.list_of_interface_identifiers
  ),

  ref_declaration: $ => seq('ref', $.variable_port_type, $.list_of_variable_identifiers),


// *** A.2.1.3 Type declarations
  data_declaration: $ => prec('data_declaration', choice(
    seq(
      optional('const'),
      // A.10.4: In a data_declaration, it shall be illegal to omit the explicit data_type
      // before a list_of_variable_decl_assignments unless the var keyword is used.
      choice(
        seq('var', optional($.lifetime), optional($.data_type_or_implicit)),
        seq(optional($.lifetime), $.data_type_or_implicit),
      ),
      $.list_of_variable_decl_assignments,
      ';'
    ),
    $.type_declaration,
    $.package_import_declaration,
    $.nettype_declaration
  )),

  package_import_declaration: $ => seq('import', commaSep1($.package_import_item), ';'),

  package_export_declaration: $ => seq('export', choice('*::*', commaSep1($.package_import_item)), ';'),

  package_import_item: $ => seq($.package_identifier, '::', choice($._identifier, '*')),

  genvar_declaration: $ => seq('genvar', $.list_of_genvar_identifiers, ';'),

  net_declaration: $ => seq(
    choice(
      seq(
        $.net_type,
        optchoice($.drive_strength, $.charge_strength),
        optchoice('vectored', 'scalared'),
        optional($.data_type_or_implicit),
        optional($.delay3),
        $.list_of_net_decl_assignments,
      ),
      seq(
        $.nettype_identifier,
        optional($.delay_control),
        $.list_of_net_decl_assignments,
      ),
      seq(
        'interconnect',
        optional($.implicit_data_type),
        optseq('#', $.delay_value),
        $.net_identifier,
        repeat($.unpacked_dimension),
        optseq(',', $.net_identifier, repeat($.unpacked_dimension)),
      )),
    ';'
  ),

  type_declaration: $ => seq(
    'typedef',
    choice(
      seq($._data_type_or_incomplete_class_scoped_type, field('type_name', $.type_identifier), repeat($._variable_dimension)),
      seq($.interface_port_identifier, optional($.constant_bit_select), '.', $.type_identifier, field('type_name', $.type_identifier)),
      seq(optional($._forward_type), field('type_name', $.type_identifier))
    ),
    ';'
  ),

  _forward_type: $ => choice('enum', 'struct', 'union', seq(optional('interface'), 'class')),

  nettype_declaration: $ => prec('nettype_declaration', seq(
    'nettype',
    choice(
      seq(
        $.data_type,
        $.nettype_identifier,
        optseq(
          'with',
          optchoice($.package_scope, $.class_scope),
          $.tf_identifier
        )
      ),
      seq(
        optchoice($.package_scope, $.class_scope),
        $.nettype_identifier,
        $.nettype_identifier
      )
    ),
    ';'
  )),

  lifetime: $ => prec('lifetime', choice('static', 'automatic')),


// ** A.2.2 Declaration data types
// *** A.2.2.1 Net and variable types
  // $.constant_mintypmax_expression and $.type_reference replace the $.constant_primary
  // branch, as these are the only possible options of $.constant_primary in a static cast.
  // A.10.45: It shall be legal to use a type_reference constant_primary as the casting_type in a static cast.
  casting_type: $ => choice(
    $._simple_type,
    seq('(', $.constant_mintypmax_expression, ')'), // $.constant_primary branch
    $.type_reference,                               // $.constant_primary branch
    $._signing,
    'string',
    'const'
  ),

  data_type: $ => prec('data_type', choice(
    seq($.integer_vector_type, optional($._signing), repeat($.packed_dimension)),
    seq($.integer_atom_type, optional($._signing)),
    $.non_integer_type,
    seq(
      $.struct_union,
      optseq('packed', optional($._signing)),
      '{', repeat1(choice($._directives, $.struct_union_member)), '}', // _directives out of LRM, (e.g. allow use of `ifdefs in structs)
      repeat($.packed_dimension)
    ),
    seq(
      'enum', optional($.enum_base_type),
      '{', choice($._directives, commaSep1($.enum_name_declaration)), '}', // _directives out of LRM, (e.g. allow use of `ifdefs in structs)
      repeat($.packed_dimension)
    ),
    'string',
    'chandle',
    seq(
      'virtual', optional('interface'),
      $.interface_identifier,
      optional($.parameter_value_assignment),
      optseq('.', $.modport_identifier)
    ),
    seq(
      optchoice($.class_scope, $.package_scope),
      $.type_identifier,
      repeat($.packed_dimension)
    ),
    $.class_type,
    'event',
    $.ps_covergroup_identifier,
    $.type_reference
  )),

  data_type_or_implicit: $ => prec('data_type_or_implicit', choice(
    $.data_type,
    $.implicit_data_type
  )),

  // Modified to avoid matching empty string
  implicit_data_type: $ => prec.right(choice(
    seq($._signing, repeat($.packed_dimension)),
    repeat1($.packed_dimension)
  )),

  enum_base_type: $ => choice(
    seq($.integer_atom_type, optional($._signing)),
    seq($.integer_vector_type, optional($._signing), optional($.packed_dimension)),
    seq($.type_identifier, optional($.packed_dimension))
  ),

  enum_name_declaration: $ => seq(
    $.enum_identifier,
    optseq('[', $.integral_number, optseq(':', $.integral_number), ']'),
    optseq('=', $.constant_expression)
  ),

  class_scope: $ => seq($.class_type, '::'),

  class_type: $ => prec('class_type', seq(
    $.ps_class_identifier, optional($.parameter_value_assignment),
    repeat(prec('class_type_repeat1', seq('::', $.class_identifier, optional($.parameter_value_assignment))))
  )),

  interface_class_type: $ => seq($.ps_class_identifier, optional($.parameter_value_assignment)),

  _integer_type: $ => choice($.integer_vector_type, $.integer_atom_type),

  integer_atom_type: $ => choice('byte', 'shortint', 'int', 'longint', 'integer', 'time'),

  integer_vector_type: $ => choice('bit', 'logic', 'reg'),

  non_integer_type: $ => choice('shortreal', 'real', 'realtime'),

  net_type: $ => choice('supply0', 'supply1', 'tri', 'triand', 'trior', 'trireg', 'tri0', 'tri1', 'uwire', 'wire', 'wand', 'wor'),

  // Modified to avoid matching empty string
  net_port_type: $ => choice(
    $.net_type,
    seq(optional($.net_type), $.data_type_or_implicit),
    $.nettype_identifier,
    seq('interconnect', optional($.implicit_data_type))
  ),

  variable_port_type: $ => prec('variable_port_type', $.var_data_type),

  var_data_type: $ => choice(
    $.data_type,
    seq('var', optional($.data_type_or_implicit))
  ),

  _signing: $ => choice('signed', 'unsigned'),

  _simple_type: $ => prec('_simple_type', choice(
    $._integer_type,
    $.non_integer_type,
    $.ps_type_identifier,
    $.ps_parameter_identifier
  )),

  struct_union: $ => choice(
    'struct',
    seq('union', optchoice('soft', 'tagged'))
  ),

  struct_union_member: $ => seq(
    repeat($.attribute_instance),
    optional($.random_qualifier),
    $.data_type_or_void,
    $.list_of_variable_decl_assignments,
    ';'
  ),

  data_type_or_void: $ => choice($.data_type, 'void'),

  // A.10.21) An expression that is used as the argument in a type_reference
  // shall not contain any hierarchical references or references to elements of
  // dynamic objects.
  type_reference: $ => seq(
    'type',
    '(', choice($.expression, $._data_type_or_incomplete_class_scoped_type), ')'
  ),

  _data_type_or_incomplete_class_scoped_type: $ => prec('_data_type_or_incomplete_class_scoped_type', choice(
    $.data_type,
    $._incomplete_class_scoped_type
  )),

  // Set precedence to fix parsing conflict: could result in an endless loop due to recursivity
  _incomplete_class_scoped_type: $ => prec('_incomplete_class_scoped_type', choice(
    seq($.type_identifier, '::', $._type_identifier_or_class_type),
    $._incomplete_class_scoped_type, '::', $._type_identifier_or_class_type
  )),

  _type_identifier_or_class_type: $ => prec('_type_identifier_or_class_type', choice($.type_identifier, $.class_type)),

  // Out of LRM, used to restrict the choices to
  associative_dimension_data_type: $ => choice(
    seq($.integer_vector_type, optional($._signing), repeat($.packed_dimension)), // 7.8.4
    seq($.integer_atom_type, optional($._signing)), // 7.8.4
    'string', // 7.8.2
    // Do not include 7.8.3 Class index to avoid ambiguities with packed array declarations
  ),


// *** A.2.2.2 Strengths
  drive_strength: $ => seq(
    '(',
    choice(
      seq($.strength0, ',', choice($.strength1, 'highz1')),
      seq($.strength1, ',', choice($.strength0, 'highz0')),
      seq('highz0', ',', $.strength1),
      seq('highz1', ',', $.strength0)
    ),
    ')'
  ),

  strength0: $ => choice('supply0', 'strong0', 'pull0', 'weak0'),

  strength1: $ => choice('supply1', 'strong1', 'pull1', 'weak1'),

  charge_strength: $ => seq('(', choice('small', 'medium', 'large'), ')'),


// *** A.2.2.3 Delays
  delay2: $ => seq(
    '#',
    choice(
      $.delay_value,
      seq('(', $.mintypmax_expression, optseq(',', $.mintypmax_expression), ')')
    )
  ),

  delay3: $ => seq(
    '#',
    choice(
      $.delay_value,
      seq('(', $.mintypmax_expression, optseq(',', $.mintypmax_expression, optseq(',', $.mintypmax_expression)), ')')
    )
  ),

  delay_value: $ => choice(
    $.unsigned_number,
    $.real_number,
    $.ps_identifier,
    $.time_literal,
    '1step'
  ),


// ** A.2.3 Declaration lists
  list_of_defparam_assignments: $ => commaSep1($.defparam_assignment),

  list_of_genvar_identifiers: $ => commaSep1($.genvar_identifier),

  list_of_interface_identifiers: $ => commaSep1(seq($.interface_identifier, repeat($.unpacked_dimension))),

  list_of_net_decl_assignments: $ => commaSep1($.net_decl_assignment),

  list_of_param_assignments: $ => commaSep1($.param_assignment),

  list_of_port_identifiers: $ => prec('list_of_port_identifiers',
    sepBy1prec(',', 'list_of_port_identifiers', seq(
      $.port_identifier,
      repeat(prec('list_of_port_identifiers', $.unpacked_dimension))
    ))
  ),

  list_of_udp_port_identifiers: $ => commaSep1($.port_identifier),

  list_of_specparam_assignments: $ => commaSep1($.specparam_assignment),

  list_of_tf_variable_identifiers: $ => commaSep1(seq(
    $.port_identifier,
    repeat($._variable_dimension),
    optseq('=', $.expression)
  )),

  list_of_type_assignments: $ => commaSep1($.type_assignment),

  list_of_variable_decl_assignments: $ => commaSep1($.variable_decl_assignment),

  list_of_variable_identifiers: $ => prec('list_of_variable_identifiers',
    sepBy1prec(',', 'list_of_variable_identifiers', seq(
      $.variable_identifier,
      repeat(prec('list_of_variable_identifiers', $._variable_dimension))
    ))
  ),

  list_of_variable_port_identifiers: $ => prec('list_of_variable_port_identifiers',
    sepBy1prec(',', 'list_of_variable_port_identifiers', seq(
      $.port_identifier,
      repeat(prec('list_of_variable_port_identifiers', $._variable_dimension)),
      optseq('=', $.constant_expression)
    ))
  ),


// ** A.2.4 Declaration assignments
  defparam_assignment: $ => seq($.hierarchical_parameter_identifier, '=', $.constant_mintypmax_expression),

  net_decl_assignment: $ => seq($.net_identifier, repeat($.unpacked_dimension), optseq('=', $.expression)),

  param_assignment: $ => seq($.parameter_identifier, repeat($._variable_dimension), optseq('=', $.constant_param_expression)),

  specparam_assignment: $ => choice(
    seq($.specparam_identifier, '=', $.constant_mintypmax_expression),
    $.pulse_control_specparam
  ),

  pulse_control_specparam: $ => choice(
    seq('PATHPULSE$', '=', '(', $.reject_limit_value, optseq(',', $.error_limit_value), ')'),
    seq(
      // https://stackoverflow.com/questions/39178478/verilog-pathpulse-syntax
      // https://accellera.mantishub.io/view.php?id=1050
      // - Do not allow $ as part of identifiers
      // - Do not allow escaped identifiers (even though it would be possible)
      // - Do not allow optseq('[', $._constant_range_expression, ']') to simplify parser
      token(seq(
        'PATHPULSE$',
        /[a-zA-Z_][a-zA-Z0-9_]*/, // $.specify_input_terminal_descriptor,
        '$',
        /[a-zA-Z_][a-zA-Z0-9_]*/  // $.specify_output_terminal_descriptor),
      )),
      '=', '(', $.reject_limit_value, optseq(',', $.error_limit_value), ')'
    )
  ),

  error_limit_value: $ => $._limit_value,

  reject_limit_value: $ => $._limit_value,

  _limit_value: $ => $.constant_mintypmax_expression,

  type_assignment: $ => seq(
    field('name', $.type_identifier),
    optseq('=', field('value', $._data_type_or_incomplete_class_scoped_type))
  ),

  variable_decl_assignment: $ => choice(
    seq(
      field('name', $.variable_identifier),
      repeat($._variable_dimension),
      optseq('=', $.expression)
    ),
    seq(
      field('name', $.dynamic_array_variable_identifier),
      $.unsized_dimension,
      repeat($._variable_dimension),
      optseq('=', $.dynamic_array_new)
    ),
    seq(
      field('name', $.class_variable_identifier),
      optseq('=', $.class_new)
    )
  ),

  class_new: $ => choice(
    // TODO: Removing dynamic precedences results in detection of other rules where new is
    // not treated as a kewyord but as a hierarchical identifier. This could probably be
    // solved better after fixing some conflicts with precedences
    prec.dynamic(1, seq(optional($.class_scope), 'new', optseq('(', optional($.list_of_arguments), ')'))),
    prec.dynamic(0, seq('new', $.expression))
  ),

  dynamic_array_new: $ => seq('new', '[', $.expression, ']', optseq('(', $.expression, ')')),


// ** A.2.5 Declaration ranges
  unpacked_dimension: $ => prec('unpacked_dimension', seq(
    '[', choice($.constant_range, $.constant_expression), ']'
  )),

  packed_dimension: $ => prec('packed_dimension', choice(
    seq('[', $.constant_range, ']'),
    $.unsized_dimension
  )),

  associative_dimension: $ => seq(
    '[', choice(alias($.associative_dimension_data_type, $.data_type), '*'), ']'
  ),

  _variable_dimension: $ => prec('_variable_dimension', choice(
    $.unsized_dimension,
    prec.dynamic(0, $.unpacked_dimension),
    $.associative_dimension,
    prec.dynamic(1, $.queue_dimension)
  )),

  queue_dimension: $ => prec('queue_dimension', seq(
    '[', '$', optseq(':', $.constant_expression), ']'
  )),

  unsized_dimension: $ => seq('[', ']'),


// ** A.2.6 Function declarations
  _function_data_type_or_implicit: $ => choice(
    $.data_type_or_void,
    $.implicit_data_type
  ),

  function_declaration: $ => seq(
    'function',
    optional($.dynamic_override_specifiers),
    optional($.lifetime),
    $.function_body_declaration
  ),

  function_body_declaration: $ => seq(
    optional($._function_data_type_or_implicit),
    optchoice(seq($.interface_identifier, '.'), $.class_scope),
    field('name', $.function_identifier),
    choice(
      seq(';', repeat($.tf_item_declaration)),
      seq('(', optional($.tf_port_list), ')', ';', repeat($.block_item_declaration))
    ),
    repeat($.function_statement_or_null),
    enclosing('endfunction', $.function_identifier)
  ),

  function_prototype: $ => seq(
    'function',
    optional($.dynamic_override_specifiers),
    $.data_type_or_void,
    field('name', $.function_identifier),
    optseq('(', optional($.tf_port_list), ')')
  ),

  dpi_import_export: $ => choice(
    seq(
      'import', $.dpi_spec_string,
      choice(
        seq(optional($.dpi_function_import_property), optseq(field('c_name', $.c_identifier), '='), $.dpi_function_proto),
        seq(optional($.dpi_task_import_property), optseq(field('c_name', $.c_identifier), '='), $.dpi_task_proto)
      ),
      ';'
    ),
    seq(
      'export', $.dpi_spec_string, optseq(field('c_name', $.c_identifier), '='),
      choice(
        seq('function', field('name', $.function_identifier)),
        seq('task', field('name', $.task_identifier))
      ) ,
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
    optchoice(seq($.interface_identifier, '.'), $.class_scope),
    field('name', $.task_identifier),
    choice(
      seq(';', repeat($.tf_item_declaration)),
      seq('(', optional($.tf_port_list), ')', ';', repeat($.block_item_declaration))
    ),
    repeat($.statement_or_null),
    enclosing('endtask', $.task_identifier)
  ),

  tf_item_declaration: $ => choice($.block_item_declaration, $.tf_port_declaration),

  tf_port_list: $ => commaSep1($.tf_port_item),

  // Modified to avoid matching the empty string
  tf_port_item: $ => seq(
    repeat($.attribute_instance),
    optional($.tf_port_direction),
    optional('var'),
    choice(
      // A.10.28: In a tf_port_item, it shall be illegal to omit the explicit
      // port_identifier except within a function_prototype or task_prototype.
      seq($.data_type_or_implicit, optional(field('name', $.port_identifier))),
      field('name', $.port_identifier),
    ),
    repeat($._variable_dimension),
    optseq('=', $.expression)
  ),

  tf_port_direction: $ => prec('tf_port_direction', choice(
    $.port_direction,
    seq(optional('const'), 'ref', optional('static'))
  )),

  tf_port_declaration: $ => seq(
    repeat($.attribute_instance),
    $.tf_port_direction,
    optional('var'),
    optional($.data_type_or_implicit),
    $.list_of_tf_variable_identifiers,
    ';'
  ),

  task_prototype: $ => seq(
    'task',
    optional($.dynamic_override_specifiers),
    field('name', $.task_identifier),
    optseq('(', optional($.tf_port_list), ')')
  ),

  // Modified to avoid matching the empty string
  dynamic_override_specifiers: $ => choice(
    seq($.initial_or_extends_specifier, optional($.final_specifier)),
    $.final_specifier
  ),

  initial_or_extends_specifier: $ => seq(':', choice('initial', 'extends')),

  final_specifier: $ => seq(':', 'final'),


// ** A.2.8 Block item declarations
  block_item_declaration: $ => seq(
    repeat($.attribute_instance),
    choice(
      $.data_declaration,
      seq($.any_parameter_declaration, ';'),
      $.let_declaration
    )
  ),


// ** A.2.9 Interface declarations
  modport_declaration: $ => seq('modport', commaSep1($.modport_item), ';'),

  modport_item: $ => seq(
    $.modport_identifier,
    '(', commaSep1($.modport_ports_declaration), ')'
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
    commaSep1($.modport_simple_port)
  ),

  modport_simple_port: $ => choice(
    $.port_identifier,
    seq('.', $.port_identifier, '(', optional($.expression), ')')
  ),

  modport_tf_ports_declaration: $ => seq(
    $.import_export, commaSep1($._modport_tf_port)
  ),

  _modport_tf_port: $ => choice(
    $._method_prototype,
    $.tf_identifier
  ),

  import_export: $ => choice('import', 'export'),


// ** A.2.10 Assertion declarations
  concurrent_assertion_item: $ => prec('concurrent_assertion_item', choice(
    seq(optseq($.block_identifier, ':'), $._concurrent_assertion_statement),
    // $.checker_instantiation
    //
    // INFO: Out of LRM: This is a workaround to support checker_instantiations
    //       and avoid multiple conflicts with module/interface/program instantiations.
    //       The proper way to do it would be uncommenting the $.checker_instantiation
    //       here and removing the one in $.checker_or_generate_item
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
    'cover', 'sequence',
    '(',
    optional($.clocking_event),
    optseq('disable', 'iff', '(', $.expression_or_dist, ')'),
    $.sequence_expr,
    ')',
    $.statement_or_null
  ),

  restrict_property_statement: $ => seq(
    'restrict', 'property', '(', $.property_spec, ')', ';'
  ),

  property_instance: $ => seq(
    $.ps_or_hierarchical_property_identifier,
    optseq('(', optional($.property_list_of_arguments), ')')
  ),

  property_list_of_arguments: $ => list_of_args($, 'property_list_of_arguments', $._property_actual_arg),

  _property_actual_arg: $ => choice($.property_expr, $._sequence_actual_arg),

  _assertion_item_declaration: $ => choice(
    $.property_declaration,
    $.sequence_declaration,
    $.let_declaration
  ),

  property_declaration: $ => seq(
    'property',
    field('name', $.property_identifier),
    optseq('(', optional($.property_port_list), ')'),
    ';',
    repeat($.assertion_variable_declaration),
    $.property_spec,
    optional(';'),
    enclosing('endproperty', $.property_identifier)
  ),

  property_port_list: $ => commaSep1($.property_port_item),

  property_port_item: $ => seq(
    repeat($.attribute_instance),
    optseq('local', optional($.property_lvar_port_direction)),
    optional($.property_formal_type), // Contains empty string branch $.data_type_or_implicit
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optseq('=', $._property_actual_arg)
  ),

  property_lvar_port_direction: $ => 'input',

  property_formal_type: $ => choice(
    $.sequence_formal_type,  // Contains empty string branch $.data_type_or_implicit
    'property'
  ),

  property_spec: $ => prec('property_spec', seq(
    optional($.clocking_event),
    optseq('disable', 'iff', '(', $.expression_or_dist, ')'),
    $.property_expr
  )),

  property_expr: $ => choice(
    prec('sequence_expr', $.sequence_expr),
    seq(choice('strong', 'weak'), '(', $.sequence_expr, ')'),
    paren_expr($.property_expr),
    prec(PREC.PROP_NEXTTIME, seq('not', $.property_expr)),
    prec.left(PREC.PROP_SEQ_OR, seq($.property_expr, 'or', $.property_expr)),
    prec.left(PREC.PROP_SEQ_AND, seq($.property_expr, 'and', $.property_expr)),
    prec.right(PREC.PROP_INCIDENCE, seq($.sequence_expr, choice('|->', '|=>', '#-#', '#=#'), $.property_expr)),
    prec.right(seq('if', '(', $.expression_or_dist, ')', $.property_expr, optseq('else', $.property_expr))),
    prec.right(seq('case', '(', $.expression_or_dist, ')', repeat1($.property_case_item), 'endcase')),
    prec.left(PREC.PROP_NEXTTIME, seq(choice('nexttime', 's_nexttime'), optseq('[', $.constant_expression, ']'), $.property_expr)),
    prec.left(PREC.PROP_ALWAYS, seq(choice('always', 's_eventually'), optseq('[', $.cycle_delay_const_range_expression, ']'), $.property_expr)),
    prec.left(PREC.PROP_ALWAYS, seq(choice('s_always', 'eventually'), '[', $.constant_range, ']', $.property_expr)),
    prec.right(PREC.PROP_UNTIL, seq($.property_expr, choice('until', 's_until', 'until_with', 's_until_with', 'implies'), $.property_expr)),
    prec.right(PREC.PROP_IFF, seq($.property_expr, 'iff', $.property_expr)),
    prec(PREC.PROP_ALWAYS, seq(choice('accept_on', 'reject_on', 'sync_accept_on', 'sync_reject_on'), '(', $.expression_or_dist, ')', $.property_expr)),
    $.property_instance,
    prec('property_expr', seq($.clocking_event, $.property_expr))
  ),

  property_case_item: $ => choice(
    seq(commaSep1($.expression_or_dist), ':', $.property_expr, ';'),
    seq('default', optional(':'), $.property_expr, ';')
  ),

  sequence_declaration: $ => seq(
    'sequence',
    field('name', $.sequence_identifier),
    optseq('(', optional($.sequence_port_list), ')'), ';',
    repeat($.assertion_variable_declaration),
    $.sequence_expr, optional(';'),
    enclosing('endsequence', $.sequence_identifier)
  ),

  sequence_port_list: $ => commaSep1($.sequence_port_item),

  sequence_port_item: $ => seq(
    repeat($.attribute_instance),
    optseq('local', optional($.sequence_lvar_port_direction)),
    optional($.sequence_formal_type), // Contains empty string branch $.data_type_or_implicit
    $.formal_port_identifier,
    repeat($._variable_dimension),
    optseq('=', $._sequence_actual_arg)
  ),

  sequence_lvar_port_direction: $ => choice('input', 'inout', 'output'),

  sequence_formal_type: $ => choice(
    $.data_type_or_implicit,
    'sequence',
    'untyped'
  ),

  sequence_expr: $ => choice(
    repseq1($.cycle_delay_range, $.sequence_expr),
    seq($.sequence_expr, repseq1($.cycle_delay_range, $.sequence_expr)),
    seq($.expression_or_dist, optional($._boolean_abbrev)),
    prec('sequence_expr', seq($.sequence_instance, optional($.sequence_abbrev))),
    seq('(', $.sequence_expr, repseq(',', $._sequence_match_item), ')', optional($.sequence_abbrev)),
    prec.left(PREC.PROP_SEQ_AND, seq($.sequence_expr, 'and', $.sequence_expr)),
    prec.left(PREC.SEQ_INTERSECT, seq($.sequence_expr, 'intersect', $.sequence_expr)),
    prec.left(PREC.PROP_SEQ_OR, seq($.sequence_expr, 'or', $.sequence_expr)),
    seq('first_match', '(', $.sequence_expr, repseq(',', $._sequence_match_item), ')'),
    prec.right(PREC.SEQ_THROUGHOUT, seq($.expression_or_dist, 'throughout', $.sequence_expr)),
    prec.left(PREC.SEQ_WITHIN, seq($.sequence_expr, 'within', $.sequence_expr)),
    seq($.clocking_event, $.sequence_expr)
  ),

  cycle_delay_range: $ => choice(
    seq('##',
      choice(
        $.constant_primary,
        seq('[', $.cycle_delay_const_range_expression, ']')
      )),
    '##[*]',
    '##[+]'
  ),

  sequence_method_call: $ => seq($.sequence_instance, '.', $.method_identifier),

  _sequence_match_item: $ => choice(
    $.operator_assignment,
    $.inc_or_dec_expression,
    $.subroutine_call
  ),

  sequence_instance: $ => seq(
    $.ps_or_hierarchical_sequence_identifier,
    optseq('(', optional($.sequence_list_of_arguments), ')')
  ),

  sequence_list_of_arguments: $ => list_of_args($, 'sequence_list_of_arguments', $._sequence_actual_arg),

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

  assertion_variable_declaration: $ => seq($.var_data_type, $.list_of_variable_decl_assignments, ';'),


// ** A.2.11 Covergroup declarations
  covergroup_declaration: $ => seq(
    'covergroup',
    choice(
      seq(
        field('name', $.covergroup_identifier),
        optseq('(', optional($.tf_port_list), ')'),
        optional($.coverage_event),
      ),
      seq('extends', field('parent', $.covergroup_identifier))
    ),
    ';',
    repeat($.coverage_spec_or_option),
    enclosing('endgroup', $.covergroup_identifier),
  ),

  coverage_spec_or_option: $ => seq(
    repeat($.attribute_instance),
    choice(
      $._coverage_spec,
      seq($.coverage_option, ';')
    ),
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

  block_event_expression: $ => prec('block_event_expression', choice(
    prec.left(seq($.block_event_expression, 'or', $.block_event_expression)),
    seq('begin', $.hierarchical_btf_identifier),
    seq('end', $.hierarchical_btf_identifier)
  )),

  hierarchical_btf_identifier: $ => choice(
    $.hierarchical_tf_identifier,
    $.hierarchical_block_identifier,
    seq(
      optchoice(seq($.hierarchical_identifier, '.'), $.class_scope),
      $.method_identifier
    )
  ),

  cover_point: $ => seq(
    optseq(optional($.data_type_or_implicit), field('name', $.cover_point_identifier), ':'),
    'coverpoint', $.expression,
    optseq('iff', '(', $.expression, ')'),
    $.bins_or_empty
  ),

  bins_or_empty: $ => choice(
    seq('{', repeat($.attribute_instance), repseq($.bins_or_options, ';'), '}'),
    ';'
  ),

  bins_or_options: $ => choice(
    // Branch 1
    $.coverage_option,
    // Branches 2-5
    seq(
      optional('wildcard'), $.bins_keyword, field('name', $.bin_identifier),
      choice(
        // Branches 2-4
        seq(optseq('[', optional($._covergroup_expression), ']'), '=',
          choice(
            seq('{', $.covergroup_range_list, '}', optseq('with', '(', $._with_covergroup_expression, ')')),
            seq($.cover_point_identifier, 'with', '(', $._with_covergroup_expression, ')'),
            $._set_covergroup_expression
          )),
        // Branch 5
        seq(optseq('[', ']'), '=', $.trans_list),
      ),
      optseq('iff', '(', $.expression, ')')
    ),
    // Branches 6-7
    seq($.bins_keyword, field('name', $.bin_identifier),
      choice(
        seq(optseq('[', optional($._covergroup_expression), ']'), '=', 'default'),
        seq('=', 'default', 'sequence')
      ),
      optseq('iff', '(', $.expression, ')')
    )),

  bins_keyword: $ => choice('bins', 'illegal_bins', 'ignore_bins'),

  trans_list: $ => commaSep1(seq('(', $.trans_set, ')')),

  trans_set: $ => sepBy1('=>', $.trans_range_list),

  trans_range_list: $ => seq(
    $.trans_item,
    optseq(choice('[*', '[->', '[='), $.repeat_range, ']')
  ),

  trans_item: $ => $.covergroup_range_list,

  repeat_range: $ => seq(
    $._covergroup_expression, optseq(':', $._covergroup_expression)
  ),

  cover_cross: $ => seq(
    optseq(field('name', $.cross_identifier), ':'),
    'cross',
    $.list_of_cross_items,
    optseq('iff', '(', $.expression, ')'),
    $.cross_body
  ),

  list_of_cross_items: $ => seq($._cross_item, ',', commaSep1($._cross_item)),

  _cross_item: $ => choice(
    $.cover_point_identifier,
    $.variable_identifier
  ),

  cross_body: $ => choice(
    seq('{', repeat($.cross_body_item), '}'),
    ';'
  ),

  cross_body_item: $ => choice(
    $.function_declaration,
    seq($.bins_selection_or_option, ';')
  ),

  bins_selection_or_option: $ => seq(
    repeat($.attribute_instance),
    choice(
      $.coverage_option,
      $.bins_selection
    )
  ),

  bins_selection: $ => seq(
    $.bins_keyword, $.bin_identifier, '=', $.select_expression,
    optseq('iff', '(', $.expression, ')')
  ),

  // Fixed conflicts by keeping numerical precedences on branches that call $.select_expression recursively.
  // The ones that do not, set named precedences and associativity to solve conflicts.
  select_expression: $ => choice(
    $.select_condition,
    prec.left(PREC.UNARY, seq('!', $.select_condition)),
    prec.left(PREC.LOGICAL_AND, seq($.select_expression, '&&', $.select_expression)),
    prec.left(PREC.LOGICAL_OR, seq($.select_expression, '||', $.select_expression)),
    paren_expr($.select_expression),
    seq($.select_expression, 'with', '(', $._with_covergroup_expression, ')', prec.right('select_expression', optseq('matches', $._integer_covergroup_expression))),
    prec('select_expression', $.cross_identifier),
    prec.right('select_expression', seq($._cross_set_expression, optseq('matches', $._integer_covergroup_expression)))
  ),

  select_condition: $ => seq(
    'binsof', '(', $.bins_expression, ')',
    optseq('intersect', '{', $.covergroup_range_list, '}')
  ),

  bins_expression: $ => choice(
    $.variable_identifier,
    seq($.cover_point_identifier, optseq('.', $.bin_identifier))
  ),

  covergroup_range_list: $ => commaSep1($.covergroup_value_range),

  covergroup_value_range: $ => prec('covergroup_value_range', choice(
    $._covergroup_expression,
    seq(
      '[',
      choice(
        seq($._covergroup_expression, ':', $._covergroup_expression),
        seq('$', ':', $._covergroup_expression),
        seq($._covergroup_expression, ':', '$'),
        seq($._covergroup_expression, '+/-', $._covergroup_expression),
        seq($._covergroup_expression, '+%-', $._covergroup_expression)
      ),
      ']'
    ))),

  _with_covergroup_expression: $ => $._covergroup_expression,

  _set_covergroup_expression: $ => $._covergroup_expression,

  _integer_covergroup_expression: $ => choice(
    $._covergroup_expression,
    '$'
  ),

  _cross_set_expression: $ => $._covergroup_expression,

  _covergroup_expression: $ => $.expression,


// ** A.2.12 Let declarations
  let_declaration: $ => seq(
    'let', field('name', $.let_identifier),
    optseq('(', optional($.let_port_list), ')'),
    '=', $.expression, ';'
  ),

  let_identifier: $ => $._identifier,

  let_port_list: $ => commaSep1($.let_port_item),

  let_port_item: $ => seq(
    repeat($.attribute_instance),
    optional($.let_formal_type), // $.let_formal_type contains branch $.data_type_or_implicit which could match empty string
    field('formal_port', $.formal_port_identifier),
    repeat($._variable_dimension),
    optseq('=', $.expression)
  ),

  let_formal_type: $ => choice(
    $.data_type_or_implicit,
    'untyped'
  ),

  let_expression: $ => seq(
    optional($.package_scope),
    $.let_identifier,
    optseq('(', optional($.let_list_of_arguments), ')')
  ),

  let_list_of_arguments: $ => alias($.list_of_arguments, $.let_list_of_arguments),

  let_actual_arg: $ => $.expression, // Unused since $.let_list_of_arguments is aliased


// * A.3 Primitive instances
// ** A.3.1 Primitive instantiation and instances
  gate_instantiation: $ => seq(
    choice(
      seq($.cmos_switchtype, optional($.delay3), commaSep1($.cmos_switch_instance)),
      seq($.mos_switchtype, optional($.delay3), commaSep1($.mos_switch_instance)),
      seq($.enable_gatetype, optional($.drive_strength), optional($.delay3), commaSep1($.enable_gate_instance)),
      seq($.n_input_gatetype, optional($.drive_strength), optional($.delay2), commaSep1($.n_input_gate_instance)),
      seq($.n_output_gatetype, optional($.drive_strength), optional($.delay2), commaSep1($.n_output_gate_instance)),
      seq($.pass_en_switchtype, optional($.delay2), commaSep1($.pass_enable_switch_instance)),
      seq($.pass_switchtype, commaSep1($.pass_switch_instance)),
      seq('pulldown', optional($.pulldown_strength), commaSep1($.pull_gate_instance)),
      seq('pullup', optional($.pullup_strength), commaSep1($.pull_gate_instance))
    ),
    ';'
  ),

  cmos_switch_instance: $ => seq(
    optional($.name_of_instance), '(',
    $.output_terminal, ',',
    $.input_terminal, ',',
    $.ncontrol_terminal, ',',
    $.pcontrol_terminal,
    ')'
  ),

  enable_gate_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    $.output_terminal, ',',
    $.input_terminal, ',',
    $.enable_terminal,
    ')'
  ),

  mos_switch_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    $.output_terminal, ',',
    $.input_terminal, ',',
    $.enable_terminal,
    ')'
  ),

  n_input_gate_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    $.output_terminal, ',',
    commaSep1($.input_terminal),
    ')'
  ),

  n_output_gate_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    commaSep1($.output_terminal), ',',
    $.input_terminal,
    ')'
  ),

  pass_switch_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    $.inout_terminal, ',',
    $.inout_terminal,
    ')'
  ),

  pass_enable_switch_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    $.inout_terminal, ',',
    $.inout_terminal, ',',
    $.enable_terminal,
    ')'
  ),

  pull_gate_instance: $ => seq(
    optional($.name_of_instance),
    '(',
    $.output_terminal,
    ')'
  ),

// ** A.3.2 Primitive strengths
  pulldown_strength: $ => choice(
    seq('(', $.strength0, ',', $.strength1, ')'),
    seq('(', $.strength1, ',', $.strength0, ')'),
    seq('(', $.strength0, ')')
  ),

  pullup_strength: $ =>choice(
    seq(',', $.strength0, ',', $.strength1, ')'),
    seq(',', $.strength1, ',', $.strength0, ')'),
    seq(',', $.strength1, ')')
  ),


// ** A.3.3 Primitive terminals
  enable_terminal: $ => $.expression,

  inout_terminal: $ => $.net_lvalue,

  input_terminal: $ => $.expression,

  ncontrol_terminal: $ => $.expression,

  output_terminal: $ => $.net_lvalue,

  pcontrol_terminal: $ => $.expression,


// ** A.3.4 Primitive gate and switch types
  cmos_switchtype: $ => choice('cmos', 'rcmos'),

  enable_gatetype: $ => choice('bufif0', 'bufif1', 'notif0', 'notif1'),

  mos_switchtype: $ => choice('nmos', 'pmos', 'rnmos', 'rpmos'),

  n_input_gatetype: $ => choice('and', 'nand', 'or', 'nor', 'xor', 'xnor'),

  n_output_gatetype: $ => choice('buf', 'not'),

  pass_en_switchtype: $ => choice('tranif0', 'tranif1', 'rtranif1', 'rtranif0'),

  pass_switchtype: $ => choice('tran', 'rtran'),


// * A.4 Instantiations
// ** A.4.1 Instantiation
// *** A.4.1.1 Module instantiation
  module_instantiation: $ => seq(
    field('instance_type', $.module_identifier),
    optional($.parameter_value_assignment),
    commaSep1($.hierarchical_instance),
    ';'
  ),

  parameter_value_assignment: $ => seq(
    '#', '(', optional($.list_of_parameter_value_assignments), ')'
  ),

  // The basic $.ordered_parameter_assignment branch would be: commaSep1($.ordered_parameter_assignment)
  // Current entry also supports empty positional arguments for parameters
  list_of_parameter_value_assignments: $ => choice(
    seq(choice(',', $.ordered_parameter_assignment), repeat(choice(',', (seq(',', $.ordered_parameter_assignment))))),
    commaSep1($.named_parameter_assignment),
  ),

  ordered_parameter_assignment: $ => $.param_expression,

  // Optional $_directives out of LRM (supports ifdefs in parameter lists)
  named_parameter_assignment: $ => seq(
    optional($._directives), '.', $.parameter_identifier, '(', optional($.param_expression), ')'
  ),

  hierarchical_instance: $ => prec('hierarchical_instance', seq(
    $.name_of_instance, '(', optional($.list_of_port_connections), ')'
  )),

  name_of_instance: $ => seq(
    field('instance_name', $.instance_identifier),
    repeat($.unpacked_dimension)
  ),

  // The basic $.ordered_port_connection branch would be: commaSep1($.ordered_port_connection)
  // Current entry also supports empty positional arguments for ports
  list_of_port_connections: $ => choice(
    seq(choice(',', $.ordered_port_connection), repeat(choice(',', (seq(',', $.ordered_port_connection))))),
    commaSep1($.named_port_connection)
  ),

  ordered_port_connection: $ => seq(
    repeat($.attribute_instance),
    $.expression // Removed optional to avoid matching empty string
  ),

  // Optional $_directives out of LRM (supports ifdefs in parameter lists)
  named_port_connection: $ => seq(
    repeat($.attribute_instance),
    choice(
      seq(optional($._directives), '.', field('port_name', $.port_identifier), optseq('(', optional(field('connection', $.expression)), ')')),
      '.*'
    )
  ),


// *** A.4.1.2 Interface instantiation
  interface_instantiation: $ => prec('interface_instantiation',
    alias($.module_instantiation, $.interface_instantiation)
  ),


// *** A.4.1.3 Program instantiation
  program_instantiation: $ => prec('program_instantiation',
    alias($.module_instantiation, $.program_instantiation)
  ),


// *** A.4.1.4 Checker instantiation
  checker_instantiation: $ => prec('checker_instantiation', seq(
    field('instance_type', $.ps_checker_identifier),
    $.name_of_instance,
    '(', optional($.list_of_checker_port_connections), ')',
    ';'
  )),

  list_of_checker_port_connections: $ => choice(
    commaSep1($.ordered_checker_port_connection),
    commaSep1($.named_checker_port_connection)
  ),

  ordered_checker_port_connection: $ => seq( // Similar to $.ordered_port_connection
    repeat($.attribute_instance),
    $._property_actual_arg // Removed optional to avoid matching empty string
  ),

  named_checker_port_connection: $ => seq( // Similar to $.named_port_connection
    repeat($.attribute_instance),
    choice(
      seq(optional($._directives), '.', field('port_name', $.formal_port_identifier), optseq('(', optional(field('connection', $._property_actual_arg)), ')')),
      '.*'
    )
  ),


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

  genvar_initialization: $ => prec('genvar_initialization', seq(
    optional('genvar'),
    $.genvar_identifier,
    '=',
    $.constant_expression
  )),

  genvar_iteration: $ => choice(
    seq($.genvar_identifier, $.assignment_operator, $._genvar_expression),
    seq($.inc_or_dec_operator, $.genvar_identifier),
    seq($.genvar_identifier, $.inc_or_dec_operator)
  ),

  conditional_generate_construct: $ => choice(
    $.if_generate_construct,
    $.case_generate_construct
  ),

  if_generate_construct: $ => prec.right(seq(
    'if', '(', $.constant_expression, ')', $.generate_block,
    optseq('else', $.generate_block)
  )),

  case_generate_construct: $ => prec.right(seq(
    'case', '(', $.constant_expression, ')', $.case_generate_item,
    repeat($.case_generate_item),
    'endcase'
  )),

  case_generate_item: $ => choice(
    seq(commaSep1($.constant_expression), ':', $.generate_block),
    seq('default', optional(':'), $.generate_block)
  ),

  generate_block: $ => choice(
    $._generate_item,
    seq(
      optseq(field('name', $.generate_block_identifier), ':'),
      'begin',
      optseq(':', field('name', $.generate_block_identifier)),
      repeat($._generate_item),
      'end',
      optseq(':', field('name', $.generate_block_identifier))
    )
  ),

  _generate_item: $ => choice(
    $._module_or_generate_item,
    $._interface_or_generate_item,
    // alias($.checker_or_generate_item, $.checker_item)
  ),


// * A.5 UDP declaration and instantiation
// ** A.5.1 UDP declaration
  udp_nonansi_declaration: $ => seq(
    repeat($.attribute_instance), 'primitive', $.udp_identifier, '(', $.udp_port_list, ')', ';'
  ),

  udp_ansi_declaration: $ => seq(
    repeat($.attribute_instance), 'primitive', $.udp_identifier, '(', $.udp_declaration_port_list, ')', ';'
  ),

  udp_declaration: $ => choice(
    seq(
      $.udp_nonansi_declaration,
      repeat1($.udp_port_declaration),
      $._udp_body,
      enclosing('endprimitive', $.udp_identifier)
    ),
    seq(
      $.udp_ansi_declaration,
      $._udp_body,
      enclosing('endprimitive', $.udp_identifier)
    ),
    seq('extern', $.udp_nonansi_declaration),
    seq('extern', $.udp_ansi_declaration),
    seq(
      repeat($.attribute_instance),
      'primitive',
      $.udp_identifier,
      '(', '.*', ')', ';',
      repeat($.udp_port_declaration),
      $._udp_body,
      enclosing('endprimitive', $.udp_identifier)
    )
  ),

// ** A.5.2 UDP ports
  udp_port_list: $ => seq(
    $.output_port_identifier, ',', commaSep1($.input_port_identifier)
  ),

  udp_declaration_port_list: $ => seq(
    $.udp_output_declaration, ',', commaSep1($.udp_input_declaration)
  ),

  udp_port_declaration: $ => seq(
    choice(
      $.udp_output_declaration,
      $.udp_input_declaration,
      $.udp_reg_declaration
    ),
    ';'
  ),

  udp_output_declaration: $ => seq(
    repeat($.attribute_instance), 'output',
    choice(
      $.port_identifier,
      seq('reg', $.port_identifier, optseq('=', $.constant_expression))
    )
  ),

  udp_input_declaration: $ => seq(
    repeat($.attribute_instance), 'input', $.list_of_udp_port_identifiers
  ),

  udp_reg_declaration: $ => seq(
    repeat($.attribute_instance), 'reg', $.variable_identifier
  ),


// ** A.5.3 UDP body
  _udp_body: $ => choice(
    $.combinational_body,
    $.sequential_body
  ),

  combinational_body: $ => seq(
    'table', repeat1($.combinational_entry), 'endtable'
  ),

  combinational_entry: $ => seq($.level_input_list, ':', $.output_symbol, ';'),

  sequential_body: $ => seq(
    optional($.udp_initial_statement), 'table', repeat1($.sequential_entry), 'endtable'
  ),

  udp_initial_statement: $ => seq(
    'initial', $.output_port_identifier, '=', $.init_val, ';'
  ),

  init_val: $ => choice(
    "1'b0", "1'b1", "1'bx", "1'bX", "1'B0", "1'B1", "1'Bx", "1'BX", "1", "0"
  ),

  sequential_entry: $ => seq(
    $._seq_input_list, ':', $._current_state, ':', $.next_state, ';'
  ),

  _seq_input_list: $ => choice(
    $.level_input_list,
    $.edge_input_list
  ),

  level_input_list: $ => repeat1($.level_symbol),

  edge_input_list: $ => seq(
    repeat($.level_symbol), $.edge_indicator, repeat($.level_symbol)
  ),

  edge_indicator: $ => choice(
    seq('(', $.level_symbol, $.level_symbol, ')'),
    $.edge_symbol
  ),

  _current_state: $ => $.level_symbol,

  next_state: $ => choice($.output_symbol, '-'),

  output_symbol: $ => /[01xX]/,

  level_symbol: $ => /[01xX?bB]/,

  edge_symbol: $ => /[rRfFpPnN*]/,


// ** A.5.4 UDP instantiation
  udp_instantiation: $ => seq(
    // field('instance_type', $.udp_identifier), // TODO: For some reason results in parse errors with tree-sitter 0.22.6, in core/instantiation/user_defined_primitives
    $.udp_identifier,
    optional($.drive_strength),
    optional($.delay2),
    prec.dynamic(-1, commaSep1($.udp_instance)), // Give $.hierarchical_instance and $.module_instantiation higher priority
    ';'
  ),

  udp_instance: $ => seq(
    optional($.name_of_instance),
    '(', $.output_terminal, ',', commaSep1($.input_terminal), ')'
  ),


// * A.6 Behavioral statements
// ** A.6.1 Continuous assignment and net alias statements
  continuous_assign: $ => seq(
    'assign',
    choice(
      seq(optional($.drive_strength), optional($.delay3), $.list_of_net_assignments),
      seq(optional($.delay_control), $.list_of_variable_assignments)
    ) ,
    ';'
  ),

  list_of_net_assignments: $ => commaSep1($.net_assignment),

  list_of_variable_assignments: $ => prec('list_of_variable_assignments', commaSep1($.variable_assignment)),

  net_alias: $ => prec.right(PREC.ASSIGN, seq(
    'alias', $.net_lvalue, '=', sepBy1('=', $.net_lvalue), ';'
  )),

  net_assignment: $ => seq($.net_lvalue, '=', $.expression),


// ** A.6.2 Procedural blocks and assignments
  initial_construct: $ => seq('initial', $.statement_or_null),

  always_construct: $ => seq($.always_keyword, $.statement),

  always_keyword: $ => choice('always', 'always_comb', 'always_latch', 'always_ff'),

  final_construct: $ => seq('final', $.function_statement),

  blocking_assignment: $ => choice(
    seq($.variable_lvalue, '=', $.delay_or_event_control, $.expression),
    seq($.nonrange_variable_lvalue, '=', $.dynamic_array_new),
    seq(
      optchoice(seq($.implicit_class_handle, '.'), $.class_scope, $.package_scope),
      $.hierarchical_variable_identifier, optional($.select), '=', $.class_new
    ),
    $.operator_assignment,
    $.inc_or_dec_expression,
  ),

  operator_assignment: $ => seq($.variable_lvalue, $.assignment_operator, $.expression),

  assignment_operator: $ => choice(
    '=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=', '<<<=', '>>>='
  ),

  nonblocking_assignment: $ => seq(
    $.variable_lvalue,
    '<=',
    optional($.delay_or_event_control),
    $.expression
  ),

  procedural_continuous_assignment: $ => prec('procedural_continuous_assignment', choice(
    seq('assign', $.variable_assignment),
    seq('deassign', $.variable_lvalue),
    prec.dynamic(1, seq('force', $.variable_assignment)),
    seq('force', $.net_assignment),
    prec.dynamic(1, seq('release', $.variable_lvalue)),
    seq('release', $.net_lvalue)
  )),

  variable_assignment: $ => seq($.variable_lvalue, '=', $.expression),


// ** A.6.3 Parallel and sequential blocks
  action_block: $ => prec('action_block', choice(
    $.statement_or_null,
    seq(optional($.statement), 'else', $.statement_or_null)
  )),

  seq_block: $ => seq(
    'begin', optseq(':', $.block_identifier),
    repeat($.block_item_declaration),
    repeat($.statement_or_null),
    enclosing('end', $.block_identifier)
  ),

  par_block: $ => seq(
    'fork', optseq(':', $.block_identifier),
    repeat($.block_item_declaration),
    repeat($.statement_or_null),
    enclosing($.join_keyword, $.block_identifier)
  ),

  join_keyword: $ => choice('join', 'join_any', 'join_none'),


// ** A.6.4 Statements
  statement_or_null: $ => prec('statement_or_null', choice(
    $.statement,
    seq(repeat($.attribute_instance), ';')
  )),

  statement: $ => seq(
    optseq(field('block_name', $.block_identifier), ':'),
    repeat($.attribute_instance),
    $.statement_item
  ),

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
    $.procedural_timing_control_statement,
    $.seq_block,
    $.wait_statement,
    $._procedural_assertion_statement,
    prec.dynamic(-1, seq($.clocking_drive, ';')), // NBA > clocking drive (outside of a clocking block)
    $.randsequence_statement,
    $.randcase_statement,
    $.expect_property_statement,
    $._directives, // Out of LRM
  )),

  function_statement: $ => $.statement,

  function_statement_or_null: $ => choice(
    $.function_statement,
    seq(repeat($.attribute_instance), ';')
  ),


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

  delay_control: $ => seq(
    '#',
    choice(
      $.delay_value,
      seq('(', $.mintypmax_expression, ')'),
      $.text_macro_usage, // Out of LRM
    )
  ),

  event_control: $ => choice(
    $.clocking_event,
    seq('@', '*'),
    seq('@', '(', '*', ")")
  ),

  clocking_event: $ => seq(
    '@',
    choice(
      $.ps_identifier,
      $.hierarchical_identifier,
      seq('(', $.event_expression, ')')
    )
  ),

  event_expression: $ => prec('event_expression', choice(
    prec.dynamic(1, seq(optional($.edge_identifier), $.expression, optseq('iff', $.expression))),
    seq($.sequence_instance, optseq('iff', $.expression)),
    prec.left(seq($.event_expression, 'or', $.event_expression)),
    prec.left('event_expression', seq($.event_expression, ',', $.event_expression)),
    seq('(', $.event_expression, ')')
  )),

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
    seq('wait_order', '(', commaSep1($.hierarchical_identifier), ')', $.action_block)
  ),

  event_trigger: $ => choice(
    seq('->', $.hierarchical_event_identifier, optional($.nonrange_select), ';'),
    seq('->>', optional($.delay_or_event_control), $.hierarchical_event_identifier, optional($.nonrange_select), ';')
  ),

  disable_statement: $ => choice(
    seq('disable', $.hierarchical_task_identifier, ';'),
    seq('disable', $.hierarchical_block_identifier, ';'),
    seq('disable', 'fork', ';')
  ),


// ** A.6.6 Conditional statements
  conditional_statement: $ => prec.right(seq(
    optional($.unique_priority),
    'if', '(', $.cond_predicate, ')', $.statement_or_null,
    repseq('else', 'if', '(', $.cond_predicate, ')', $.statement_or_null),
    optseq('else', $.statement_or_null)
  )),

  unique_priority: $ => choice('unique', 'unique0', 'priority'),

  cond_predicate: $ => prec(PREC.CONDITIONAL, sepBy1('&&&', $._expression_or_cond_pattern)),

  _expression_or_cond_pattern: $ => choice(
    $.expression,
    $.cond_pattern
  ),

  cond_pattern: $ => seq($.expression, 'matches', $.pattern),


// ** A.6.7 Case statements
  case_statement: $ => prec.right(seq(
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
  )),

  case_keyword: $ => choice('case', 'casez', 'casex'),

  case_expression: $ => $.expression,

  case_item: $ => choice(
    seq(commaSep1($.case_item_expression), ':', $.statement_or_null),
    seq('default', optional(':'), $.statement_or_null)
  ),

  case_pattern_item: $ => choice(
    seq($.pattern, optseq('&&&', $.expression), ':', $.statement_or_null),
    seq('default', optional(':'), $.statement_or_null)
  ),

  case_inside_item: $ => choice(
    seq($.range_list, ':', $.statement_or_null),
    seq('default', optional(':'), $.statement_or_null)
  ),

  case_item_expression: $ => $.expression,

  randcase_statement: $ => seq(
    'randcase', repeat1($.randcase_item), 'endcase'
  ),

  randcase_item: $ => seq($.expression, ':', $.statement_or_null),

  range_list: $ => commaSep1($.value_range),

  value_range: $ => prec('value_range', choice(
    $.expression,
    seq('[',
      choice(
        seq($.expression, ':', $.expression),
        seq('$', ':', $.expression),
        seq($.expression, ':', '$'),
        seq($.expression, '+/-', $.expression),
        seq($.expression, '+%-', $.expression)
      ),
      ']'
    )
  )),


// *** A.6.7.1 Patterns
  pattern: $ => prec(PREC.MATCHES, choice(
    paren_expr($.pattern),
    seq('.', $.variable_identifier),
    '.*',
    $.constant_expression,
    seq('tagged', $.member_identifier, optional($.pattern)),
    seq('\'{', commaSep1($.pattern), '}'),
    seq('\'{', commaSep1(seq($.member_identifier, ':', $.pattern)), '}')
  )),

  assignment_pattern: $ => seq(
    '\'{',
    choice(
      commaSep1($.expression),
      commaSep1(seq($._structure_pattern_key, ':', $.expression)),
      commaSep1(seq($._array_pattern_key, ':', $.expression)),
      seq($.constant_expression, '{', commaSep1($.expression), '}')
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

  _assignment_pattern_expression_type: $ => prec('_assignment_pattern_expression_type', choice(
    $.ps_type_identifier,
    $.ps_parameter_identifier,
    $.integer_atom_type,
    $.type_reference
  )),

  _constant_assignment_pattern_expression: $ => prec('_constant_assignment_pattern_expression', $.assignment_pattern_expression),

  assignment_pattern_net_lvalue: $ => seq('\'{', commaSep1($.net_lvalue), '}'),

  assignment_pattern_variable_lvalue: $ => seq('\'{', commaSep1($.variable_lvalue), '}'),


// ** A.6.8 Looping statements
  loop_statement: $ => choice(
    seq('forever', $.statement_or_null),
    seq('repeat', '(', $.expression, ')', $.statement_or_null),
    seq('while', '(', $.expression, ')', $.statement_or_null),
    seq(
      'for',
      '(', optional($.for_initialization), ';', optional($.expression), ';', optional($.for_step), ')',
      $.statement_or_null
    ),
    seq('do', $.statement_or_null, 'while', '(', $.expression, ')', ';'),
    seq(
      'foreach',
      '(', $.ps_or_hierarchical_array_identifier, '[', optional($.loop_variables), ']', ')',
      $.statement
    )
  ),

  for_initialization: $ => choice(
    $.list_of_variable_assignments,
    commaSep1($.for_variable_declaration)
  ),

  for_variable_declaration: $ => prec.left(seq(
    optional('var'), $.data_type,
    commaSep1(seq($.variable_identifier, '=', $.expression))
  )),

  for_step: $ => commaSep1($._for_step_assignment),

  _for_step_assignment: $ => choice(
    $.operator_assignment,
    $.inc_or_dec_expression,
    $.function_subroutine_call
  ),

  // Modified to avoid matching empty string
  loop_variables: $ => seq(
    $.index_variable_identifier,
    repseq(',', optional($.index_variable_identifier))
  ),


// ** A.6.9 Subroutine call statements
  subroutine_call_statement: $ => prec('subroutine_call_statement', choice(
    seq($.subroutine_call, ';'),
    seq('void\'', '(', $.function_subroutine_call, ')', ';'),
    $.severity_system_task,   // Out of LRM: allow $fatal/$error/$warning/$info in procedural code
    $.simulation_control_task // Out of LRM: allow $stop/$finish/$exit in procedural code
  )),


// ** A.6.10 Assertion statements
  _assertion_item: $ => choice(
    $.concurrent_assertion_item,
    $.deferred_immediate_assertion_item
  ),

  deferred_immediate_assertion_item: $ => prec('deferred_immediate_assertion_item', seq(
    optseq($.block_identifier, ':'),
    $._deferred_immediate_assertion_statement
  )),

  _procedural_assertion_statement: $ => prec('_procedural_assertion_statement', choice(
    $._concurrent_assertion_statement,
    $._immediate_assertion_statement,
    $.checker_instantiation
  )),

  _immediate_assertion_statement: $ => prec('_immediate_assertion_statement', choice(
    $._simple_immediate_assertion_statement,
    $._deferred_immediate_assertion_statement
  )),

  _simple_immediate_assertion_statement: $ => choice(
    $.simple_immediate_assert_statement,
    $.simple_immediate_assume_statement,
    $.simple_immediate_cover_statement
  ),

  _deferred_immediate_assertion_statement: $ => choice(
    $.deferred_immediate_assert_statement,
    $.deferred_immediate_assume_statement,
    $.deferred_immediate_cover_statement
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

  deferred_immediate_assert_statement: $ => seq(
    'assert', choice('#0', 'final'), '(', $.expression, ')', $.action_block
  ),

  deferred_immediate_assume_statement: $ => seq(
    'assume', choice('#0', 'final'), '(', $.expression, ')', $.action_block
  ),

  deferred_immediate_cover_statement: $ => seq(
    'cover', choice('#0', 'final'), '(', $.expression, ')', $.statement_or_null
  ),


// ** A.6.11 Clocking block
  clocking_declaration: $ => choice(
    seq(
      optional('default'), 'clocking',
      field('name', optional($.clocking_identifier)),
      $.clocking_event, ';',
      repeat($.clocking_item),
      enclosing('endclocking', $.clocking_identifier)
    ),
    seq(
      'global', 'clocking',
      field('name', optional($.clocking_identifier)),
      $.clocking_event, ';',
      enclosing('endclocking', $.clocking_identifier)
    )
  ),

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
    'inout'
  ),

  list_of_clocking_decl_assign: $ => commaSep1($.clocking_decl_assign),

  clocking_decl_assign: $ => seq($.signal_identifier, optseq('=', $.expression)),

  clocking_skew: $ => choice(
    seq($.edge_identifier, optional($.delay_control)),
    $.delay_control
  ),

  clocking_drive: $ => seq(
    $.clockvar_expression, '<=', optional($.cycle_delay), $.expression
  ),

  cycle_delay: $ => seq(
    '##',
    choice(
      $.integral_number,
      $._identifier,
      seq('(', $.expression, ')')
    )
  ),

  clockvar: $ => $.hierarchical_identifier,

  clockvar_expression: $ => seq(
    $.clockvar,
    optional($.select)
  ),


// ** A.6.12 Randsequence
  randsequence_statement: $ => seq(
    'randsequence', '(', optional($.rs_production_identifier), ')',
    repeat1($.rs_production),
    'endsequence'
  ),

  rs_production: $ => seq(
    optional($.data_type_or_void),
    $.rs_production_identifier,
    optseq('(', $.tf_port_list, ')'),
    ':',
    sepBy1('|', $.rs_rule),
    ';'
  ),

  rs_rule: $ => seq(
    $.rs_production_list, optseq(':=', $.rs_weight_specification, optional($.rs_code_block))
  ),

  rs_production_list: $ => choice(
    repeat1($.rs_prod),
    seq('rand', 'join', optseq('(', $.expression, ')'), $.rs_production_item, repeat1($.rs_production_item))
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
    $.rs_production_identifier, optseq('(', optional($.list_of_arguments), ')')
  ),

  rs_if_else: $ => prec.right(seq(
    'if', '(', $.expression, ')', $.rs_production_item, optseq('else', $.rs_production_item)
  )),

  rs_repeat: $ => seq(
    'repeat', '(', $.expression, ')', $.rs_production_item
  ),

  rs_case: $ => prec.right(seq(
    'case', '(', $.case_expression, ')', repeat1($.rs_case_item), 'endcase'
  )),

  rs_case_item: $ => choice(
    seq(commaSep1($.case_item_expression), ":", $.rs_production_item, ';'),
    seq('default', optional(':'), $.rs_production_item, ';')
  ),


// * A.7 Specify section
// ** A.7.1 Specify block declaration
  specify_block: $ => seq(
    'specify',
    repeat($.specify_item),
    'endspecify'
  ),

  specify_item: $ => choice(
    $.specparam_declaration,
    $.pulsestyle_declaration,
    $.showcancelled_declaration,
    $.path_declaration,
    $.system_timing_check
  ),

  pulsestyle_declaration: $ => seq(
    choice('pulsestyle_onevent', 'pulsestyle_ondetect'),
    $.list_of_path_outputs,
    ';'
  ),

  showcancelled_declaration: $ => seq(
    choice('showcancelled', 'noshowcancelled'),
    $.list_of_path_outputs,
    ';'
  ),


// ** A.7.2 Specify path declarations
  path_declaration: $ => seq(
    choice(
      $.simple_path_declaration,
      $.edge_sensitive_path_declaration,
      $.state_dependent_path_declaration
    ),
    ';'
  ),

  simple_path_declaration: $ => seq(
    choice($.parallel_path_description, $.full_path_description),
    '=',
    $.path_delay_value
  ),

  parallel_path_description: $ => seq(
    '(',
    $.specify_input_terminal_descriptor,
    optional($.polarity_operator),
    '=>',
    $.specify_output_terminal_descriptor,
    ')'
  ),

  full_path_description: $ => seq(
    '(',
    $.list_of_path_inputs,
    optional($.polarity_operator),
    '*>',
    $.list_of_path_outputs,
    ')'
  ),

  edge_sensitive_path_declaration: $ => seq(
    choice(
      $.parallel_edge_sensitive_path_description,
      $.full_edge_sensitive_path_description
    ),
    '=',
    $.path_delay_value
  ),

  parallel_edge_sensitive_path_description: $ => seq(
    '(',
    optional($.edge_identifier),
    $.specify_input_terminal_descriptor,
    optional($.polarity_operator),
    '=>',
    choice(
      seq('(', $.specify_output_terminal_descriptor, optional($.polarity_operator), ':', $.data_source_expression, ')'),
      $.specify_output_terminal_descriptor,
    ),
    ')'
  ),

  full_edge_sensitive_path_description: $ => seq(
    '(',
    optional($.edge_identifier),
    $.list_of_path_inputs,
    optional($.polarity_operator),
    '*>',
    choice(
      seq('(', $.list_of_path_outputs, optional($.polarity_operator), ':', $.data_source_expression, ')'),
      $.list_of_path_outputs,
    ),
    ')'
  ),

  state_dependent_path_declaration: $ => choice(
    seq('if', '(', $.module_path_expression, ')', choice($.simple_path_declaration, $.edge_sensitive_path_declaration)),
    seq('ifnone', $.simple_path_declaration)
  ),

  data_source_expression: $ => $.expression,

  edge_identifier: $ => choice('posedge', 'negedge', 'edge'),

  polarity_operator: $ => choice('+', '-'),


// ** A.7.3 Specify block terminals
  list_of_path_inputs: $ => commaSep1($.specify_input_terminal_descriptor),

  list_of_path_outputs: $ => commaSep1($.specify_output_terminal_descriptor),

  specify_input_terminal_descriptor: $ => seq(
    $.input_identifier, optseq('[', $._constant_range_expression, ']')
  ),

  specify_output_terminal_descriptor: $ => seq(
    $.output_identifier, optseq('[', $._constant_range_expression, ']')
  ),

  input_identifier: $ => choice(
    $.input_port_identifier,
    $.inout_port_identifier,
    seq($.interface_identifier, '.', $.port_identifier)
  ),

  output_identifier: $ => choice(
    $.output_port_identifier,
    $.inout_port_identifier,
    seq($.interface_identifier, '.', $.port_identifier)
  ),


// ** A.7.4 Specify path delays
  path_delay_value: $ => choice(
    $.list_of_path_delay_expressions,
    seq('(', $.list_of_path_delay_expressions, ')')
  ),

  list_of_path_delay_expressions: $ => choice(
    $.t_path_delay_expression,
    seq($.trise_path_delay_expression, ',', $.tfall_path_delay_expression),
    seq($.trise_path_delay_expression, ',', $.tfall_path_delay_expression, ',', $.tz_path_delay_expression),
    seq(
      $.t01_path_delay_expression, ',', $.t10_path_delay_expression, ',', $.t0z_path_delay_expression, ',',
      $.tz1_path_delay_expression, ',', $.t1z_path_delay_expression, ',', $.tz0_path_delay_expression
    ),
    seq(
      $.t01_path_delay_expression, ',', $.t10_path_delay_expression, ',', $.t0z_path_delay_expression, ',',
      $.tz1_path_delay_expression, ',', $.t1z_path_delay_expression, ',', $.tz0_path_delay_expression, ',',
      $.t0x_path_delay_expression, ',', $.tx1_path_delay_expression, ',', $.t1x_path_delay_expression, ',',
      $.tx0_path_delay_expression, ',', $.txz_path_delay_expression, ',', $.tzx_path_delay_expression
    )
  ),

  t_path_delay_expression: $ => $.path_delay_expression,

  trise_path_delay_expression: $ => $.path_delay_expression,

  tfall_path_delay_expression: $ => $.path_delay_expression,

  tz_path_delay_expression: $ => $.path_delay_expression,

  t01_path_delay_expression: $ => $.path_delay_expression,

  t10_path_delay_expression: $ => $.path_delay_expression,

  t0z_path_delay_expression: $ => $.path_delay_expression,

  tz1_path_delay_expression: $ => $.path_delay_expression,

  t1z_path_delay_expression: $ => $.path_delay_expression,

  tz0_path_delay_expression: $ => $.path_delay_expression,

  t0x_path_delay_expression: $ => $.path_delay_expression,

  tx1_path_delay_expression: $ => $.path_delay_expression,

  t1x_path_delay_expression: $ => $.path_delay_expression,

  tx0_path_delay_expression: $ => $.path_delay_expression,

  txz_path_delay_expression: $ => $.path_delay_expression,

  tzx_path_delay_expression: $ => $.path_delay_expression,

  path_delay_expression: $ => $.constant_mintypmax_expression,


// ** A.7.5 System timing checks
// *** A.7.5.1 System timing check commands
  system_timing_check: $ => choice(
    $.$setup_timing_check,
    $.$hold_timing_check,
    $.$setuphold_timing_check,
    $.$recovery_timing_check,
    $.$removal_timing_check,
    $.$recrem_timing_check,
    $.$skew_timing_check,
    $.$timeskew_timing_check,
    $.$fullskew_timing_check,
    $.$period_timing_check,
    $.$width_timing_check,
    $.$nochange_timing_check
  ),

  $setup_timing_check: $ => seq(
    '$setup',
    '(',
    $.data_event, ',', $.reference_event, ',', $.timing_check_limit, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $hold_timing_check: $ => seq(
    '$hold',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $setuphold_timing_check: $ => seq(
    '$setuphold',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, ',', $.timing_check_limit,
    optseq(',', optional($.notifier),
      optseq(',', optional($.timestamp_condition),
        optseq(',', optional($.timecheck_condition),
          optseq(',', optional($.delayed_reference),
            optseq(',', optional($.delayed_data))
          )
        )
      )
    ),
    ')', ';'
  ),

  $recovery_timing_check: $ => seq(
    '$recovery',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $removal_timing_check: $ => seq(
    '$removal',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $recrem_timing_check: $ => seq(
    '$recrem',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, ',', $.timing_check_limit,
    optseq(',', optional($.notifier),
      optseq(',', optional($.timestamp_condition),
        optseq(',', optional($.timecheck_condition),
          optseq(',', optional($.delayed_reference),
            optseq(',', optional($.delayed_data))
          )
        )
      )
    ),
    ')', ';'
  ),

  $skew_timing_check: $ => seq(
    '$skew',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $timeskew_timing_check: $ => seq(
    '$timeskew',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit,
    optseq(',', optional($.notifier),
      optseq(',', optional($.event_based_flag),
        optseq(',', optional($.remain_active_flag))
      )
    ),
    ')', ';'
  ),

  $fullskew_timing_check: $ => seq(
    '$fullskew',
    '(',
    $.reference_event, ',', $.data_event, ',', $.timing_check_limit, ',', $.timing_check_limit,
    optseq(',', optional($.notifier),
      optseq(',', optional($.event_based_flag),
        optseq(',', optional($.remain_active_flag))
      )
    ),
    ')', ';'
  ),

  $period_timing_check: $ => seq(
    '$period',
    '(',
    $.controlled_reference_event, ',', $.timing_check_limit, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $width_timing_check: $ => seq(
    '$width',
    '(',
    $.controlled_reference_event, ',', $.timing_check_limit, ',', $.threshold, optseq(',', optional($.notifier)),
    ')', ';'
  ),

  $nochange_timing_check: $ => seq(
    '$nochange',
    '(',
    $.reference_event, ',', $.data_event, ',', $.start_edge_offset, ',', $.end_edge_offset, optseq(',', optional($.notifier)),
    ')', ';'
  ),


// *** A.7.5.2 System timing check command arguments
  controlled_reference_event: $ => $.controlled_timing_check_event,

  data_event: $ => $.timing_check_event,

  delayed_data: $ => seq(
    $.terminal_identifier, optional($.constant_mintypmax_expression)
  ),

  delayed_reference: $ => seq(
    $.terminal_identifier, optional($.constant_mintypmax_expression)
  ),

  end_edge_offset: $ => $.mintypmax_expression,

  event_based_flag: $ => $.constant_expression,

  notifier: $ => $.variable_identifier,

  reference_event: $ => $.timing_check_event,

  remain_active_flag: $ => $.constant_mintypmax_expression,

  timecheck_condition: $ => $.mintypmax_expression,

  timestamp_condition: $ => $.mintypmax_expression,

  start_edge_offset: $ => $.mintypmax_expression,

  threshold: $ => $.constant_expression,

  timing_check_limit: $ => $.expression,


// *** A.7.5.3 System timing check event definitions
  timing_check_event: $ => seq(
    optional($.timing_check_event_control),
    $._specify_terminal_descriptor,
    optseq('&&&', $.timing_check_condition)
  ),

  controlled_timing_check_event: $ => seq(
    $.timing_check_event_control,
    $._specify_terminal_descriptor,
    optseq('&&&', $.timing_check_condition)
  ),

  timing_check_event_control: $ => choice(
    'posedge', 'negedge', 'edge', $.edge_control_specifier
  ),

  _specify_terminal_descriptor: $ => choice(
    $.specify_input_terminal_descriptor,
    $.specify_output_terminal_descriptor
  ),

  edge_control_specifier: $ => seq(
    'edge', '[', commaSep1($.edge_descriptor), ']'
  ),

  edge_descriptor: $ => choice(
    '01',
    '10',
    /[xXzZ][01]/, // $.z_or_x, token.immediate(/[01]/),
    /[01][xXzZ]/  // $.zero_or_one, token.immediate(/[xXzZ]/),
  ),

  zero_or_one: $ => /[01]/, // Unused

  z_or_x: $ => /[xXzZ]/, // Unused

  timing_check_condition: $ => choice(
    $.scalar_timing_check_condition,
    seq('(', $.scalar_timing_check_condition, ')')
  ),

  scalar_timing_check_condition: $ => choice(
    $.expression,
    prec.left(PREC.UNARY, seq('~', $.expression)),
    prec.left(PREC.EQUAL, seq($.expression, '==', $.scalar_constant)),
    prec.left(PREC.EQUAL, seq($.expression, '===', $.scalar_constant)),
    prec.left(PREC.EQUAL, seq($.expression, '!=', $.scalar_constant)),
    prec.left(PREC.EQUAL, seq($.expression, '!==', $.scalar_constant))
  ),

  scalar_constant: $ => choice(
    "1'b0", "1'b1", "1'B0", "1'B1", "'b0", "'b1", "'B0", "'B1", "1", "0"
  ),


// * A.8 Expressions
// ** A.8.1 Concatenations
  concatenation: $ => prec('concatenation', seq(
    '{', commaSep1($.expression), '}'
  )),

  constant_concatenation: $ => seq(
    '{', commaSep1($.constant_expression), '}'
  ),

  constant_multiple_concatenation: $ => seq(
    '{', $.constant_expression, $.constant_concatenation, '}'
  ),

  module_path_concatenation: $ => seq(
    '{', commaSep1($.module_path_expression), '}'
  ),

  module_path_multiple_concatenation: $ => seq(
    '{', $.constant_expression, $.module_path_concatenation, '}'
  ),

  multiple_concatenation: $ => seq(
    '{', $.expression, $.concatenation, '}'
  ),

  streaming_concatenation: $ => seq(
    '{', $.stream_operator, optional($.slice_size), $.stream_concatenation, '}'
  ),

  stream_operator: $ => choice('>>', '<<'),

  slice_size: $ => choice($._simple_type, $.constant_expression),

  stream_concatenation: $ => seq(
    '{', commaSep1($.stream_expression), '}'
  ),

  stream_expression: $ => seq(
    $.expression, optseq('with', '[', $.array_range_expression, ']')
  ),

  array_range_expression: $ => seq(
    $.expression,
    optchoice(
      seq( ':', $.expression),
      seq('+:', $.expression),
      seq('-:', $.expression)
    )
  ),

  empty_unpacked_array_concatenation: $ => prec('empty_unpacked_array_concatenation', seq('{', '}')),


// ** A.8.2 Subroutine calls
  constant_function_call: $ => $.function_subroutine_call,

  tf_call: $ => prec.right('tf_call', seq(
    $.ps_or_hierarchical_tf_identifier,
    repeat($.attribute_instance),
    optseq('(', optional($.list_of_arguments), ')')
  )),

  system_tf_call: $ => prec.right(seq(
    $.system_tf_identifier,
    choice(
      prec.dynamic(1, optseq('(', optional($.list_of_arguments), ')')),
      seq('(', $.data_type, optseq(',', $.expression), ')'),
      prec.dynamic(0, seq('(', commaSep1($.expression), optseq(',', $.clocking_event), ')'))
    )
  )),

  subroutine_call: $ => choice(
    prec.dynamic(-1, $.tf_call), // Give $.method_call higher priority
    $.system_tf_call,
    $.method_call,
    seq(optseq('std', '::'), $.randomize_call),
  ),

  function_subroutine_call: $ => $.subroutine_call,

  list_of_arguments: $ => list_of_args($, 'list_of_arguments', $.expression),

  method_call: $ => seq(
    $._method_call_root,
    choice('.', '::'), // :: Out of LRM: Needed to support static method calls
    $.method_call_body
  ),

  method_call_body: $ => prec.right(choice(
    seq(
      field('name', $.method_identifier),
      repeat($.attribute_instance),
      field('arguments', optseq('(', optional($.list_of_arguments), ')'))
    ),
    $._built_in_method_call
  )),

  _built_in_method_call: $ => choice(
    $.array_manipulation_call,
    $.randomize_call,
    $.string_method_call,                    // Out of LRM
    $.enum_method_call,                      // Out of LRM
    $.associative_array_method_call,         // Out of LRM
    $.queue_method_call,                     // Out of LRM
    $.enum_or_associative_array_method_call, // Out of LRM
    $.array_or_queue_method_call,            // Out of LRM
  ),

  array_manipulation_call: $ => prec.right(seq(
    $.array_method_name,
    repeat($.attribute_instance),
    optseq('(', optional($.list_of_arguments), ')'),
    optseq('with', '(', $.expression, ')')
  )),

  randomize_call: $ => prec.right(seq(
    'randomize', repeat($.attribute_instance),
    optseq('(', optchoice($.variable_identifier_list, 'null'), ')'),
    optseq('with', optseq('(', optional($.identifier_list), ')'), $.constraint_block)
  )),

  variable_identifier_list: $ => commaSep1($.variable_identifier),

  identifier_list: $ => commaSep1($._identifier),

  // TODO: Modified with respect to LRM:
  // The $.implicit_class_handle should be matched by $.primary second
  // condition. However there must be some precedences that prevent this from
  // being detected. This workaround might complicate a bit more the parser but
  // seems to work well.
  _method_call_root: $ => choice(
    $.primary,
    prec.dynamic(2, seq($.implicit_class_handle, optional($.select))), // optional($.select) out of LRM
    $.class_type,       // Out of LRM: Added to support calling parameterized static methods
    $.text_macro_usage, // Out of LRM, Added to fix parsing errors in UVM
  ),

  // Different from the LRM. The LRM possibly groups all these identifiers under $.method_identifier.
  // Setting them explicitly helps avoiding potential ambiguities and conflicts.
  array_method_name: $ => choice(
    // 7.12.1 Array locator method
    'find', 'find_index', 'find_first', 'find_first_index', 'find_last', 'find_last_index',
    'min', 'max', 'unique', 'unique_index',
    // 7.12.2 Array ordering methods
    'reverse', 'sort', 'rsort', 'shuffle',
    // 7.12.3 Array reduction methods
    'sum', 'product', 'and', 'or', 'xor',
    // 7.12.5 Array mapping method
    'map'
  ),

  // INFO: The following builtin method call entries are not in the LRM
  string_method_call: $ => prec.right(seq(
    $.string_method_name,
    optseq('(', optional($.list_of_arguments), ')'),
  )),

  string_method_name: $ => choice(
    // 6.16 String data type
    'len', 'putc', 'getc', 'toupper', 'tolower', 'compare', 'icompare',
    'substr', 'atoi', 'atohex', 'atooct', 'atobin', 'atoreal', 'itoa', 'hextoa',
    'octtoa', 'bintoa', 'realtoa'
  ),

  enum_method_call: $ => prec.right(seq(
    $.enum_method_name,
    optseq('(', optional($.list_of_arguments), ')'),
  )),

  enum_method_name: $ => 'name',

  associative_array_method_call: $ => prec.right(seq(
    $.associative_array_method_name,
    optseq('(', optional($.list_of_arguments), ')'),
  )),

  associative_array_method_name: $ => 'exists',

  queue_method_call: $ => prec.right(seq(
    $.queue_method_name,
    optseq('(', optional($.list_of_arguments), ')'),
  )),

  queue_method_name: $ => choice('insert', 'pop_front', 'pop_back', 'push_front', 'push_back'),

  array_or_queue_method_call: $ => prec.right(seq(
    $.array_or_queue_method_name,
    optseq('(', optional($.list_of_arguments), ')'),
  )),

  array_or_queue_method_name: $ => choice('size', 'delete'),

  enum_or_associative_array_method_call: $ => prec.right(seq(
    $.enum_or_associative_array_method_name,
    optseq('(', optional($.list_of_arguments), ')'),
  )),

  enum_or_associative_array_method_name: $ => choice(
    // 6.19.5 Enumerated type methods
    // 7.9 Associative array methods
    'num', 'first', 'last', 'next', 'prev'
  ),


// ** A.8.3 Expressions
  inc_or_dec_expression: $ => prec.left(PREC.UNARY, choice(
    seq($.inc_or_dec_operator, repeat($.attribute_instance), $.variable_lvalue),
    seq($.variable_lvalue, repeat($.attribute_instance), $.inc_or_dec_operator)
  )),

  conditional_expression: $ => conditional_expr($, $.cond_predicate, $.expression),

  constant_expression: $ => choice(
    $.constant_primary,
    $._constant_unary_expression,
    $._constant_binary_expression,
    $._constant_conditional_expression,
    $.text_macro_usage, // Out of LRM
  ),

  constant_mintypmax_expression: $ => seq(
    $.constant_expression,
    optseq(':', $.constant_expression, ':', $.constant_expression)
  ),

  constant_param_expression: $ => prec('constant_param_expression', choice(
    prec.dynamic(1, $.constant_mintypmax_expression),
    prec.dynamic(0, $.data_type),
    '$'
  )),

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

  expression: $ => choice(
    $.primary,
    $._unary_expression,
    $.inc_or_dec_expression,
    $._parenthesized_expression,
    $._binary_expression,
    $.conditional_expression,
    $.inside_expression,
    $.tagged_union_expression,
    $.text_macro_usage, // Out of LRM
  ),

  tagged_union_expression: $ => prec.right(seq(
    'tagged', $.member_identifier, optional($.primary)
  )),

  inside_expression: $ => prec.left(PREC.RELATIONAL, seq(
    $.expression, 'inside', '{', $.range_list, '}'
  )),

  mintypmax_expression: $ => prec('mintypmax_expression', seq(
    $.expression,
    optseq(':', $.expression, ':', $.expression)
  )),

  module_path_conditional_expression: $ => conditional_expr($, $.module_path_expression, $.module_path_expression),

  module_path_expression: $ => choice(
    $.module_path_primary,
    $._module_path_unary_expression,
    $._module_path_binary_expression,
    $.module_path_conditional_expression
  ),

  module_path_mintypmax_expression: $ => seq(
    $.module_path_expression,
    optseq(':', $.module_path_expression, ':', $.module_path_expression)
  ),

  _part_select_range: $ => choice(
    $.constant_range,
    $.indexed_range
  ),

  indexed_range: $ => seq(
    $.expression, choice('+:', '-:'), $.constant_expression
  ),

  _genvar_expression: $ => $.constant_expression,

  // The ones below are not part of the LRM explicitly (added to simplify reading of the grammar)
  _unary_expression: $ => unary_expr($, $.unary_operator, $.primary),

  _binary_expression: $ => binary_expr($, BINARY_OP_TABLE, $.expression),

  _parenthesized_expression: $ => paren_expr($.operator_assignment),

  _constant_unary_expression: $ => unary_expr($, $.unary_operator, $.constant_primary),

  _constant_binary_expression: $ => binary_expr($, BINARY_OP_TABLE, $.constant_expression),

  _constant_conditional_expression: $ => conditional_expr($, $.constant_expression, $.constant_expression),

  _module_path_unary_expression: $ => unary_expr($, $.unary_module_path_operator, $.module_path_primary),

  _module_path_binary_expression: $ => binary_expr($, BINARY_MOD_PATH_OP_TABLE, $.module_path_expression),


// ** A.8.4 Primaries
  // There are some branches that match the same items due to inlining:
  // E.g: $.ps_parameter_identifier, $.genvar_identifier, $.formal_port_identifier, and $.enum_identifier
  // could match the same $._identifier
  constant_primary: $ => prec('constant_primary', choice(
    $.primary_literal,
    seq($.ps_parameter_identifier, optional($.constant_select)),
    // seq($.specparam_identifier, optseq('[', $._constant_range_expression, ']')), // TODO:
    $.genvar_identifier,
    seq($.formal_port_identifier, optional($.constant_select)),
    seq(optchoice($.package_scope, $.class_scope), $.enum_identifier),
    $.empty_unpacked_array_concatenation,
    seq($.constant_concatenation, optseq('[', $._constant_range_expression, ']')),
    seq($.constant_multiple_concatenation, optseq('[', $._constant_range_expression, ']')),
    seq($.constant_function_call, optseq('[', $._constant_range_expression, ']')),
    // $._constant_let_expression, // No need to add since it's syntax is the same as a tf_call/constant_function_call (true ambiguity that adds conflicts)
    seq('(', $.constant_mintypmax_expression, ')'),
    $.constant_cast,
    $._constant_assignment_pattern_expression,
    $.type_reference,
    '$', // Out of LRM, required for 7.10.4 (bullet point 47): The $ primary shall be legal only in a select for a queue variable.
    'null'
  )),

  module_path_primary: $ => choice(
    $._number,
    $._identifier,
    $.module_path_concatenation,
    $.module_path_multiple_concatenation,
    $.function_subroutine_call,
    seq('(', $.module_path_mintypmax_expression, ')')
  ),

  primary: $ => prec('primary', choice(
    $.primary_literal,
    choice(
      seq(
        optchoice($.class_qualifier, $.package_scope),
        $.hierarchical_identifier,
        optional($.select)
      ),
      // INFO: The one below is a subgroup of the one above, however it doesn't work well
      // possibly because of some bad specified precedence/conflict. For the time being, adding
      // the option below fixes things and seems to work well (at the expense of maybe
      // some more complexity in the parser)
      seq($.implicit_class_handle, optional($.select)), // Out of LRM, but used as a workaround
    ),
    $.empty_unpacked_array_concatenation,
    seq($.concatenation, optseq('[', $.range_expression, ']')),
    seq($.multiple_concatenation, optseq('[', $.range_expression, ']')),
    prec.dynamic(-99, $.function_subroutine_call), // Avoid giving precedence to nested method_call instead of to hierarchical_identifier
    // $.let_expression,  // No need to add since its syntax is the same as a tf_call/subroutine_call (true ambiguity that adds conflicts)
    seq('(', $.mintypmax_expression, ')'),
    $.cast,
    $.assignment_pattern_expression,
    $.streaming_concatenation,
    // $.sequence_method_call, // TODO: Remove temporarily to narrow conflicts
    'this',
    '$',
    'null',
    '$root',          // Out of LRM, needed for sv-tests/chapter-20/20.14--coverage
    '\'{}',           // Out of LRM, fixes errors in some UVM files
    $.type_reference, // Out of LRM, should be for type comparison (6.23)
  )),

  // Modified to avoid matching empty string
  class_qualifier: $ => prec('class_qualifier', choice(
    seq('local', '::'),
    seq(optseq('local', '::'), choice(seq($.implicit_class_handle, '.'), $.class_scope))
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

  time_literal: $ => seq(
    choice($.unsigned_number, $.fixed_point_number),
    $.time_unit
  ),

  time_unit: $ => choice('s', 'ms', 'us', 'ns', 'ps', 'fs'),

  implicit_class_handle: $ => prec('implicit_class_handle', choice(
    seq('this', optseq('.', 'super')),
    'super'
  )),

  // Modified to avoid matching empty string
  bit_select: $ => repeat1(
    seq('[', $.expression, ']')
  ),

  // Modified to avoid matching empty string
  // Dynamic precedences are set so that indexes are set to belong to $.hierarchical_identifier rather than to $.select.
  // This is because first branch (prec -2) overlaps a lot with $.hierarchical_identifier, (having constant_bit_select instead of select)
  select: $ => choice(
    prec.dynamic(-2, seq(
      // This branch does not support $.text_macro_usage as $.hierarchical_identifier does
      repeat(seq('.', $.member_identifier, optional($.bit_select))), '.', $.member_identifier,
      optional($.bit_select),
      optseq('[', $._part_select_range, ']')
    )),
    prec.dynamic(-1, seq(
      $.bit_select,
      optseq('[', $._part_select_range, ']')
    )),
    prec.dynamic(0, seq('[', $._part_select_range, ']'))
  ),

  // Modified to avoid matching empty string
  nonrange_select: $ => choice(
    seq(
      repeat(seq('.', $.member_identifier, optional($.bit_select))), '.', $.member_identifier,
      optional($.bit_select)
    ),
    $.bit_select
  ),

  // Modified to avoid matching empty string
  constant_bit_select: $ => repeat1(prec('constant_bit_select', seq(
    '[', $.constant_expression, ']'
  ))),

  // Modified to avoid matching empty string
  constant_select: $ => choice(
    seq(
      repeat(seq('.', $.member_identifier, optional($.constant_bit_select))), '.', $.member_identifier,
      optional($.constant_bit_select),
      optseq('[', $._constant_part_select_range, ']')
    ),
    seq(
      $.constant_bit_select,
      optseq('[', $._constant_part_select_range, ']')
    ),
    seq('[', $._constant_part_select_range, ']'),
  ),

  cast: $ => seq($.casting_type, '\'', '(', $.expression, ')'),

  constant_cast: $ => seq($.casting_type, '\'', '(', $.constant_expression, ')'),

  _constant_let_expression: $ => $.let_expression,


// ** A.8.5 Expression left-side values
  net_lvalue: $ => choice(
    seq($.ps_or_hierarchical_net_identifier, optional($.constant_select)),
    seq('{', commaSep1($.net_lvalue), '}'),
    seq(optional($._assignment_pattern_expression_type), $.assignment_pattern_net_lvalue)
  ),

  variable_lvalue: $ => prec('variable_lvalue', choice(
    seq(
      // $.class_qualifier Out of LRM in optchoice: needed for static class access
      optchoice(seq($.implicit_class_handle, '.'), $.package_scope, $.class_qualifier),
      $.hierarchical_variable_identifier,
      optional($.select)
    ),
    seq('{', commaSep1($.variable_lvalue), '}'),
    seq(optional($._assignment_pattern_expression_type), $.assignment_pattern_variable_lvalue),
    $.streaming_concatenation
  )),

  nonrange_variable_lvalue: $ => seq(
    optchoice(seq($.implicit_class_handle, '.'), $.package_scope),
    $.hierarchical_variable_identifier,
    optional($.nonrange_select)
  ),


// ** A.8.6 Operators
  unary_operator: $ => choice('+', '-', '!', '~', '&', '~&', '|', '~|', '^', '~^', '^~'),

  // Unused (using BINARY_OP_TABLE constant instead). Left as a reference
  binary_operator: $ => choice(
    '+', '-', '*', '/', '%', '==', '!=', '===', '!==', '==?', '!=?', '&&', '||',
    '**', '<', '<=', '>', '>=', '&', '|', '^', '^~', '~^', '>>', '<<', '>>>',
    '<<<', '->', '<->'
  ),

  inc_or_dec_operator: $ => choice('++', '--'),

  unary_module_path_operator: $ => choice('!', '~', '&', '~&', '|', '~|', '^', '~^', '^~'),

  // Unused (using BINARY_MOD_PATH_OP_TABLE constant instead). Left as a reference
  binary_module_path_operator: $ => choice('==', '!=', '&&', '||', '&', '|', '^', '^~', '~^'),


// ** A.8.7 Numbers
  _number: $ => choice($.integral_number, $.real_number),

  integral_number: $ => choice(
    $.decimal_number,
    $.octal_number,
    $.binary_number,
    $.hex_number
  ),

  decimal_number: $ => prec('decimal_number', choice(
    $.unsigned_number,
    seq(
      field('size', optional($._size)),
      field('base', $.decimal_base),
      field('value', choice(
        $.unsigned_number,
        seq($.x_digit, token.immediate(/_*/)),
        seq($.z_digit, token.immediate(/_*/)),
      ))
    )
  )),

  binary_number: $ => seq(
    field('size', optional($._size)),
    field('base', $.binary_base),
    field('value', $.binary_value)
  ),

  octal_number: $ => seq(
    field('size', optional($._size)),
    field('base', $.octal_base),
    field('value', $.octal_value)
  ),

  hex_number: $ => seq(
    field('size', optional($._size)),
    field('base', $.hex_base),
    field('value', $.hex_value)
  ),

  sign: $ => token(choice('+', '-')), // Unused, leave as a reference

  _size: $ => prec('_size', $.unsigned_number),

  real_number: $ => choice(
    $.fixed_point_number,
    token(seq(
      /[0-9][0-9_]*/,      // $.unsigned_number
      /(\.[0-9][0-9_]*)?/, // optseq('.', $.unsigned_number)
      /[eE]/,              // $.exp
      /[+-]?/,             // optional($.sign),
      /[0-9][0-9_]*/       // $.unsigned_number
    ))
  ),

  fixed_point_number: $ => token(seq(
    /[0-9][0-9_]*/, // $.unsigned_number
    /\./,           // .
    /[0-9][0-9_]*/  // $.unsigned_number
  )),

  exp: $ => token(/[eE]/), // Unused, leave as a reference

  unsigned_number: $ => token(seq(
    /[0-9]/,  // $.decimal_digit,
    /[0-9_]*/ // repeat(choice(/_/, $.decimal_digit))
  )),

  binary_value: $ => token(seq(
    /[xXzZ?0-1]/,   // $.binary_digit,
    /[xXzZ?0-1_]*/, // repeat(choice(/_/, $.binary_digit))
  )),

  octal_value: $ => token(seq(
    /[xXzZ?0-7]/,   // $.octal_digit,
    /[xXzZ?0-7_]*/, // repeat(choice('_', $.octal_digit))
  )),

  hex_value: $ => token(seq(
    /[xXzZ?0-9a-fA-F]/,   // $.hex_digit,
    /[xXzZ?0-9a-fA-F_]*/, // repeat(choice('_', $.hex_digit))
  )),

  decimal_base: $ => /\'[sS]?[dD]/,

  binary_base: $ => /\'[sS]?[bB]/,

  octal_base: $ => /\'[sS]?[oO]/,

  hex_base: $ => /\'[sS]?[hH]/,

  decimal_digit: $ => /[0-9]/, // Unused, leave as a reference

  binary_digit: $ => choice($.x_digit, $.z_digit, /[0-1]/), // Unused, leave as a reference

  octal_digit: $ => choice($.x_digit, $.z_digit, /[0-7]/), // Unused, leave as a reference

  hex_digit: $ => choice($.x_digit, $.z_digit, /[0-9a-fA-F]/), // Unused, leave as a reference

  x_digit: $ => /[xX]/,

  z_digit: $ => /[zZ?]/,

  unbased_unsized_literal: $ => choice('\'0', '\'1', /'[xXzZ]/), // A.10.53: The apostrophe in unbased_unsized_literal shall not be followed by white_space


// ** A.8.8 Strings
  string_literal: $ => choice(
    $.quoted_string,
    $.triple_quoted_string
  ),

  quoted_string: $ => seq(
    '"',
    repeat(choice(
      $._quoted_string_item,
      $._string_escape_seq
    )),
    '"'
  ),

  triple_quoted_string: $ => seq(
    '"""',
    repeat(choice(
      $._triple_quoted_string_item,
      token(prec(1, seq('"', /[^"]/))),
      token(prec(1, seq('""', /[^"]/))),
      $._string_escape_seq
    )),
    '"""'
  ),

  _quoted_string_item: $ => token.immediate(prec(1, /[^\\"\n]+/)), // any_ASCII_character except \ or newline or "

  _triple_quoted_string_item: $ => token.immediate(prec(1, /[^\\"]+/)), //  any_ASCII_character except \

  _string_escape_seq: $ => token(prec(1, seq(
    '\\',
    choice(
      /[^x0-7]/,           // \any_ASCII_character (exclude 'x' and '0-7' since those would be matched by following cases)
      /[0-7]{1,3}/,        // \one_to_three_digit_octal_number
      /x[0-9a-fA-F]{1,2}/, // \x one_to_two_digit_hex_number
    )
  ))),


// * A.9 General
// ** A.9.1 Attributes
  attribute_instance: $ => seq('(*', commaSep1($.attr_spec), '*)'),

  attr_spec: $ => seq($.attr_name, optseq('=', $.constant_expression)),

  attr_name: $ => $._identifier,


// ** A.9.2 Comments
  // comment: $ => one_line_comment | block_comment
  // one_line_comment: $ => // comment_text \n
  // block_comment: $ => /* comment_text */
  // comment_text: $ => { Any_ASCII_character }

  // http://stackoverflow.com/questions/13014947/regex-to-match-a-c-style-multiline-comment/36328890#36328890
  // from: https://github.com/tree-sitter/tree-sitter-c/blob/master/grammar.js
  comment: $ => token(choice(
    seq('//', /.*/), // $._one_line_comment -> seq('//', $.comment_text)
    seq(             // $._block_comment
      '/*',
      /[^*]*\*+([^/*][^*]*\*+)*/,
      '/'
    )
  )),


// ** A.9.3 Identifiers
  array_identifier: $ => $._identifier, // Seems unused
  block_identifier: $ => $._identifier,
  bin_identifier: $ => $._identifier,
  c_identifier: $ => token(prec(-1, /[a-zA-Z_][a-zA-Z0-9_]*/)),
  cell_identifier: $ => $._identifier,
  checker_identifier: $ => $._identifier,
  class_identifier: $ => $._identifier,
  class_variable_identifier: $ => $.variable_identifier,
  clocking_identifier: $ => $._identifier,
  config_identifier: $ => $._identifier,
  const_identifier: $ => $._identifier,
  constraint_identifier: $ => $._identifier,
  covergroup_identifier: $ => $._identifier,
  covergroup_variable_identifier: $ => $.variable_identifier,
  cover_point_identifier: $ => $._identifier,
  cross_identifier: $ => $._identifier,
  dynamic_array_variable_identifier: $ => $.variable_identifier,
  enum_identifier: $ => $._identifier,
  escaped_identifier: $ => seq('\\', /[^\s]*/), // \ { any_printable_ASCII_character_except_white_space } white_space
  formal_identifier: $ => $._identifier,
  formal_port_identifier: $ => $._identifier,
  function_identifier: $ => $._identifier,
  generate_block_identifier: $ => $._identifier,
  genvar_identifier: $ => $._identifier,

  hierarchical_array_identifier: $ => $.hierarchical_identifier,
  hierarchical_block_identifier: $ => $.hierarchical_identifier,
  hierarchical_event_identifier: $ => $.hierarchical_identifier,

  hierarchical_identifier: $ => prec('hierarchical_identifier', seq(
    optseq('$root', '.'),
    repeat(prec('hierarchical_identifier', seq(
      choice($._identifier, $.text_macro_usage), // Slightly out of LRM to support use of $.text_macro_usage as part of hierarchical identifiers
      optional($.constant_bit_select),
      '.'))) ,
    $._identifier
  )),

  hierarchical_net_identifier: $ => $.hierarchical_identifier,
  hierarchical_parameter_identifier: $ => $.hierarchical_identifier,
  hierarchical_property_identifier: $ => $.hierarchical_identifier,
  hierarchical_sequence_identifier: $ => $.hierarchical_identifier,
  hierarchical_task_identifier: $ => $.hierarchical_identifier,
  hierarchical_tf_identifier: $ => $.hierarchical_identifier,
  hierarchical_variable_identifier: $ => $.hierarchical_identifier,

  _identifier: $ => choice(
    $.simple_identifier,
    $.escaped_identifier
  ),

  index_variable_identifier: $ => $._identifier,
  interface_identifier: $ => $._identifier,
  interface_port_identifier: $ => $._identifier,
  inout_port_identifier: $ => $._identifier,
  input_port_identifier: $ => $._identifier,
  instance_identifier: $ => $._identifier,
  library_identifier: $ => $._identifier,
  member_identifier: $ => $._identifier,
  method_identifier: $ => $._identifier,
  modport_identifier: $ => $._identifier,
  module_identifier: $ => $._identifier,
  net_identifier: $ => $._identifier,
  nettype_identifier: $ => $._identifier,
  output_port_identifier: $ => $._identifier,
  package_identifier: $ => $._identifier,

  package_scope: $ => prec('package_scope', seq(
    choice($.package_identifier, '$unit'),
    '::'
  )),

  parameter_identifier: $ => $._identifier,
  port_identifier: $ => $._identifier,
  program_identifier: $ => $._identifier,
  property_identifier: $ => $._identifier,

  ps_class_identifier: $ => seq(
    optional($.package_scope), $.class_identifier
  ),

  ps_covergroup_identifier: $ => seq(
    optional($.package_scope), $.covergroup_identifier
  ),

  ps_checker_identifier: $ => seq(
    optional($.package_scope), $.checker_identifier
  ),

  ps_identifier: $ => seq(
    optional($.package_scope), $._identifier
  ),

  ps_or_hierarchical_array_identifier: $ => seq(
    optchoice(
      seq($.implicit_class_handle, '.'),
      $.class_scope,
      $.package_scope
    ),
    $.hierarchical_array_identifier
  ),

  ps_or_hierarchical_net_identifier: $ => choice(
    seq(optional($.package_scope), $.net_identifier),
    $.hierarchical_net_identifier
  ),

  ps_or_hierarchical_property_identifier: $ => choice(
    seq(optional($.package_scope), $.property_identifier),
    $.hierarchical_property_identifier
  ),

  ps_or_hierarchical_sequence_identifier: $ => choice(
    seq(optional($.package_scope), $.sequence_identifier),
    $.hierarchical_sequence_identifier
  ),

  ps_or_hierarchical_tf_identifier: $ => choice(
    seq(optional($.package_scope), $.tf_identifier),
    $.hierarchical_tf_identifier
  ),

  ps_parameter_identifier: $ => choice(
    seq(
      optchoice($.package_scope, $.class_scope),
      $.parameter_identifier
    ),
    // INFO: This choice does not add branches that are not already covered by other rules.
    //       On the other and it adds numerous unnecessary conflicts
    // seq(
    //   repseq($.generate_block_identifier, optseq('[', $.constant_expression, ']'), '.'),
    //   $.parameter_identifier
    // )
  ),

  ps_type_identifier: $ => seq(
    optchoice(seq('local', '::'), $.package_scope, $.class_scope),
    $.type_identifier
  ),

  rs_production_identifier: $ => $._identifier,
  sequence_identifier: $ => $._identifier,
  signal_identifier: $ => $._identifier,
  simple_identifier: $ => /[a-zA-Z_][a-zA-Z0-9_$]*/,
  specparam_identifier: $ => $._identifier,
  system_tf_identifier: $ => /\$[a-zA-Z0-9_$]+/,
  task_identifier: $ => $._identifier,
  tf_identifier: $ => $._identifier,
  terminal_identifier: $ => $._identifier,
  topmodule_identifier: $ => $._identifier,
  type_identifier: $ => $._identifier,
  udp_identifier: $ => $._identifier,
  variable_identifier: $ => $._identifier,


// ** A.9.4 White space
  // white_space: $ => space | tab | newline | eof;
  // Set as /\s/ in $.extras


// * 20. Utility system tasks and system functions
// ** 20.2 Simulation control system tasks
  simulation_control_task: $ => seq(
    choice('$stop', '$finish', '$exit'),
    optseq('(', optional($.list_of_arguments), ')'),
    ';'
  ),

// * 22. Compiler directives
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
  system_lib_string: $ => token(seq(
    '<',
    repeat(choice(/[^>\n]/, '\\>')),
    '>',
  )),

  include_compiler_directive: $ => seq(
    directive('include'),
    choice(
      $.quoted_string,
      $.system_lib_string,
      $.text_macro_usage,// Out of LRM (test sv-tests/chapter-22/22.5.1--include-define-expansion)
    )
  ),


// ** 22.5 `define, `undef, and `undefineall
  default_text: $ => /\w+/,

  macro_text: $ => /(\\(.|\r?\n)|[^\\\n])*/,

  text_macro_definition: $ => seq(
    directive('define'),
    $.text_macro_name,
    optional($.macro_text),
    token.immediate(/\r?\n/),
  ),

  text_macro_name: $ => seq(
    $.text_macro_identifier,
    optseq('(', $.list_of_formal_arguments, ')')
  ),

  list_of_formal_arguments: $ => commaSep1($.formal_argument),

  formal_argument: $ => seq(
    $.simple_identifier,
    optseq('=', $.default_text)
  ),

  text_macro_identifier: $ => $._identifier,

  text_macro_usage: $ => prec.right(seq(
    '`',
    $.text_macro_identifier,
    optseq('(', optional($.list_of_actual_arguments), ')')
  )),

  list_of_actual_arguments: $ => list_of_args($, 'list_of_arguments', $.actual_argument),

  actual_argument: $ => choice(
    // Out of LRM, needed to support parameterized data types and constraints as macro args (common in the UVM)
    $.param_expression, // e.g: `uvm_component_utils_param
    $.constraint_block  // e.g: `uvm_do_with
  ),

  undefine_compiler_directive: $ => seq(directive('undef'), $.text_macro_identifier),

  undefineall_compiler_directive: $ => directive('undefineall'),


// ** 22.6 `ifdef, `else, `elsif, `endif, `ifndef
  // Modified with respect to LRM: do not parse preprocessed code
  conditional_compilation_directive: $ => choice(
    seq($._ifdef_or_ifndef, $.ifdef_condition),
    seq(directive('elsif'), $.ifdef_condition),
    directive('else'),
    directive('endif')
  ),

  _ifdef_or_ifndef: $ => choice(
    directive('ifdef'),
    directive('ifndef')
  ),

  ifdef_condition: $ => choice(
    $.text_macro_identifier,
    seq('(', $.ifdef_macro_expression, ')')
  ),

  ifdef_macro_expression: $ => choice(
    $.text_macro_identifier,
    binary_expr($, BINARY_MACRO_OP_TABLE, $.ifdef_macro_expression),
    unary_expr($, '!', $.ifdef_macro_expression),
    paren_expr($.ifdef_macro_expression),
  ),

  binary_logical_operator: $ => choice('&&', '||', '->', '<->'), // Unused


// ** 22-7 timescale
  timescale_compiler_directive: $ => seq(
    directive('timescale'),
    $.time_literal, // time_unit,
    '/',
    $.time_literal, // time_precision
    token.immediate(/\r?\n/),
  ),

// ** 22-8 default_nettype
  default_nettype_compiler_directive: $ => seq(
    directive('default_nettype'),
    $.default_nettype_value,
    token.immediate(/\r?\n/),
  ),

  default_nettype_value: $ => choice('wire', 'tri', 'tri0', 'tri1', 'wand', 'triand', 'wor', 'trior', 'trireg', 'uwire', 'none'),


// ** 22-9
  unconnected_drive_compiler_directive: $ => seq(
    directive('unconnected_drive'),
    choice('pull0', 'pull1'),
    token.immediate(/\r?\n/),
  ),


// ** 22.10 `celldefine and `endcelldefine
  celldefine_compiler_directive: $ => directive('celldefine'),

  endcelldefine_compiler_directive: $ => directive('endcelldefine'),


// ** 22.11 `pragma
  pragma: $ => prec.right(seq(
    directive('pragma'),
    $.pragma_name,
    commaSep($.pragma_expression),
  )),

  pragma_name: $ => $.simple_identifier,

  pragma_expression: $ => choice(
    $.pragma_keyword,
    seq($.pragma_keyword, '=', $.pragma_value),
    $.pragma_value,
  ),

  pragma_value: $ => choice(
    seq('(', commaSep1($.pragma_expression) , ')'),
    $._number,
    $.string_literal,
    $._identifier,
  ),

  pragma_keyword: $ => $.simple_identifier,


// ** 22-12 `line
  line_compiler_directive: $ => seq(
    directive('line'),
    $.unsigned_number,
    alias($.quoted_string, $.filename),
    alias(token(/[0-2]/), $.level),
    token.immediate(/\r?\n/),
  ),

// ** 22.13 `__FILE__ and `__LINE__
  file_or_line_compiler_directive: $ => choice(
    directive('__FILE__'),
    directive('__LINE__'),
  ),


// ** 22.14 `begin_keywords, `end_keywords
  keywords_directive: $ => seq(
    directive('begin_keywords'),
    '\"',
    $.version_specifier,
    '\"',
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
    $.snippets,

    $.var_data_type,
    $.any_parameter_declaration,
    $.elaboration_severity_system_task,
    $.attr_name,

    $._binary_expression,
    $._constant_binary_expression,
    $._constant_conditional_expression,

    // Identifiers
    $.array_identifier,
    $.block_identifier,
    $.bin_identifier,
    $.cell_identifier,
    $.checker_identifier,
    $.class_identifier,
    $.class_variable_identifier,
    $.clocking_identifier,
    $.config_identifier,
    $.const_identifier,
    $.constraint_identifier,
    $.covergroup_identifier,
    $.covergroup_variable_identifier,
    $.cover_point_identifier,
    $.cross_identifier,
    $.dynamic_array_variable_identifier,
    $.enum_identifier,
    $.formal_identifier,
    $.formal_port_identifier,
    $.function_identifier,
    $.generate_block_identifier,
    $.genvar_identifier,

    $.hierarchical_array_identifier,
    $.hierarchical_block_identifier,
    $.hierarchical_event_identifier,
    // $.hierarchical_identifier, // Don't inline
    $.hierarchical_net_identifier,
    $.hierarchical_parameter_identifier,
    $.hierarchical_property_identifier,
    $.hierarchical_sequence_identifier,
    $.hierarchical_task_identifier,
    $.hierarchical_tf_identifier,
    $.hierarchical_variable_identifier,

    $.index_variable_identifier,
    $.interface_identifier,
    $.interface_port_identifier,
    $.inout_port_identifier,
    $.input_port_identifier,
    $.instance_identifier,
    $.library_identifier,
    $.member_identifier,
    $.method_identifier,
    $.modport_identifier,
    $.module_identifier,
    $.net_identifier,
    $.nettype_identifier,
    $.output_port_identifier,
    $.package_identifier,
    // $.package_scope, // Don't inline
    $.parameter_identifier,
    $.port_identifier,
    $.program_identifier,
    $.property_identifier,

    $.ps_class_identifier,
    $.ps_covergroup_identifier,
    $.ps_checker_identifier,
    $.ps_identifier,
    $.ps_or_hierarchical_array_identifier,
    $.ps_or_hierarchical_net_identifier,
    $.ps_or_hierarchical_property_identifier,
    $.ps_or_hierarchical_sequence_identifier,
    $.ps_or_hierarchical_tf_identifier,
    $.ps_parameter_identifier,
    $.ps_type_identifier,

    $.rs_production_identifier,
    $.sequence_identifier,
    $.signal_identifier,
    $.specparam_identifier,
    $.task_identifier,
    $.tf_identifier,
    $.terminal_identifier,
    $.topmodule_identifier,
    $.type_identifier,
    $.udp_identifier,
    $.variable_identifier,

    // Identifiers out of A.9
    $.hierarchical_btf_identifier,
    $.let_identifier,
    $.input_identifier,
    $.output_identifier,
    // $.edge_identifier, // Don't inline
    $.text_macro_identifier,

    // Specify expressions
    $.t_path_delay_expression,
    $.trise_path_delay_expression,
    $.tfall_path_delay_expression,
    $.tz_path_delay_expression,
    $.t01_path_delay_expression,
    $.t10_path_delay_expression,
    $.t0z_path_delay_expression,
    $.tz1_path_delay_expression,
    $.t1z_path_delay_expression,
    $.tz0_path_delay_expression,
    $.t0x_path_delay_expression,
    $.tx1_path_delay_expression,
    $.t1x_path_delay_expression,
    $.tx0_path_delay_expression,
    $.txz_path_delay_expression,
    $.tzx_path_delay_expression,

    // Coverage expressions
    $._covergroup_expression,
    $._cross_set_expression,
    $._integer_covergroup_expression,
    $._with_covergroup_expression,
    $._set_covergroup_expression,
  ],

// ** Precedences
  precedences: () => [
    // Top level precedence
    //   Used when items, declarations or statements are outside of modules,
    //   classes, packages or checkers
    //   Use case: snippets of code on web, include files...
    ['_description', '_non_port_module_item'],
    ['_description', '_module_common_item'],
    ['_description', 'data_declaration'],
    ['_description', '_package_or_generate_item_declaration'],
    ['_description', 'statement_item'],
    ['_package_or_generate_item_declaration', '_non_port_module_item'],
    ['_package_or_generate_item_declaration', 'statement_item'],
    ['_package_or_generate_item_declaration', '_library_description'],
    ['_package_or_generate_item_declaration', '_interface_or_generate_item'],


    // Common item for module/package without context -> Consider it a module item
    //
    // _package_or_generate_item_declaration  •  ';'  …
    // 1:  (_module_or_generate_item_declaration  _package_or_generate_item_declaration)  •  ';'  …  (precedence: '_module_or_generate_item_declaration')
    // 2:  (_package_item  _package_or_generate_item_declaration)  •  ';'  …                          (precedence: '_package_item')
    ['_module_or_generate_item_declaration', '_package_item'],
    // timeunits_declaration  •  ';'  …
    // 1:  (_non_port_module_item  timeunits_declaration)  •  ';'  …  (precedence: '_non_port_module_item')
    // 2:  (_package_item  timeunits_declaration)  •  ';'  …          (precedence: '_package_item')
    ['_non_port_module_item', '_package_item'],


    // First appearing timeunits being part of the declaration have higher precedence than the item.
    // Plus, A.10.3: A timeunits_declaration shall be legal as a non_port_module_item, non_port_interface_item,
    // non_port_program_item, or package_item only if it repeats and matches a previous
    // timeunits_declaration within the same time scope.
    //
    // 'package'  _identifier  ';'  timeunits_declaration  •  ';'  …
    // 1:  'package'  _identifier  ';'  (_package_item  timeunits_declaration)  •  ';'  …                                                                    (precedence: '_package_item')
    // 2:  (package_declaration  'package'  _identifier  ';'  timeunits_declaration  •  package_declaration_repeat1  'endpackage'  ':'  package_identifier)  (precedence: 'package_declaration')
    // 3:  (package_declaration  'package'  _identifier  ';'  timeunits_declaration  •  package_declaration_repeat1  'endpackage')                           (precedence: 'package_declaration')
    ['package_declaration', '_package_item'],


    // In case we are working with a snippet (no module/interface declaration), consider it a _module_item
    //
    // 'generate'  _module_common_item  •  ';'  …
    // 1:  'generate'  (_interface_or_generate_item  _module_common_item)  •  ';'  …  (precedence: '_interface_or_generate_item')
    // 2:  'generate'  (_module_or_generate_item  _module_common_item)  •  ';'  …     (precedence: '_module_or_generate_item')
    ['_module_or_generate_item', '_interface_or_generate_item'],


    // Consider port list without directions to be nonANSI:
    //
    // module_keyword  module_identifier  '('  _identifier  •  ')'  …
    //   1:  module_keyword  module_identifier  '('  (ansi_port_declaration  _identifier)  •  ')'  …
    //   2:  module_keyword  module_identifier  '('  (port_reference  _identifier)  •  ')'  …
    ['port_reference', 'ansi_port_declaration'],


    // If no port direction is specified but there is something besides the identifier (e.g. the unpacked dimension)
    // then it must be an ANSI declaration instead of a nonANSI
    //
    // module_keyword  module_identifier  '('  _identifier  unpacked_dimension  •  ')'  …
    //   1:  module_keyword  module_identifier  '('  _identifier  (_variable_dimension  unpacked_dimension)  •  ')'  …            (precedence: '_variable_dimension')
    //   2:  module_keyword  module_identifier  '('  _identifier  (ansi_port_declaration_repeat1  unpacked_dimension)  •  ')'  …
    ['ansi_port_declaration', '_variable_dimension'],


    // $.data_type corresponds to variables, $.net_type to $.net_port_type
    //
    // 'input'  data_type  •  '\'  …
    // 1:  'input'  (data_type_or_implicit  data_type)  •  '\'  …  (precedence: 'data_type_or_implicit')
    // 2:  'input'  (variable_port_type  data_type)  •  '\'  …      (precedence: 'variable_port_type')
    ['variable_port_type', 'data_type_or_implicit'],


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


    // Not sure about this one, but the other way around creates an endless loop in the parsing process
    //
    // 'typedef'  _incomplete_class_scoped_type  •  '\'  …
    // 1:  'typedef'  (_data_type_or_incomplete_class_scoped_type  _incomplete_class_scoped_type)  •  '\'  …
    // 2:  'typedef'  (_incomplete_class_scoped_type  _incomplete_class_scoped_type)  •  '\'  …
    ['_data_type_or_incomplete_class_scoped_type', '_incomplete_class_scoped_type'],


    // pure virtual function will always be a function prototype overriden in the extended class
    //
    // 'class'  _identifier  ';'  'pure'  'virtual'  •  'function'  …
    // 1:  'class'  _identifier  ';'  (class_method  'pure'  'virtual'  •  _method_prototype  ';')
    // 2:  'class'  _identifier  ';'  (method_qualifier  'pure'  'virtual')  •  'function'  …
    ['class_method', 'method_qualifier'],


    // Since it is placed inside a class declaration consider it a class property
    //
    //   'class'  _identifier  ';'  'const'  data_type  •  simple_identifier  …
    //   1:  'class'  _identifier  ';'  'const'  (data_type_or_implicit  data_type)  •  simple_identifier  …                     (precedence: 'data_type_or_implicit')
    //   2:  'class'  _identifier  ';'  (class_property  'const'  data_type  •  const_identifier  ';')                            (precedence: 'class_property')
    //   3:  'class'  _identifier  ';'  (class_property  'const'  data_type  •  const_identifier  '='  constant_expression  ';')  (precedence: 'class_property')
    ['class_property', 'data_type_or_implicit'],


    // nettype keyword means there is a nettype_declaration
    //
    // 'nettype'  _identifier  •  '\'  …
    // 1:  'nettype'  (data_type  _identifier)  •  '\'  …                      (precedence: 'data_type')
    // 2:  (nettype_declaration  'nettype'  _identifier  •  _identifier  ';')
    ['nettype_declaration', 'data_type'],


    // If it's inside a class consider it a class_item_qualifier since it seems more specific
    //
    //   'class'  _identifier  ';'  'static'  •  'string'  …
    //   1:  'class'  _identifier  ';'  (class_item_qualifier  'static')  •  'string'  …  (precedence: 'class_item_qualifier')
    //   2:  'class'  _identifier  ';'  (lifetime  'static')  •  'string'  …              (precedence: 'lifetime')
    ['class_item_qualifier', 'lifetime'],


    // In declarations after the identifier:
    //  - Variables:  $._variable_dimension (includes $.unpacked_dimension plus $.associative_dimension and $.queue_dimension)
    //  - Nets: $.unpacked_dimension
    // If no type is specified explicitly it is considered a net.
    //
    // module_nonansi_header  'input'  _identifier  •  ';'  …
    //   1:  module_nonansi_header  'input'  _identifier  (_variable_dimension  unpacked_dimension)  •  ';'  …
    //   2:  module_nonansi_header  'input'  _identifier  (list_of_port_identifiers_repeat1  unpacked_dimension)  •  ';'  …
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


    // For $.class_new only the 1st syntax is correct (2nd corresponds to a shallow copy but should have parenthesis)
    //
    // _identifier  '='  'new'  '('  expression  •  ')'  …
    // 1:  _identifier  '='  'new'  '('  (list_of_arguments  expression)  •  ')'  …     (precedence: 'list_of_arguments')
    // 2:  _identifier  '='  'new'  '('  (mintypmax_expression  expression)  •  ')'  …  (precedence: 'mintypmax_expression')
    ['list_of_arguments', 'mintypmax_expression'],


    // Real conflict after adding the $ as a constant_primary, needed to index queues (e.g. a[0:$-1])
    //
    // 'input'  _identifier  '['  '$'  •  ':'  …
    // 1:  'input'  _identifier  '['  (constant_primary  '$')  •  ':'  …                        (precedence: 'constant_primary')
    // 2:  'input'  _identifier  (queue_dimension  '['  '$'  •  ':'  constant_expression  ']')
    ['queue_dimension', 'constant_primary'],


    // A.10.4: In packed_dimension, unsized_dimension is permitted only as the sole packed dimension in a DPI import
    // declaration; see dpi_function_proto and dpi_task_proto.
    // This is a much less likely case to happen, so prioritize $._variable_dimension
    //
    //   'localparam'  _identifier  unsized_dimension  •  '['  …
    //   1:  'localparam'  _identifier  (_variable_dimension  unsized_dimension)  •  '['  …  (precedence: '_variable_dimension')
    //   2:  'localparam'  _identifier  (packed_dimension  unsized_dimension)  •  '['  …
    ['_variable_dimension', 'packed_dimension'],


    // Dimensions after the identifier are unpacked
    //
    // 'input'  _identifier  '['  constant_range  ']'  •  '['  …
    // 1:  'input'  _identifier  (packed_dimension  '['  constant_range  ']')  •  '['  …    (precedence: 'packed_dimension')
    // 2:  'input'  _identifier  (unpacked_dimension  '['  constant_range  ']')  •  '['  …  (precedence: 'unpacked_dimension')
    ['unpacked_dimension', 'packed_dimension'],


    // First ansi-port (interface type or net_type) with unpacked array.
    // It would be non-ansi if it didn't have the array (only a list of identifiers separated by commas)
    //
    //   module_keyword  module_identifier  '('  _identifier  '['  constant_expression  ']'  •  ')'  …
    //     1:  module_keyword  module_identifier  '('  _identifier  (constant_bit_select1_repeat1  '['  constant_expression  ']')  •  ')'  …
    //     2:  module_keyword  module_identifier  '('  _identifier  (unpacked_dimension  '['  constant_expression  ']')  •  ')'  …            (precedence: 'unpacked_dimension')
    ['unpacked_dimension', 'constant_bit_select'],


    // Since it's a declaration (of a user defined type) it's not a part select but a packed dimension (check doulos/3.3_array)
    //
    // _identifier  '['  constant_range  •  ']'  …
    // 1:  _identifier  '['  (_constant_part_select_range  constant_range)  •  ']'  …  (precedence: '_constant_part_select_range')
    // 2:  _identifier  (packed_dimension  '['  constant_range  •  ']')                (precedence: 'packed_dimension')
    ['packed_dimension', '_constant_part_select_range'],


    // $.port_direction would be for module/interface/program
    //
    //   'function'  function_identifier  '('  'ref'  •  'var'  …
    //   1:  'function'  function_identifier  '('  (port_direction  'ref')  •  'var'  …
    //   2:  'function'  function_identifier  '('  (tf_port_direction  'ref')  •  'var'  …
    ['tf_port_direction', 'port_direction'],


    // Both cases would be illegal since they have a 'nested' type_reference as a consequence
    // of it being a branch of $.primary, needed for type comparison (see sv-tests/6.23).
    // Choose the 1st one since it's the one that conforms to the LRM
    //
    // 'type'  '('  type_reference  •  ')'  …
    // 1:  'type'  '('  (data_type  type_reference)  •  ')'  …  (precedence: 'data_type')
    // 2:  'type'  '('  (primary  type_reference)  •  ')'  …    (precedence: 'primary')
    ['data_type', 'primary'],
    // 'assign'  '#'  '('  type_reference  •  ''{'  …
    // 1:  'assign'  '#'  '('  (_assignment_pattern_expression_type  type_reference)  •  ''{'  …
    // 2:  'assign'  '#'  '('  (primary  type_reference)  •  ''{'  …                              (precedence: 'primary')
    ['_assignment_pattern_expression_type', 'primary'],


    // Make checkers less relevant
    //
    // _identifier  name_of_instance  '('  ')'  •  ';'  …
    // 1:  (checker_instantiation  _identifier  name_of_instance  '('  ')'  •  ';')     (precedence: 'checker_instantiation')
    // 2:  _identifier  (hierarchical_instance  name_of_instance  '('  ')')  •  ';'  …  (precedence: 'hierarchical_instance')
    ['hierarchical_instance', 'checker_instantiation'],
    // 'generate'  ';'  •  ';'  …
    // 1:  'generate'  (_checker_or_generate_item_declaration  ';')  •  ';'  …  (precedence: '_checker_or_generate_item_declaration')
    // 2:  'generate'  (_package_or_generate_item_declaration  ';')  •  ';'  …  (precedence: '_package_or_generate_item_declaration')
    ['_package_or_generate_item_declaration', '_checker_or_generate_item_declaration'],
    // 'generate'  severity_system_task  •  ';'  …
    // 1:  'generate'  (_checker_generate_item  severity_system_task)  •  ';'  …
    // 2:  'generate'  (_module_common_item  severity_system_task)  •  ';'  …     (precedence: '_module_common_item')
    ['_module_common_item', '_checker_generate_item'],
    // 'generate'  genvar_declaration  •  ';'  …
    // 1:  'generate'  (_checker_or_generate_item_declaration  genvar_declaration)  •  ';'  …  (precedence: '_checker_or_generate_item_declaration')
    // 2:  'generate'  (_module_or_generate_item_declaration  genvar_declaration)  •  ';'  …   (precedence: '_module_or_generate_item_declaration')
    ['_module_or_generate_item_declaration', '_checker_or_generate_item_declaration'],
    // 'generate'  continuous_assign  •  ';'  …
    // 1:  'generate'  (_module_common_item  continuous_assign)  •  ';'  …       (precedence: '_module_common_item')
    // 2:  'generate'  (checker_or_generate_item  continuous_assign)  •  ';'  …
    ['_module_common_item', 'checker_or_generate_item'],


    // module, interface and program instantiations have the exact same syntax:
    //
    //   module_instantiation  •  ';'  …
    //   1:  (_module_or_generate_item  module_instantiation)  •  ';'  …  (precedence: '_module_or_generate_item')
    //   2:  (interface_instantiation  module_instantiation)  •  ';'  …   (precedence: 'interface_instantiation')
    //   3:  (program_instantiation  module_instantiation)  •  ';'  …     (precedence: 'program_instantiation')
    ['_module_or_generate_item', 'interface_instantiation', 'program_instantiation'],
    // 'bind'  bind_target_scope  module_instantiation  •  ';'  …
    // 1:  'bind'  bind_target_scope  (_bind_instantiation  module_instantiation)  •  ';'  …      (precedence: '_bind_instantiation')
    // 2:  'bind'  bind_target_scope  (interface_instantiation  module_instantiation)  •  ';'  …  (precedence: 'interface_instantiation')
    // 3:  'bind'  bind_target_scope  (program_instantiation  module_instantiation)  •  ';'  …    (precedence: 'program_instantiation')
    ['_bind_instantiation', 'interface_instantiation', 'program_instantiation'],


    // The first else on an immediate assertion inside an if-else block corresponds to the action block of the assertion
    //
    //   'wait_order'  '('  hierarchical_identifier  ')'  'wait_order'  '('  hierarchical_identifier  ')'  statement  •  'else'  …
    //   1:  'wait_order'  '('  hierarchical_identifier  ')'  'wait_order'  '('  hierarchical_identifier  ')'  (action_block  statement  •  'else'  statement_or_null)  (precedence: 'action_block')
    //   2:  'wait_order'  '('  hierarchical_identifier  ')'  'wait_order'  '('  hierarchical_identifier  ')'  (statement_or_null  statement)  •  'else'  …             (precedence: 'statement_or_null')
    ['action_block', 'statement_or_null'],


    // @ plus parenthesis means an event (e.g @(posedge clk))
    //
    // module_nonansi_header  'initial'  '@'  '('  '('  expression  •  ')'  …
    // 1:  module_nonansi_header  'initial'  '@'  '('  '('  (event_expression  expression)  •  ')'  …      (precedence: 'event_expression', associativity: Left)
    // 2:  module_nonansi_header  'initial'  '@'  '('  '('  (mintypmax_expression  expression)  •  ')'  …  (precedence: 'mintypmax_expression')
    ['event_expression', 'mintypmax_expression'],


    // Sequence declarations have arguments in ports
    //
    //   'sequence'  sequence_identifier  '('  _identifier  '='  '$'  •  ')'  …
    //   1:  'sequence'  sequence_identifier  '('  _identifier  '='  (_sequence_actual_arg  '$')  •  ')'  …
    //   2:  'sequence'  sequence_identifier  '('  _identifier  '='  (primary  '$')  •  ')'  …               (precedence: 'primary')
    ['_sequence_actual_arg', 'primary'],
    ['_sequence_actual_arg', 'event_expression'],


    // $.checker_instantiation with sequence instance as an ordered arg
    // Probably doesn't matter much which one to choose, but seems more reasonable to take $.event_expression
    // since it is a branch of $._sequence_actual_arg
    //
    // _identifier  name_of_instance  '('  sequence_instance  •  ')'  …
    // 1:  _identifier  name_of_instance  '('  (event_expression  sequence_instance)  •  ')'  …  (precedence: 'event_expression')
    // 2:  _identifier  name_of_instance  '('  (sequence_expr  sequence_instance)  •  ')'  …
    ['event_expression', 'sequence_expr'],


    // struct/array initializations:
    //   Consider higher priority a structure pattern even though it could be an assignment to an array,
    //   but the parser cannot know that...
    //
    //   ''{'  assignment_pattern_key  •  ':'  …
    //   1:  ''{'  (_array_pattern_key  assignment_pattern_key)  •  ':'  …
    //   2:  ''{'  (_structure_pattern_key  assignment_pattern_key)  •  ':'  …
    ['_structure_pattern_key', '_array_pattern_key'],


    // Add support for severity_system_task out of LRM:
    // - The $.snippets rule creates this conflict, consider it the lower level node
    //
    // severity_system_task  •  'resetall_compiler_directive_token1'  …
    // 1:  (_module_common_item  severity_system_task)  •  'resetall_compiler_directive_token1'  …        (precedence: '_module_common_item')
    // 2:  (subroutine_call_statement  severity_system_task)  •  'resetall_compiler_directive_token1'  …
    ['subroutine_call_statement', '_module_common_item'],


    // Both seem incorrect syntax but supported due to soft restricting of the broad grammar.
    // An example of this conflict would be: ('{0, 1, 2} : ) -> But this would need to be on the RHS and without parenthesis?
    // So just restrict it to be a 'primary' instead of '_constant_assignment_pattern_expression' (relevant to constant_primary)
    //
    // '('  assignment_pattern_expression  •  ':'  …
    // 1:  '('  (_constant_assignment_pattern_expression  assignment_pattern_expression)  •  ':'  …  (precedence: '_constant_assignment_pattern_expression')
    // 2:  '('  (primary  assignment_pattern_expression)  •  ':'  …                                  (precedence: 'primary')
    ['primary', '_constant_assignment_pattern_expression'],


    // A number before the base is always the $._size
    //
    // '##'  unsigned_number  •  decimal_base  …
    // 1:  '##'  (_size  unsigned_number)  •  decimal_base  …           (precedence: 0)
    // 2:  '##'  (decimal_number  unsigned_number)  •  decimal_base  …
    ['_size', 'decimal_number'],


    // $.block_event_expression is at a higher level in the syntax tree
    //
    //   'covergroup'  _identifier  '@@'  '('  'begin'  _identifier  •  ')'  …
    //   1:  'covergroup'  _identifier  '@@'  '('  'begin'  (hierarchical_identifier  _identifier)  •  ')'  …  (precedence: 'hierarchical_identifier')
    //   2:  'covergroup'  _identifier  '@@'  '('  (block_event_expression  'begin'  _identifier)  •  ')'  …
    ['block_event_expression', 'hierarchical_identifier'],


    // $.property_spec first seq element is $.optional($.clocking_event), and last .$.property_expr
    //
    // 'expect'  '('  clocking_event  property_expr  •  ')'  …
    // 1:  'expect'  '('  (property_expr  clocking_event  property_expr)  •  ')'  …  (precedence: 'property_expr')
    // 2:  'expect'  '('  (property_spec  clocking_event  property_expr)  •  ')'  …  (precedence: 'property_spec')
    ['property_spec', 'property_expr'],


    // $._simple_type is used for static casting, choose $.constant_primary to reduce the number of conflicts
    //
    // ''{'  class_scope  _identifier  •  ':'  …
    // 1:  ''{'  (_simple_type  class_scope  _identifier)  •  ':'  …      (precedence: '_simple_type')
    // 2:  ''{'  (constant_primary  class_scope  _identifier)  •  ':'  …  (precedence: 'constant_primary')
    ['constant_primary', '_simple_type'],


    // $.timeunits_declaration belongs to the declaration rule, better than to a separate $._non_port_interface_item
    // The same applies to programs
    //
    // interface_nonansi_header  timeunits_declaration  •  ';'  …
    // 1:  (interface_declaration  interface_nonansi_header  timeunits_declaration  •  interface_declaration_repeat1  'endinterface'  ':'  interface_identifier)  (precedence: 'interface_declaration')
    // 2:  (interface_declaration  interface_nonansi_header  timeunits_declaration  •  interface_declaration_repeat1  'endinterface')                             (precedence: 'interface_declaration')
    // 3:  interface_nonansi_header  (_non_port_interface_item  timeunits_declaration)  •  ';'  …                                                                 (precedence: '_non_port_interface_item')
    ['interface_declaration', '_non_port_interface_item'],
    ['program_declaration', '_non_port_program_item'],


    // That constuct in a genvar corresponds to the initialization
    //
    // 'for'  '('  _identifier  •  '='  …
    // 1:  'for'  '('  (genvar_initialization  _identifier  •  '='  constant_expression)  (precedence: 'genvar_initialization')
    // 2:  'for'  '('  (hierarchical_identifier  _identifier)  •  '='  …                  (precedence: 'hierarchical_identifier')
    ['genvar_initialization', 'hierarchical_identifier'],


    // This is illegal synax, so choose any
    //
    //   module_nonansi_header  'var'  _identifier  '='  implicit_class_handle  '.'  •  '$root'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  (class_qualifier  implicit_class_handle  '.')  •  '$root'  …                        (precedence: 'class_qualifier')
    //   2:  module_nonansi_header  'var'  _identifier  '='  (variable_lvalue  implicit_class_handle  '.'  •  hierarchical_identifier  select)  (precedence: 'variable_lvalue')
    //   3:  module_nonansi_header  'var'  _identifier  '='  (variable_lvalue  implicit_class_handle  '.'  •  hierarchical_identifier)           (precedence: 'variable_lvalue')
    ['variable_lvalue', 'class_qualifier'],


    // Even though the class_scope is implicitly a data_type, it should not be needed to set it as a node
    //
    //   _identifier  '#'  '('  class_scope  •  simple_identifier  …
    //   1:  _identifier  '#'  '('  (class_qualifier  class_scope)  •  simple_identifier  …      (precedence: 'class_qualifier')
    //   2:  _identifier  '#'  '('  (data_type  class_scope  •  _identifier  data_type_repeat1)  (precedence: 'data_type')
    //   3:  _identifier  '#'  '('  (data_type  class_scope  •  _identifier)                     (precedence: 'data_type')
    ['class_qualifier', 'data_type'],


    // If there is only one identifier, without package scope/parenthesis, consider it a hierarchical identifier with one level of nesting
    //
    // _identifier  •  ';'  …
    // 1:  (hierarchical_identifier  _identifier)  •  ';'  …  (precedence: 'hierarchical_identifier')
    // 2:  (tf_call  _identifier)  •  ';'  …                  (precedence: 'tf_call')
    ['hierarchical_identifier', 'tf_call'],
    //   'var'  _identifier  '='  hierarchical_identifier  •  ';'  …
    //   1:  'var'  _identifier  '='  (primary  hierarchical_identifier)  •  ';'  …  (precedence: 'primary')
    //   2:  'var'  _identifier  '='  (tf_call  hierarchical_identifier)  •  ';'  …  (precedence: 'tf_call')
    ['primary', 'tf_call'],
    //   'var'  _identifier  '='  hierarchical_identifier  •  '++'  …
    //   1:  'var'  _identifier  '='  (tf_call  hierarchical_identifier  •  list_of_arguments)  (precedence: 'tf_call')
    //   2:  'var'  _identifier  '='  (variable_lvalue  hierarchical_identifier)  •  '++'  …    (precedence: 'variable_lvalue')
    ['variable_lvalue', 'tf_call'],


    // '$' is out of LRM, included only to support select in queue variables
    //
    // 'sequence'  sequence_identifier  ';'  '##'  '['  constant_expression  ':'  '$'  •  ']'  …
    // 1:  'sequence'  sequence_identifier  ';'  '##'  '['  (cycle_delay_const_range_expression  constant_expression  ':'  '$')  •  ']'  …  (precedence: 'cycle_delay_const_range_expression')
    // 2:  'sequence'  sequence_identifier  ';'  '##'  '['  constant_expression  ':'  (constant_primary  '$')  •  ']'  …                    (precedence: 'constant_primary')
    ['cycle_delay_const_range_expression', 'constant_primary'],


    // $root' as a primary is out of LRM, used to cover a corner case in sv-tests
    //
    // '$root'  •  '.'  …
    // 1:  (hierarchical_identifier  '$root'  •  '.'  _identifier)                                   (precedence: 'hierarchical_identifier')
    // 2:  (hierarchical_identifier  '$root'  •  '.'  hierarchical_identifier_repeat1  _identifier)  (precedence: 'hierarchical_identifier')
    // 3:  (primary  '$root')  •  '.'  …                                                             (precedence: 'primary')
    ['hierarchical_identifier', 'primary'],


    // Consider $.timeunits_declaration part of the module declaration. The 3rd option is to support snippets of code.
    //
    // module_nonansi_header  timeunits_declaration  •  'resetall_compiler_directive_token1'  …
    // 1:  (module_declaration  module_nonansi_header  timeunits_declaration  •  module_declaration_repeat1  'endmodule'  ':'  module_identifier)  (precedence: 'module_declaration')
    // 2:  (module_declaration  module_nonansi_header  timeunits_declaration  •  module_declaration_repeat1  'endmodule')                           (precedence: 'module_declaration')
    // 3:  module_nonansi_header  (_non_port_module_item  timeunits_declaration)  •  'resetall_compiler_directive_token1'  …                        (precedence: '_non_port_module_item')
    ['module_declaration', '_non_port_module_item'],


    // randomize with constraint expressions -> constraint_set (emtpy)
    //
    // 'randomize'  'with'  '{'  expression  '->'  '{'  '}'  •  '+'  …
    // 1:  'randomize'  'with'  '{'  expression  '->'  (constraint_set  '{'  '}')  •  '+'  …
    // 2:  'randomize'  'with'  '{'  expression  '->'  (empty_unpacked_array_concatenation  '{'  '}')  •  '+'  …
    ['constraint_set', 'empty_unpacked_array_concatenation'],


    // Out of LRM support for macros in identifiers
    //
    // text_macro_usage  •  '['  …
    // 1:  (_directives  text_macro_usage)  •  '['  …                                         (precedence: '_directives')
    // 2:  (hierarchical_identifier_repeat1  text_macro_usage  •  constant_bit_select  '.')  (precedence: 'hierarchical_identifier')
    ['hierarchical_identifier', '_directives'],


    // Set the one higher in the syntax tree: _incomplete_class_scoped_type
    //
    // 'typedef'  _identifier  •  '::'  …
    // 1:  'typedef'  (class_type  _identifier  •  class_type_repeat1)                                     (precedence: 'class_type')
    // 2:  'typedef'  (class_type  _identifier)  •  '::'  …                                                (precedence: 'class_type')
    // 3:  'typedef'  (_incomplete_class_scoped_type  _identifier  •  '::'  _type_identifier_or_class_type)  (precedence: '_incomplete_class_scoped_type')
    // 4:  'typedef'  (package_scope  _identifier  •  '::')                                                (precedence: 'package_scope')
    ['_incomplete_class_scoped_type', 'class_type'],
    ['_incomplete_class_scoped_type', 'package_scope'],


    // Make class_type include LHS of the ::
    //
    // 'typedef'  _identifier  '::'  _identifier  •  '\'  …
    // 1:  'typedef'  _identifier  '::'  (class_type  _identifier)  •  '\'  …                     (precedence: 'class_type')
    // 2:  'typedef'  _identifier  '::'  (_type_identifier_or_class_type  _identifier)  •  '\'  …
    // 3:  'typedef'  _identifier  (class_type_repeat1  '::'  _identifier)  •  '\'  …             (precedence: 'class_type')
    ['class_type_repeat1', '_type_identifier_or_class_type'],


    // Save one extra level of unnecessary nesting with data_type
    //
    // 'typedef'  class_type  •  '\'  …
    // 1:  'typedef'  (_type_identifier_or_class_type  class_type)  •  '\'  …  (precedence: '_type_identifier_or_class_type')
    // 2:  'typedef'  (data_type  class_type)  •  '\'  …                       (precedence: 'data_type')
    ['_type_identifier_or_class_type', 'data_type'],


    // Set the one higher in the syntax tree: _type_identifier_or_class_type
    //
    // 'typedef'  _identifier  •  '\'  …
    // 1:  'typedef'  (_type_identifier_or_class_type  _identifier)  •  '\'  …  (precedence: '_type_identifier_or_class_type')
    // 2:  'typedef'  (class_type  _identifier)  •  '\'  …                      (precedence: 'class_type')
    // 3:  'typedef'  (data_type  _identifier)  •  '\'  …                       (precedence: 'data_type')
    ['_type_identifier_or_class_type', 'class_type'],


    // Both options are illegal syntax, consequence of adding '$' as a primary for queue dimension indexing.
    // Choose param_expression since primary is legal only for queue dimensions.
    //
    // '`'  _identifier  '('  '$'  •  ','  …
    // 1:  '`'  _identifier  '('  (param_expression  '$')  •  ','  …  (precedence: 'param_expression')
    // 2:  '`'  _identifier  '('  (primary  '$')  •  ','  …           (precedence: 'primary')
    ['param_expression', 'primary'],

    // Both options are illegal syntax, consequence of adding '$' as a primary for queue dimension indexing.
    // Choose value_range since primary is legal only for queue dimensions.
    //
    // '('  expression  'inside'  '{'  '['  '$'  •  ':'  …
    // 1:  '('  expression  'inside'  '{'  '['  (primary  '$')  •  ':'  …                    (precedence: 'primary')
    // 2:  '('  expression  'inside'  '{'  (value_range  '['  '$'  •  ':'  expression  ']')
    ['value_range', 'primary'],


    // Second option is illegal syntax, consequence of adding '$' as a primary for queue dimension indexing.
    // Choose constant_param_expression since constant_primary is legal only for queue dimensions.
    // - See: test/corpus/sv-tests/chapter-20/20.6--isunbounded.txt
    //
    // 'localparam'  _identifier  '='  '$'  •  ';'  …
    // 1:  'localparam'  _identifier  '='  (constant_param_expression  '$')  •  ';'  …
    // 2:  'localparam'  _identifier  '='  (constant_primary  '$')  •  ';'  …           (precedence: 'constant_primary')
    ['constant_param_expression', 'constant_primary'],


    // 1st option follows the $.list_of_param_assignments branch in $.local_parameter_declaration
    // 2nd option follows the $.type_parameter_declaration
    // Seems more logical to set the 2nd path for a type reference
    //
    // 'localparam'  _identifier  '='  type_reference  •  ';'  …
    // 1:  'localparam'  _identifier  '='  (constant_primary  type_reference)  •  ';'  …  (precedence: 'constant_primary')
    // 2:  'localparam'  _identifier  '='  (data_type  type_reference)  •  ';'  …         (precedence: 'data_type')
    ['data_type', 'constant_primary'],


    // Seems illegal syntax, so choose whichever
    //
    // 'expect'  '('  '##'  type_reference  •  ''{'  …
    // 1:  'expect'  '('  '##'  (_assignment_pattern_expression_type  type_reference)  •  ''{'  …  (precedence: '_assignment_pattern_expression_type')
    // 2:  'expect'  '('  '##'  (constant_primary  type_reference)  •  ''{'  …                     (precedence: 'constant_primary')
    ['constant_primary', '_assignment_pattern_expression_type'],


    // Sequence instances. Choose the first one to include the right associative 'iff' expression
    //
    // _identifier  name_of_instance  '('  expression  •  'iff'  …
    // 1:  _identifier  name_of_instance  '('  (event_expression  expression  •  'iff'  expression)  (precedence: 'event_expression')
    // 2:  _identifier  name_of_instance  '('  (expression_or_dist  expression)  •  'iff'  …         (precedence: 'expression_or_dist')
    ['event_expression', 'expression_or_dist'],


    // Consider standalone assign as continuous and not procedural
    //
    //   'assign'  variable_assignment  •  ';'  …
    //   1:  'assign'  (list_of_variable_assignments  variable_assignment)  •  ';'  …      (precedence: 'list_of_variable_assignments')
    //   2:  (procedural_continuous_assignment  'assign'  variable_assignment)  •  ';'  …  (precedence: 'procedural_continuous_assignment')
    ['list_of_variable_assignments', 'procedural_continuous_assignment'],


    // Consider a snippet concurrent_assertion_statement as non-procedural
    //
    // _concurrent_assertion_statement  •  ';'  …
    // 1:  (_procedural_assertion_statement  _concurrent_assertion_statement)  •  ';'  …
    // 2:  (concurrent_assertion_item  _concurrent_assertion_statement)  •  ';'  …        (precedence: 'concurrent_assertion_item')
    ['concurrent_assertion_item', '_procedural_assertion_statement'],
    // _deferred_immediate_assertion_statement  •  ';'  …
    // 1:  (_immediate_assertion_statement  _deferred_immediate_assertion_statement)  •  ';'  …
    // 2:  (deferred_immediate_assertion_item  _deferred_immediate_assertion_statement)  •  ';'  …
    ['deferred_immediate_assertion_item', '_immediate_assertion_statement'],


    // \ refers to a possible escaped identifier. The conflict has to do with two identifiers one after the other.
    // Therefore since the first has no bit_select at all consider it a bind_target_scope
    //
    // 'bind'  _identifier  •  '\'  …
    // 1:  'bind'  (bind_target_scope  _identifier)  •  '\'  …
    // 2:  'bind'  (hierarchical_identifier  _identifier)  •  '\'  …  (precedence: 'hierarchical_identifier')
    ['bind_target_scope', 'hierarchical_identifier'],


    // Covergroup and cross cover conflicts. Check $.select_expression comments:
    // Give $.covergroup_value_range and $.select_expression precedence over nodes lower in the syntax tree
    //
    // 'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '('  expression  •  ')'  …
    // 1:  'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '('  (covergroup_value_range  expression)  •  ')'  …  (precedence: 'covergroup_value_range')
    // 2:  'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '('  (mintypmax_expression  expression)  •  ')'  …    (precedence: 'mintypmax_expression')
    ['covergroup_value_range', 'mintypmax_expression'],
    // 'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '{'  expression  •  ','  …
    // 1:  'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '{'  (covergroup_value_range  expression)  •  ','  …                  (precedence: 'covergroup_value_range')
    // 2:  'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  (concatenation  '{'  expression  •  assignment_pattern_repeat1  '}')  (precedence: 'concatenation')
    ['covergroup_value_range', 'concatenation'],
    // 'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '('  '['  '$'  •  ':'  …
    // 1:  'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '('  '['  (primary  '$')  •  ':'  …                                           (precedence: 'primary')
    // 2:  'covergroup'  _identifier  ';'  'coverpoint'  expression  '{'  bins_keyword  _identifier  '='  '('  (covergroup_value_range  '['  '$'  •  ':'  _covergroup_expression  ']')  (precedence: 'covergroup_value_range')
    ['covergroup_value_range', 'primary'],
    // 'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  expression  •  ')'  …
    // 1:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  (mintypmax_expression  expression)  •  ')'  …  (precedence: 'mintypmax_expression')
    // 2:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  (select_expression  expression)  •  ')'  …     (precedence: 'select_expression', associativity: Right)
    ['select_expression', 'mintypmax_expression'],
    // 'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  expression  'matches'  '$'  •  ';'  …
    // 1:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  (select_expression  expression  'matches'  '$')  •  ';'  …  (precedence: 'select_expression', associativity: Right)
    // 2:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  expression  'matches'  (primary  '$')  •  ';'  …            (precedence: 'primary')
    ['select_expression', 'primary'],
    // 'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  _identifier  •  ')'  …
    // 1:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  (constant_primary  _identifier)  •  ')'  …         (precedence: 'constant_primary')
    // 2:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  (hierarchical_identifier  _identifier)  •  ')'  …  (precedence: 'hierarchical_identifier')
    // 3:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  (select_expression  _identifier)  •  ')'  …        (precedence: 'select_expression')
    // 4:  'covergroup'  _identifier  ';'  'cross'  list_of_cross_items  '{'  bins_keyword  _identifier  '='  '('  (tf_call  _identifier)  •  ')'  …                  (precedence: 'tf_call')
    ['select_expression', 'constant_primary'],
    ['select_expression', 'hierarchical_identifier'],
    ['select_expression', 'tf_call'],


    // Leave these two standalone to avoid having to replicate code with function 'list_of_args'
    ['property_list_of_arguments'],
    ['sequence_list_of_arguments'],
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


    // In $.continuous_assign:
    // - $.delay3 follows the branch $.list_of_net_assignments
    // - $.delay_control follows the branch of $.list_of_variable_assignments
    // Since a variable could also be driven from a $.continuous_assign, check more tokens to see which one is correct
    //
    // 'assign'  '#'  delay_value  •  '{'  …
    // 1:  'assign'  (delay3  '#'  delay_value)  •  '{'  …
    // 2:  'assign'  (delay_control  '#'  delay_value)  •  '{'  …
    [$.delay3, $.delay_control],


    // Needed to detect extern module/interface/program
    [$.module_declaration, $._module_header],
    [$.interface_declaration, $._interface_header],
    [$.program_declaration, $._program_header],


    // SystemVerilog allows continuous assignment both to nets and logic variables:
    //
    // module_nonansi_header  'assign'  hierarchical_identifier  •  '.'  …
    // 1:  module_nonansi_header  'assign'  (ps_or_hierarchical_net_identifier  hierarchical_identifier)  •  '.'  …
    // 2:  module_nonansi_header  'assign'  (variable_lvalue  hierarchical_identifier  •  select)
    [$.net_lvalue, $.variable_lvalue],


    // This one had no option if setting right associativity on conditional_statement to handle recursion
    //
    //   module_nonansi_header  'initial'  'if'  '('  cond_predicate  ')'  statement_or_null  'else'  'if'  '('  cond_predicate  ')'  statement_or_null  •  'endmodule'  …
    //     1:  module_nonansi_header  'initial'  'if'  '('  cond_predicate  ')'  statement_or_null  'else'  (conditional_statement  'if'  '('  cond_predicate  ')'  statement_or_null)  •  'endmodule'  …          (precedence: 0, associativity: Right)
    //     2:  module_nonansi_header  'initial'  'if'  '('  cond_predicate  ')'  statement_or_null  (conditional_statement_repeat1  'else'  'if'  '('  cond_predicate  ')'  statement_or_null)  •  'endmodule'  …
    [$.conditional_statement],


    // This is a real conflict, since it needs more lookeahead to distinguish between a hierarchical identifier
    // and a select construct, that might have some members with non-constant expressions
    //
    //   module_nonansi_header  'initial'  _identifier  •  '.'  …
    //   1:  module_nonansi_header  'initial'  (hierarchical_identifier  _identifier)  •  '.'  …       (precedence: 'hierarchical_identifier')
    //   2:  module_nonansi_header  'initial'  (hierarchical_identifier_repeat1  _identifier  •  '.')  (precedence: 'hierarchical_identifier')
    [$.hierarchical_identifier],


    // From the LRM:
    //   In a data_declaration, it shall be illegal to omit the explicit data_type
    //   before a list_of_variable_decl_assignments unless the var keyword is used.
    //
    //   'input'  'var'  •  '\'  …
    //   1:  'input'  (variable_port_type  'var'  •  data_type_or_implicit)
    //   2:  'input'  (variable_port_type  'var')  •  '\'  …
    [$.variable_port_type],


    // Setting left associativity (prec.left) prevents having more than 1 bit_select dimension:
    //
    // module_nonansi_header  'var'  _identifier  '='  hierarchical_identifier  bit_select1_repeat1  •  '['  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  hierarchical_identifier  (bit_select  bit_select1_repeat1)  •  '['  …
    //   2:  module_nonansi_header  'var'  _identifier  '='  hierarchical_identifier  (bit_select1_repeat1  bit_select1_repeat1  •  bit_select1_repeat1)
    [$.bit_select],
    //   '['  _identifier  constant_bit_select1_repeat1  •  '['  …
    //   1:  '['  _identifier  (constant_bit_select  constant_bit_select1_repeat1)  •  '['  …
    //   2:  '['  _identifier  (constant_bit_select1_repeat1  constant_bit_select1_repeat1  •  constant_bit_select1_repeat1)
    [$.constant_bit_select],


    // Examples:
    //   input my_custom_nettype_identifier ... my_signal (user defined net)
    //   input my_signal ... (net)
    //   input my_type_t ... my_signal (variable)
    //
    //   _module_header1  '('  port_direction  •  simple_identifier  …
    //   1:  _module_header1  '('  (net_port_header  port_direction  •  net_port_type)           (precedence: 'net_port_header')
    //   2:  _module_header1  '('  (net_port_header  port_direction)  •  simple_identifier  …     (precedence: 'net_port_header')
    //   3:  _module_header1  '('  (variable_port_header  port_direction  •  variable_port_type)  (precedence: 'variable_port_header')
    [$.net_port_header, $.variable_port_header],


    // Be able to differentiate between:
    //  input wire logic ...
    //  input wire identifier
    //
    //   _module_header1  '('  net_type  •  simple_identifier  …
    //   1:  _module_header1  '('  (net_port_type  net_type  •  data_type_or_implicit)  (precedence: 'net_port_type')
    //   2:  _module_header1  '('  (net_port_type  net_type)  •  simple_identifier  …    (precedence: 'net_port_type')
    [$.net_port_type],


    // It could be a case or case-inside expression (case inside does not accept casex/casez expressions)
    //
    // module_nonansi_header  'initial'  'case'  •  '('  …
    // 1:  module_nonansi_header  'initial'  (case_keyword  'case')  •  '('  …
    // 2:  module_nonansi_header  'initial'  (case_statement  'case'  •  '('  case_expression  ')'  'inside'  case_statement_repeat3  'endcase')
    [$.case_statement, $.case_keyword],


    // Implicit can be both options. Until checking following token 'super' it's not possible to know when it ends
    //
    //   module_nonansi_header  'initial'  'this'  •  '.'  …
    //   1:  module_nonansi_header  'initial'  (implicit_class_handle  'this'  •  '.'  'super')  (precedence: 'implicit_class_handle')
    //   2:  module_nonansi_header  'initial'  (implicit_class_handle  'this')  •  '.'  …        (precedence: 'implicit_class_handle')
    [$.implicit_class_handle],


    // Avoid adding associativity in data_type so that it can differentiate between data_types/net_types
    //
    //   'function'  function_identifier  '('  class_scope  _identifier  •  '['  …
    //   1:  'function'  function_identifier  '('  (data_type  class_scope  _identifier  •  data_type_repeat1)  (precedence: 'data_type')
    //   2:  'function'  function_identifier  '('  (data_type  class_scope  _identifier)  •  '['  …             (precedence: 'data_type')
    [$.data_type],


    // Need to set these to allow correct parsing of external and static methods
    //
    // module_nonansi_header  'var'  _identifier  '='  _identifier  parameter_value_assignment  •  '::'  …
    //   1:  module_nonansi_header  'var'  _identifier  '='  (class_type  _identifier  parameter_value_assignment  •  class_type_repeat1)
    //   2:  module_nonansi_header  'var'  _identifier  '='  (class_type  _identifier  parameter_value_assignment)  •  '::'  …
    [$.class_type],


    // Need to know if the optional select is to be included in the primary
    //
    // '['  class_qualifier  hierarchical_identifier  •  '.'  …
    // 1:  '['  (primary  class_qualifier  hierarchical_identifier  •  select)  (precedence: 'primary')
    // 2:  '['  (primary  class_qualifier  hierarchical_identifier)  •  '.'  …  (precedence: 'primary')
    [$.primary],


    // select branches include repetition of bit_select and dot-member identifier
    //
    // '('  hierarchical_identifier  '.'  _identifier  •  '.'  …
    // 1:  '('  hierarchical_identifier  (select  '.'  _identifier)  •  '.'  …
    // 2:  '('  hierarchical_identifier  (select_repeat1  '.'  _identifier)  •  '.'  …
    [$.select],


    // Impossible to know with just one :: if it's a class_type or an ambiguity of class_type/package_scope
    //
    // _identifier  •  '::'  …
    // 1:  (class_type  _identifier  •  class_type_repeat1)
    // 2:  (class_type  _identifier)  •  '::'  …
    // 3:  (package_scope  _identifier  •  '::')             (precedence: 'package_scope')
    [$.class_type, $.package_scope],


    // It's not possible to know after class declaration if 'virtual' belongs to a virtual interface or a virtual method
    //
    // 'class'  _identifier  ';'  class_item_qualifier  •  'virtual'  …
    // 1:  'class'  _identifier  ';'  (_property_qualifier  class_item_qualifier)  •  'virtual'  …
    // 2:  'class'  _identifier  ';'  (method_qualifier  class_item_qualifier)  •  'virtual'  …     (precedence: 'method_qualifier')
    [$._property_qualifier, $.method_qualifier],


    // `pragma could be followed by:
    // - pragma_keyword
    // - pragma_keyword = pragma_value
    // - pragma_value
    //
    // 'pragma_token1'  pragma_name  simple_identifier  •  ';'  …
    // 1:  'pragma_token1'  pragma_name  (_identifier  simple_identifier)  •  ';'  …
    // 2:  'pragma_token1'  pragma_name  (pragma_keyword  simple_identifier)  •  ';'  …
    [$.pragma_keyword, $._identifier],


    // There are cases where it's not possible to know if it's constat or not without more tokens
    //
    // '('  '$'  •  ':'  …
    // 1:  '('  (constant_primary  '$')  •  ':'  …  (precedence: 'constant_primary')
    // 2:  '('  (primary  '$')  •  ':'  …           (precedence: 'primary')
    [$.constant_primary, $.primary],


    // Checker ordered port instantiation, with args being $._property_actual_arg (not sure which one so set conflict)
    //
    // _identifier  name_of_instance  '('  sequence_expr  •  ')'  …
    // 1:  _identifier  name_of_instance  '('  (_sequence_actual_arg  sequence_expr)  •  ')'  …  (precedence: '_sequence_actual_arg')
    // 2:  _identifier  name_of_instance  '('  (property_expr  sequence_expr)  •  ')'  …         (precedence: 'property_expr')
    [$.property_expr, $._sequence_actual_arg],


    // DPI C name of task/function
    //
    // 'import'  dpi_spec_string  'context'  •  c_identifier  …
    // 1:  'import'  dpi_spec_string  (dpi_function_import_property  'context')  •  c_identifier  …
    // 2:  'import'  dpi_spec_string  (dpi_task_import_property  'context')  •  c_identifier  …
    [$.dpi_function_import_property, $.dpi_task_import_property],


    // Packed array of user defined type <-> Hierarchical identifier with constant select
    //   mytype_t [0:15] (my_var)        <->       my_hier_var[10]
    //
    //   'function'  function_identifier  ';'  _identifier  •  '['  …
    //   1:  'function'  function_identifier  ';'  (data_type  _identifier  •  data_type_repeat1)                                (precedence: 'data_type')
    //   2:  'function'  function_identifier  ';'  (hierarchical_identifier  _identifier)  •  '['  …                             (precedence: 'hierarchical_identifier')
    //   3:  'function'  function_identifier  ';'  (hierarchical_identifier_repeat1  _identifier  •  constant_bit_select  '.')  (precedence: 'hierarchical_identifier')
    [$.data_type, $.hierarchical_identifier],


    // Conflict between 1st/3rd branch of $.system_tf_call choice.
    // Since there is no $.clocking_event it should be the 1st one, but it's much simpler to resolve it with dynamic precedences
    //
    //   module_nonansi_header  'initial'  system_tf_identifier  '('  expression  •  ')'  …
    //   1:  module_nonansi_header  'initial'  (system_tf_call  system_tf_identifier  '('  expression  •  ')')
    //   2:  module_nonansi_header  'initial'  system_tf_identifier  '('  (list_of_arguments  expression)  •  ')'  …
    [$.system_tf_call, $.list_of_arguments],


    // Even though the example seems very specific, there are many constructs that happen in lvalue and primary (both lvalue and rvalue)
    // It is needed more context info to know what the construct is
    // Trying to fix this conflict statically makes many tests fail
    //
    // '{'  streaming_concatenation  •  ','  …
    // 1:  '{'  (primary  streaming_concatenation)  •  ','  …          (precedence: 'primary')
    // 2:  '{'  (variable_lvalue  streaming_concatenation)  •  ','  …  (precedence: 'variable_lvalue')
    [$.primary, $.variable_lvalue],


    // No chance of ignoring this conflict
    //
    // _module_header  '('  _description_repeat1  _identifier  •  ')'  …
    // 1:  _module_header  '('  _description_repeat1  (ansi_port_declaration  _identifier)  •  ')'  …  (precedence: 'ansi_port_declaration')
    // 2:  _module_header  '('  _description_repeat1  (ansi_port_declaration  _identifier)  •  ')'  …  (precedence: 'ansi_port_declaration')
    [$.ansi_port_declaration],


    // Seems there could be something wrong in the precedences of $.property_expr since there is a mix of named/numeric precedences.
    // Adding the conflict fixes parsing errors in doulos/133.4_property
    //
    // 'expect'  '('  clocking_event  property_expr  •  'iff'  …
    // 1:  'expect'  '('  (property_expr  clocking_event  property_expr)  •  'iff'  …              (precedence: 'property_expr')
    // 2:  'expect'  '('  clocking_event  (property_expr  property_expr  •  'iff'  property_expr)  (precedence: 11, associativity: Right)
    [$.property_expr],


    // _forward_type branch would refer to the type of declaration that is done
    // at the beginning of a file so that the enum is known to be declared
    // (e.g.what is done with classes on the UVM)
    //
    // 'typedef'  'enum'  •  '\'  …
    // 1:  'typedef'  (_forward_type  'enum')  •  '\'  …
    // 2:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  '}'  data_type_repeat1)                     (precedence: 'data_type')
    // 3:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  '}')                                        (precedence: 'data_type')
    // 4:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  data_type_repeat3  '}'  data_type_repeat1)  (precedence: 'data_type')
    // 5:  'typedef'  (data_type  'enum'  •  enum_base_type  '{'  enum_name_declaration  data_type_repeat3  '}')                     (precedence: 'data_type')
    [$._forward_type, $.data_type],


    // case / case inside / conditional generate
    // 'case'  •  '('  …
    // 1:  (case_generate_construct  'case'  •  '('  constant_expression  ')'  case_generate_item  'endcase')
    // 2:  (case_generate_construct  'case'  •  '('  constant_expression  ')'  case_generate_item  case_generate_construct_repeat1  'endcase')
    // 3:  (case_keyword  'case')  •  '('  …
    // 4:  (case_statement  'case'  •  '('  case_expression  ')'  'inside'  case_statement_repeat3  'endcase')
    [$.case_generate_construct, $.case_statement, $.case_keyword],


    // $.delay_control -> Net declaration delay
    // $.param_expression -> class variable paramemeter (e.g: uvm_config_db #(some_type))
    //
    //   _identifier  '#'  '('  mintypmax_expression  •  ')'  …
    //   1:  _identifier  '#'  '('  (param_expression  mintypmax_expression)  •  ')'  …  (precedence: 'param_expression')
    //   2:  _identifier  (delay_control  '#'  '('  mintypmax_expression  •  ')')
    [$.delay_control, $.param_expression],


    // Modport declaration:
    // Differentiate between a single modport or list of modports, e.g:
    //   modport A (output .P(r[3:0]), input .Q(x), R); -> 1 declaration with 1 elem (output .P), 1 decl with 2 elems (input .Q, R)
    //
    // interface_nonansi_header  'modport'  modport_identifier  '('  port_direction  modport_simple_port  •  ','  …
    // 1:  interface_nonansi_header  'modport'  modport_identifier  '('  (modport_simple_ports_declaration  port_direction  modport_simple_port  •  modport_simple_ports_declaration_repeat1)
    // 2:  interface_nonansi_header  'modport'  modport_identifier  '('  (modport_simple_ports_declaration  port_direction  modport_simple_port)  •  ','  …
    [$.modport_simple_ports_declaration],
    [$.modport_tf_ports_declaration],


    // This is misleading. It is needed to detect standalone 'this' as a (primary) instead of as
    // a (primary (implicit_class_handle)).
    //
    // 'this'  •  '.'  …
    // 1:  (implicit_class_handle  'this'  •  '.'  'super')  (precedence: 'implicit_class_handle')
    // 2:  (implicit_class_handle  'this')  •  '.'  …        (precedence: 'implicit_class_handle')
    // 3:  (primary  'this')  •  '.'  …                      (precedence: 'primary')
    [$.primary, $.implicit_class_handle],


    // There could be macros both in constant_expressions and expressions, e.g:
    // - constant_expression: test/files/uvm/1800.2-2020-2.0/src/base/uvm_packer.svh:42
    // - expression:          test/files/uvm/1800.2-2020-2.0/src/base/uvm_root.svh:1181
    //
    // '('  text_macro_usage  •  ':'  …
    // 1:  '('  (constant_expression  text_macro_usage)  •  ':'  …
    // 2:  '('  (expression  text_macro_usage)  •  ':'  …
    [$.constant_expression, $.expression],


    // $.nonrange_select would cover the $.dynamic_array_new case
    //
    // hierarchical_identifier  bit_select  •  '='  …
    // 1:  hierarchical_identifier  (nonrange_select  bit_select)  •  '='  …
    // 2:  hierarchical_identifier  (select  bit_select)  •  '='  …
    [$.select, $.nonrange_select],


    // 1) Corresponds to declaration of a variable via $.list_of_variable_decl_assignments
    // 2) Corresponds to declaration of a port via $.list_of_variable_identifiers
    //
    // 'var'  _identifier  unsized_dimension  •  ';'  …
    // 1:  'var'  (variable_decl_assignment  _identifier  unsized_dimension)  •  ';'  …
    // 2:  'var'  _identifier  (_variable_dimension  unsized_dimension)  •  ';'  …       (precedence: '_variable_dimension')
    [$.variable_decl_assignment, $._variable_dimension],
    // The same happens below
    //
    // 'var'  _identifier  unsized_dimension  •  '['  …
    // 1:  'var'  (variable_decl_assignment  _identifier  unsized_dimension  •  ansi_port_declaration_repeat2  '='  dynamic_array_new)
    // 2:  'var'  (variable_decl_assignment  _identifier  unsized_dimension  •  ansi_port_declaration_repeat2)
    // 3:  'var'  _identifier  (_variable_dimension  unsized_dimension)  •  '['  …                                                      (precedence: '_variable_dimension')  4:  'var'  _identifier  (packed_dimension  unsized_dimension)  •  '['  …                                                         (precedence: 'packed_dimension')
    // 4:  'var'  _identifier  (packed_dimension  unsized_dimension)  •  '['  …                                                         (precedence: 'packed_dimension')
    [$.variable_decl_assignment, $.packed_dimension, $._variable_dimension],


    // Out of LRM, macros on hierarchical identifiers or method prefixes
    //
    // text_macro_usage  •  '.'  …
    // 1:  (_method_call_root  text_macro_usage)  •  '.'  …             (precedence: '_method_call_root')
    // 2:  (hierarchical_identifier_repeat1  text_macro_usage  •  '.')  (precedence: 'hierarchical_identifier')
    [$._method_call_root, $.hierarchical_identifier],


    // Leave as a conflict since there are many options possible for this rule
    //
    // 'expect'  '('  sequence_expr_repeat1  •  '##'  …
    // 1:  'expect'  '('  (sequence_expr  sequence_expr_repeat1)  •  '##'  …                        (precedence: 'sequence_expr')
    // 2:  'expect'  '('  (sequence_expr_repeat1  sequence_expr_repeat1  •  sequence_expr_repeat1)
    [$.sequence_expr],


    // Leave conflict to consider declarations below as variables (data_declaration).
    // Conflict is solved using dynamic precedences
    //
    // _identifier  _identifier  •  ';'  …
    // 1:  _identifier  (list_of_interface_identifiers  _identifier)  •  ';'  …
    // 2:  _identifier  (net_decl_assignment  _identifier)  •  ';'  …
    [$.list_of_interface_identifiers, $.net_decl_assignment],


    // Need more lookahead to know if extern declaration refers to class constraint or to method
    //
    //   'class'  _identifier  ';'  'extern'  •  'static'  …
    //   1:  'class'  _identifier  ';'  (class_method  'extern'  •  class_method_repeat1  _method_prototype  ';')       (precedence: 'class_method')
    //   2:  'class'  _identifier  ';'  (class_method  'extern'  •  class_method_repeat1  class_constructor_prototype)  (precedence: 'class_method')
    //   3:  'class'  _identifier  ';'  (constraint_prototype_qualifier  'extern')  •  'static'  …
    [$.class_method, $.constraint_prototype_qualifier],


    // Give dynamically higher precedence to nonblocking assignemnt than to clockvar for snippets.
    // Leave conflict to avoid errors in expressions like:
    //  - CB1.Data <= ##2 Int_Data;
    //
    //   hierarchical_identifier  •  '<='  …
    // 1:  (clockvar  hierarchical_identifier)  •  '<='  …
    // 2:  (variable_lvalue  hierarchical_identifier)  •  '<='  …  (precedence: 'variable_lvalue')
    [$.clockvar, $.variable_lvalue],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // 'assign'  hierarchical_identifier  '.'  _identifier  •  '.'  …
    // 1:  'assign'  hierarchical_identifier  (constant_select_repeat1  '.'  _identifier)  •  '.'  …  (precedence: 'constant_select')
    // 2:  'assign'  hierarchical_identifier  (select_repeat1  '.'  _identifier)  •  '.'  …
    [$.select, $.constant_select],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // 'assign'  hierarchical_identifier  '['  constant_range  •  ']'  …
    // 1:  'assign'  hierarchical_identifier  '['  (_constant_part_select_range  constant_range)  •  ']'  …  (precedence: '_constant_part_select_range')
    // 2:  'assign'  hierarchical_identifier  '['  (_part_select_range  constant_range)  •  ']'  …
    [$._constant_part_select_range, $._part_select_range],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // '@'  '('  hierarchical_identifier  '('  ','  •  ','  …
    // 1:  '@'  '('  hierarchical_identifier  '('  (list_of_arguments_repeat1  ',')  •  ','  …
    // 2:  '@'  '('  hierarchical_identifier  '('  (sequence_list_of_arguments_repeat1  ',')  •  ','  …
    [$.sequence_list_of_arguments, $.list_of_arguments],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // '('  hierarchical_identifier  •  '.'  …
    // 1:  '('  (primary  hierarchical_identifier  •  select)          (precedence: 'primary')
    // 2:  '('  (primary  hierarchical_identifier)  •  '.'  …          (precedence: 'primary')
    // 3:  '('  (tf_call  hierarchical_identifier)  •  '.'  …          (precedence: 'tf_call', associativity: Right)
    // 4:  '('  (variable_lvalue  hierarchical_identifier  •  select)  (precedence: 'variable_lvalue')
    [$.tf_call, $.primary, $.variable_lvalue],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // '['  hierarchical_identifier  •  '.'  …
    // 1:  '['  (primary  hierarchical_identifier  •  select)  (precedence: 'primary')
    // 2:  '['  (primary  hierarchical_identifier)  •  '.'  …  (precedence: 'primary')
    // 3:  '['  (tf_call  hierarchical_identifier)  •  '.'  …  (precedence: 'tf_call', associativity: Right)
    [$.tf_call, $.primary],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // 'ref'  _identifier  •  '\'  …
    // 1:  'ref'  (class_type  _identifier)  •  '\'  …  (precedence: 'class_type')
    // 2:  'ref'  (data_type  _identifier)  •  '\'  …   (precedence: 'data_type')
    [$.data_type, $.class_type],


    // Didn't test but makes sense to leave the conflict to avoid errors
    //
    // 'type'  '('  package_scope  _identifier  •  ')'  …
    // 1:  'type'  '('  (class_type  package_scope  _identifier)  •  ')'  …               (precedence: 'class_type')
    // 2:  'type'  '('  (data_type  package_scope  _identifier)  •  ')'  …                (precedence: 'data_type')
    // 3:  'type'  '('  (tf_call  package_scope  _identifier)  •  ')'  …                  (precedence: 'tf_call', associativity: Right)
    // 4:  'type'  '('  package_scope  (hierarchical_identifier  _identifier)  •  ')'  …  (precedence: 'hierarchical_identifier')
    [$.data_type, $.class_type, $.tf_call, $.hierarchical_identifier],


    // Probably should be fixed by using numeric precedences for the $.expression_or_dist, but seems too much effort for the price
    //
    // 'randomize'  'with'  '{'  expression  '->'  expression  •  ';'  …
    // 1:  'randomize'  'with'  '{'  (expression  expression  '->'  expression)  •  ';'  …          (precedence: 22, associativity: Left)
    // 2:  'randomize'  'with'  '{'  expression  '->'  (expression_or_dist  expression)  •  ';'  …  (precedence: 'expression_or_dist')
    [$.expression_or_dist, $.expression],


    // Support expressions inside bit_select
    [$.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.tf_call, $.constant_primary],
    [$.data_type, $.class_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.data_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.data_type, $.class_type, $.tf_call, $.constant_primary],


    // Support for static method calls
    [$.class_type, $.tf_call, $.hierarchical_identifier, $.package_scope],
    [$.class_type, $.tf_call, $.hierarchical_identifier],
    [$._incomplete_class_scoped_type, $.class_type, $.tf_call, $.hierarchical_identifier, $.package_scope],
    [$.class_scope, $._method_call_root],


    // Support method call with bit_select
    [$.class_qualifier, $.select],
    [$.select, $.hierarchical_identifier],
    [$.constant_select, $.hierarchical_identifier],
    [$._method_call_root, $.primary],
    [$._method_call_root, $.primary, $.class_qualifier, $.variable_lvalue],
    [$._method_call_root, $.primary, $.class_qualifier],


    // Method calls inside indexes
    [$.class_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.class_type, $.tf_call, $.constant_primary, $.net_lvalue, $.hierarchical_identifier],
    [$.class_type, $.tf_call, $.net_lvalue, $.hierarchical_identifier],
    [$.interface_port_declaration, $.class_type, $.tf_call, $.hierarchical_identifier],
    [$.interface_port_declaration, $.hierarchical_identifier],


    // Class_type as data_type
    [$.class_type, $.module_instantiation],
    [$.data_type, $.class_type, $.net_port_type],
    [$.data_type, $.class_type, $.tf_port_item],
    [$.interface_port_header, $.data_type, $.class_type, $.net_port_type],
    [$.net_declaration, $.data_type, $.class_type, $.module_instantiation],
    [$.net_declaration, $.data_type, $.class_type],
    [$.nettype_declaration, $.data_type, $.class_type],


    // local:: class_qualifier
    [$._simple_type, $._assignment_pattern_expression_type, $.class_qualifier],


    // Add nested static class access on LHS
    [$._assignment_pattern_expression_type, $.class_qualifier],


    // Inout/ref/interface ports
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type, $.module_instantiation],
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type],


    // Constant function call
    [$.constant_function_call, $.primary],
    [$._simple_type, $._structure_pattern_key, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._simple_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._simple_type, $.tf_call, $.constant_primary],
    [$.concatenation, $.stream_expression],
    [$._simple_type, $.pattern, $._structure_pattern_key, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._assignment_pattern_expression_type, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$._assignment_pattern_expression_type, $.tf_call, $.constant_primary],


    //  $.class_new branch in $.blocking_assignment
    [$.blocking_assignment, $.class_qualifier],
    [$.blocking_assignment, $._method_call_root, $.primary, $.class_qualifier, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.blocking_assignment, $.clockvar, $.tf_call, $.primary, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.blocking_assignment, $.variable_lvalue, $.nonrange_variable_lvalue],
    [$.blocking_assignment, $.variable_lvalue],
    [$.blocking_assignment, $.primary, $.variable_lvalue, $.nonrange_variable_lvalue],


    // After removing $.constant_primary from $.casting_type to fix issue with concatenation on RHS
    [$._simple_type, $.blocking_assignment, $._assignment_pattern_expression_type, $.class_qualifier],
    [$.blocking_assignment, $.clockvar, $.primary, $.variable_lvalue, $.nonrange_variable_lvalue],


    // Sequences/Properties/Assertions
    // Attempting to set named priorities on the ones below gave errors on some assertion tests
    [$.expression_or_dist, $.mintypmax_expression],
    [$.property_expr, $.sequence_expr],
    [$.cover_sequence_statement, $.sequence_expr],


    // Checkers
    [$.data_type, $.class_type, $.checker_instantiation],
    [$.named_port_connection, $.named_checker_port_connection],
    [$.expression_or_dist, $.ordered_port_connection, $.event_expression],
    [$.expression_or_dist, $.named_port_connection, $.event_expression],


    // Primitives (fixed partially with named precedences)
    // -  The only one left is the $.net_lvalue / $.variable_lvalue that exists above on purpose
    [$.tf_call, $.primary, $.net_lvalue, $.variable_lvalue],


    // UDP declaration
    [$.combinational_entry, $._seq_input_list], // Could have the same syntax for $.sequential_body and $.combinational_body
    [$.list_of_udp_port_identifiers],


    // UDP instantiation
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type, $.module_instantiation, $.checker_instantiation, $.udp_instantiation],
    [$.net_declaration, $.data_type, $.class_type, $.module_instantiation, $.udp_instantiation],
    [$.interface_port_declaration, $.net_declaration, $.data_type, $.class_type, $.module_instantiation, $.udp_instantiation],
    [$.delay2, $.delay_control],
    [$.delay2, $.param_expression],
    [$.delay2, $.delay_control, $.param_expression],


    // Give higher prioriy dynamically to $.module_instantiation than to $.udp_instantiation
    [$.constant_primary, $.net_lvalue],
    [$.net_lvalue, $.hierarchical_identifier],
    [$.property_instance, $.sequence_instance, $.tf_call, $.net_lvalue, $.hierarchical_identifier],
    [$.property_instance, $.sequence_instance, $.tf_call, $.primary, $.net_lvalue],
    [$.tf_call, $.constant_primary, $.net_lvalue, $.hierarchical_identifier],
    [$.tf_call, $.net_lvalue, $.hierarchical_identifier],
    [$.tf_call, $.primary, $.net_lvalue],


    // Specify
    [$.parallel_path_description, $.parallel_edge_sensitive_path_description, $.list_of_path_inputs],
    [$.parallel_edge_sensitive_path_description, $.list_of_path_inputs],
    [$.tf_call, $.module_path_primary, $.hierarchical_identifier],
    [$.parallel_path_description, $.list_of_path_inputs],
    [$.specify_input_terminal_descriptor, $.specify_output_terminal_descriptor],
    [$.unary_operator, $.unary_module_path_operator],
    [$.constant_function_call, $.module_path_primary, $.primary],
    [$.module_path_primary, $.primary_literal],
    [$.tf_call, $.constant_primary, $.module_path_primary, $.hierarchical_identifier],
    [$.module_path_primary, $.primary],
    [$.casting_type, $.path_delay_expression, $.constant_primary],
    [$.full_path_description, $.full_edge_sensitive_path_description],
    [$.parallel_path_description, $.parallel_edge_sensitive_path_description],
    [$.scalar_timing_check_condition, $.mintypmax_expression],
    [$.constant_function_call, $.module_path_primary],


    // After inlining of identifiers
    [$._property_actual_arg, $.sequence_list_of_arguments],
    [$._simple_type, $._assignment_pattern_expression_type, $.constant_primary, $.class_qualifier],
    [$._simple_type, $._structure_pattern_key],
    [$.clocking_event, $.hierarchical_identifier],
    [$.expression_or_dist, $.event_expression, $.list_of_arguments],
    [$.property_instance, $.sequence_instance, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.property_instance, $.sequence_instance, $.tf_call, $.hierarchical_identifier],
    [$.property_instance, $.sequence_instance, $.tf_call],
    [$.property_list_of_arguments, $.sequence_list_of_arguments, $.list_of_arguments],
    [$.sequence_instance, $.tf_call, $.constant_primary, $.hierarchical_identifier],
    [$.sequence_instance, $.tf_call, $.hierarchical_identifier],
    [$.sequence_instance, $.tf_call],


    // Allow constraint blocks on text_macro_usage
    [$.constraint_block, $.empty_unpacked_array_concatenation],

  ],

});

