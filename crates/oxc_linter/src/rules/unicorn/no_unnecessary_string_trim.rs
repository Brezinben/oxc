use oxc_ast::{
    AstKind,
    ast::{
        Argument, Class, Expression, IdentifierReference, TSLiteral, TSType, TSTypeAnnotation,
        TSTypeName, TSTypeOperatorOperator, VariableDeclarator,
    },
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_semantic::SymbolId;
use oxc_span::Span;
use oxc_syntax::{
    identifier::is_white_space, line_terminator::is_line_terminator, operator::UnaryOperator,
};

use crate::{
    AstNode,
    ast_util::{get_declaration_of_variable, get_symbol_id_of_variable, variable_declaration_kind},
    context::LintContext,
    rule::Rule,
    utils::{
        call_uses_optional_chain, is_import_from_module, is_import_symbol, static_string_value,
    },
};

fn no_unnecessary_string_trim_diagnostic(
    span: Span,
    method: &str,
    replacement: &str,
) -> OxcDiagnostic {
    OxcDiagnostic::warn(format!("Unnecessary `String#trim()` before `String#{method}()`"))
        .with_help(format!("Use `String#{replacement}()` instead."))
        .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct NoUnnecessaryStringTrim;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Reports `String#trim()` before `String#startsWith()` or `String#endsWith()`, and asks
    /// for `String#trimStart()` or `String#trimEnd()` instead.
    ///
    /// The rule does not report a call with a second argument, because the position can make
    /// the other side of the string observable. The rule also does not report `trim()` with
    /// arguments, optional chaining, a receiver that is known not to be a string, or a zod
    /// `z.string()` schema. It does not report a search value that it cannot resolve statically,
    /// a `startsWith()` search value that ends with whitespace, or an `endsWith()` search value
    /// that starts with whitespace.
    ///
    /// ### Why is this bad?
    ///
    /// Without a position argument, `startsWith()` compares only the start of the string, and
    /// `endsWith()` compares only the end. If the search value has no whitespace at the other
    /// end, the whitespace that `trim()` removes there does not change the result.
    /// `trimStart()` and `trimEnd()` show the intent better and do less work.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```js
    /// value.trim().startsWith('-');
    /// value.trim().endsWith('-');
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```js
    /// value.trimStart().startsWith('-');
    /// value.trimEnd().endsWith('-');
    /// value.trim().startsWith('-', 1);
    /// value.trim().startsWith('foo ');
    /// ```
    NoUnnecessaryStringTrim,
    unicorn,
    pedantic,
    fix,
    version = "next",
    short_description = "Disallow `String#trim()` before `String#startsWith()` or `String#endsWith()`.",
);

impl Rule for NoUnnecessaryStringTrim {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let AstKind::CallExpression(call_expr) = node.kind() else {
            return;
        };
        let Expression::StaticMemberExpression(outer_member) =
            call_expr.callee.without_parentheses()
        else {
            return;
        };
        let method = outer_member.property.name.as_str();
        let replacement = match method {
            "startsWith" => "trimStart",
            "endsWith" => "trimEnd",
            _ => return,
        };
        if call_expr.arguments.len() > 1 || call_expr.arguments.iter().any(Argument::is_spread) {
            return;
        }

        let Expression::CallExpression(trim_call) = outer_member.object.without_parentheses()
        else {
            return;
        };
        let Expression::StaticMemberExpression(trim_member) =
            trim_call.callee.without_parentheses()
        else {
            return;
        };
        if trim_member.property.name.as_str() != "trim"
            || !trim_call.arguments.is_empty()
            || call_uses_optional_chain(call_expr)
        {
            return;
        }

        let receiver = &trim_member.object;
        if is_static_non_string(receiver, ctx)
            || is_known_non_string(receiver, ctx)
            || is_zod_string_call(receiver, ctx)
        {
            return;
        }

        if let Some(search_value) = call_expr.arguments.first().and_then(Argument::as_expression)
            && !is_search_value_safe(search_value, method == "startsWith", ctx)
        {
            return;
        }

        let span = trim_member.property.span;
        ctx.diagnostic_with_fix(
            no_unnecessary_string_trim_diagnostic(span, method, replacement),
            |fixer| fixer.replace(span, replacement),
        );
    }
}

fn const_declarator_init<'a>(
    declarator: &'a VariableDeclarator<'a>,
    ctx: &LintContext<'a>,
) -> Option<&'a Expression<'a>> {
    declarator.init.as_ref().filter(|_| {
        declarator.id.is_binding_identifier()
            && variable_declaration_kind(declarator, ctx).is_const()
    })
}

fn resolve_const<'a>(expr: &'a Expression<'a>, ctx: &LintContext<'a>) -> &'a Expression<'a> {
    let expr = expr.get_inner_expression();
    if let Expression::Identifier(ident) = expr
        && let Some(declaration) = get_declaration_of_variable(ident, ctx)
        && let AstKind::VariableDeclarator(declarator) = declaration.kind()
        && let Some(init) = const_declarator_init(declarator, ctx)
    {
        return init.get_inner_expression();
    }
    expr
}

/// These values are not strings, and their string form never starts or ends with whitespace.
fn is_non_string_primitive(expr: &Expression, ctx: &LintContext) -> bool {
    match expr {
        Expression::NumericLiteral(_)
        | Expression::BigIntLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_) => true,
        Expression::Identifier(ident) => {
            ident.name.as_str() == "undefined" && ctx.is_reference_to_global_variable(ident)
        }
        Expression::UnaryExpression(unary) => match unary.operator {
            UnaryOperator::Void => unary.argument.is_literal(),
            UnaryOperator::UnaryNegation => matches!(
                unary.argument,
                Expression::NumericLiteral(_) | Expression::BigIntLiteral(_)
            ),
            _ => false,
        },
        _ => false,
    }
}

fn is_static_non_string<'a>(expr: &'a Expression<'a>, ctx: &LintContext<'a>) -> bool {
    let expr = resolve_const(expr, ctx);
    matches!(
        expr,
        Expression::ArrayExpression(_)
            | Expression::ArrowFunctionExpression(_)
            | Expression::ClassExpression(_)
            | Expression::FunctionExpression(_)
            | Expression::ObjectExpression(_)
            | Expression::RegExpLiteral(_)
    ) || is_non_string_primitive(expr, ctx)
}

fn is_search_value_safe<'a>(
    expr: &'a Expression<'a>,
    is_starts_with: bool,
    ctx: &LintContext<'a>,
) -> bool {
    let expr = resolve_const(expr, ctx);
    if is_non_string_primitive(expr, ctx) {
        return true;
    }
    let Some(value) = static_string_value(expr) else {
        return false;
    };
    let is_js_whitespace = |c: char| is_white_space(c) || is_line_terminator(c);
    if is_starts_with {
        !value.ends_with(is_js_whitespace)
    } else {
        !value.starts_with(is_js_whitespace)
    }
}

/// The syntactic part of upstream `isKnownNonString`. It reads the type annotations of
/// parameters and variables, `as` and `<T>` assertions, `const` initializers, the return
/// types of called functions, both branches of a conditional expression, and the last
/// expression of a sequence.
fn is_known_non_string<'a>(expr: &Expression<'a>, ctx: &LintContext<'a>) -> bool {
    let mut state = Resolution { visited: Vec::new(), steps: MAX_RESOLVE_STEPS };
    expression_string_type(expr, ctx, &mut state) == Some(false)
}

/// A symbol hop budget for one receiver. The cycle guard alone does not bound the work: a
/// crafted chain like `type A1 = A0 | A0; type A2 = A1 | A1; ...` doubles it at each step.
const MAX_RESOLVE_STEPS: u32 = 64;

struct Resolution {
    /// The symbols on the current path, to stop a symbol that refers to itself.
    visited: Vec<SymbolId>,
    steps: u32,
}

/// The functions below return `None` when the syntax does not tell if the value is a string.
fn expression_string_type<'a>(
    expr: &Expression<'a>,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
) -> Option<bool> {
    match expr {
        Expression::ParenthesizedExpression(e) => expression_string_type(&e.expression, ctx, state),
        Expression::TSSatisfiesExpression(e) => expression_string_type(&e.expression, ctx, state),
        Expression::TSNonNullExpression(e) => expression_string_type(&e.expression, ctx, state),
        Expression::TSAsExpression(e) => type_string_type(&e.type_annotation, ctx, state)
            .or_else(|| expression_string_type(&e.expression, ctx, state)),
        Expression::TSTypeAssertion(e) => type_string_type(&e.type_annotation, ctx, state)
            .or_else(|| expression_string_type(&e.expression, ctx, state)),
        Expression::SequenceExpression(e) => {
            expression_string_type(e.expressions.last()?, ctx, state)
        }
        Expression::ConditionalExpression(e) => {
            let consequent = expression_string_type(&e.consequent, ctx, state)?;
            let alternate = expression_string_type(&e.alternate, ctx, state)?;
            (consequent == alternate).then_some(consequent)
        }
        Expression::Identifier(ident) => {
            let symbol_id = single_declaration_symbol(ident, ctx)?;
            visit_symbol(symbol_id, ctx, state, |declaration, state| match declaration {
                AstKind::FormalParameter(param) if param.pattern.is_binding_identifier() => {
                    type_annotation_string_type(param.type_annotation.as_deref(), ctx, state)
                }
                AstKind::VariableDeclarator(declarator)
                    if declarator.id.is_binding_identifier() =>
                {
                    type_annotation_string_type(declarator.type_annotation.as_deref(), ctx, state)
                        .or_else(|| {
                            let init = const_declarator_init(declarator, ctx)?;
                            expression_string_type(init, ctx, state)
                        })
                }
                _ => None,
            })
        }
        Expression::CallExpression(call) => {
            let Expression::Identifier(callee) = call.callee.without_parentheses() else {
                return None;
            };
            let symbol_id = single_declaration_symbol(callee, ctx)?;
            if ctx.scoping().symbol_is_mutated(symbol_id) {
                return None;
            }
            visit_symbol(symbol_id, ctx, state, |declaration, state| {
                let (return_type, has_type_parameters) = match declaration {
                    AstKind::Function(function) => {
                        (&function.return_type, function.type_parameters.is_some())
                    }
                    AstKind::VariableDeclarator(declarator) => {
                        let mut init = const_declarator_init(declarator, ctx)?;
                        loop {
                            init = match init {
                                Expression::ParenthesizedExpression(e) => &e.expression,
                                Expression::TSSatisfiesExpression(e) => &e.expression,
                                Expression::TSNonNullExpression(e) => &e.expression,
                                _ => break,
                            };
                        }
                        match init {
                            Expression::FunctionExpression(function) => {
                                (&function.return_type, function.type_parameters.is_some())
                            }
                            Expression::ArrowFunctionExpression(function) => {
                                (&function.return_type, function.type_parameters.is_some())
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                };
                if has_type_parameters {
                    return None;
                }
                type_annotation_string_type(return_type.as_deref(), ctx, state)
            })
        }
        _ => None,
    }
}

fn single_declaration_symbol(ident: &IdentifierReference, ctx: &LintContext) -> Option<SymbolId> {
    let symbol_id = get_symbol_id_of_variable(ident, ctx)?;
    ctx.scoping().symbol_redeclarations(symbol_id).is_empty().then_some(symbol_id)
}

fn visit_symbol<'a>(
    symbol_id: SymbolId,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
    resolve: impl FnOnce(AstKind<'a>, &mut Resolution) -> Option<bool>,
) -> Option<bool> {
    if state.steps == 0 || state.visited.contains(&symbol_id) {
        return None;
    }
    state.steps -= 1;
    state.visited.push(symbol_id);
    let declaration = ctx.nodes().kind(ctx.scoping().symbol_declaration(symbol_id));
    let result = resolve(declaration, state);
    state.visited.pop();
    result
}

fn type_annotation_string_type<'a>(
    annotation: Option<&TSTypeAnnotation<'a>>,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
) -> Option<bool> {
    type_string_type(&annotation?.type_annotation, ctx, state)
}

fn type_string_type<'a>(
    ts_type: &TSType<'a>,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
) -> Option<bool> {
    match ts_type {
        TSType::TSStringKeyword(_) => Some(true),
        // Like upstream, a template literal type such as `foo` is not a string literal here.
        TSType::TSLiteralType(literal) => {
            Some(matches!(literal.literal, TSLiteral::StringLiteral(_)))
        }
        TSType::TSBigIntKeyword(_)
        | TSType::TSBooleanKeyword(_)
        | TSType::TSNeverKeyword(_)
        | TSType::TSNumberKeyword(_)
        | TSType::TSSymbolKeyword(_)
        | TSType::TSVoidKeyword(_)
        | TSType::TSNullKeyword(_)
        | TSType::TSUndefinedKeyword(_)
        | TSType::TSArrayType(_)
        | TSType::TSTupleType(_)
        | TSType::TSTypeLiteral(_)
        | TSType::TSFunctionType(_)
        | TSType::TSConstructorType(_) => Some(false),
        TSType::TSParenthesizedType(e) => type_string_type(&e.type_annotation, ctx, state),
        TSType::TSTypeOperatorType(e) if e.operator == TSTypeOperatorOperator::Readonly => {
            type_string_type(&e.type_annotation, ctx, state)
        }
        TSType::TSUnionType(union) => {
            let mut types = union.types.iter();
            let first = type_string_type(types.next()?, ctx, state)?;
            types.all(|t| type_string_type(t, ctx, state) == Some(first)).then_some(first)
        }
        TSType::TSIntersectionType(intersection) => intersection_string_type(
            intersection.types.iter().map(|t| type_string_type(t, ctx, state)),
        ),
        TSType::TSTypeReference(reference) => {
            type_name_string_type(&reference.type_name, ctx, state)
        }
        _ => None,
    }
}

fn intersection_string_type(types: impl Iterator<Item = Option<bool>>) -> Option<bool> {
    let mut all_non_string = true;
    for t in types {
        match t {
            Some(true) => return Some(true),
            Some(false) => {}
            None => all_non_string = false,
        }
    }
    all_non_string.then_some(false)
}

fn type_name_string_type<'a>(
    type_name: &TSTypeName<'a>,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
) -> Option<bool> {
    let TSTypeName::IdentifierReference(ident) = type_name else {
        return None;
    };
    let symbol_id = get_symbol_id_of_variable(ident, ctx)?;
    visit_symbol(symbol_id, ctx, state, |declaration, state| match declaration {
        AstKind::TSTypeAliasDeclaration(alias) => {
            type_string_type(&alias.type_annotation, ctx, state)
        }
        AstKind::TSTypeParameter(param) => {
            param.constraint.as_ref().and_then(|t| type_string_type(t, ctx, state))
        }
        AstKind::TSInterfaceDeclaration(interface) => intersection_string_type(
            interface
                .extends
                .iter()
                .map(|heritage| type_name_string_type(&heritage.type_name, ctx, state)),
        ),
        AstKind::Class(class) => class_string_type(class, ctx, state),
        _ => None,
    })
}

fn class_string_type<'a>(
    class: &Class<'a>,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
) -> Option<bool> {
    class
        .heritage_expression()
        .map_or(Some(false), |super_class| class_reference_string_type(super_class, ctx, state))
}

fn class_reference_string_type<'a>(
    expr: &Expression<'a>,
    ctx: &LintContext<'a>,
    state: &mut Resolution,
) -> Option<bool> {
    match expr.without_parentheses() {
        Expression::Identifier(ident) => {
            let symbol_id = get_symbol_id_of_variable(ident, ctx)?;
            visit_symbol(symbol_id, ctx, state, |declaration, state| match declaration {
                AstKind::VariableDeclarator(declarator) => {
                    let init = const_declarator_init(declarator, ctx)?;
                    class_reference_string_type(init, ctx, state)
                }
                AstKind::Class(class) => class_string_type(class, ctx, state),
                _ => None,
            })
        }
        Expression::ClassExpression(class) => class_string_type(class, ctx, state),
        _ => None,
    }
}

/// `z.string().trim()` is a zod schema method, not `String#trim()`.
fn is_zod_string_call(expr: &Expression, ctx: &LintContext) -> bool {
    let Expression::CallExpression(call) = expr.get_inner_expression() else {
        return false;
    };
    let Expression::StaticMemberExpression(member) = call.callee.without_parentheses() else {
        return false;
    };
    if !call.arguments.is_empty() || member.property.name.as_str() != "string" {
        return false;
    }
    let Expression::Identifier(ident) = member.object.without_parentheses() else {
        return false;
    };
    let Some(symbol_id) = get_symbol_id_of_variable(ident, ctx) else {
        return false;
    };
    if ctx.scoping().symbol_flags(symbol_id).is_type_import() {
        return false;
    }
    is_import_symbol(ident, "zod", "z", ctx)
        || (is_import_from_module(ident, "zod", ctx)
            && matches!(
                ctx.nodes().kind(ctx.scoping().symbol_declaration(symbol_id)),
                AstKind::ImportNamespaceSpecifier(_)
            ))
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        r#"import {z} from "zod"; z.string().trim().startsWith("asdf")"#,
        r#"import {z as schema} from "zod"; schema.string().trim().startsWith("asdf")"#,
        r#"import {"z" as schema} from "zod"; schema.string().trim().startsWith("asdf")"#,
        r#"import * as z from "zod"; z.string().trim().endsWith("asdf")"#,
        r#"import {z} from "zod"; (z.string() as unknown).trim().startsWith("-");"#,
        r#"import {z} from "zod"; (z.string() satisfies unknown).trim().startsWith("-");"#,
        r#"import {z} from "zod"; z.string()!.trim().startsWith("-");"#,
        r#"import {z} from "zod"; (<unknown>z.string()).trim().startsWith("-");"#,
        r#"foo.trimStart().startsWith("-")"#,
        r#"foo.trimEnd().endsWith("-")"#,
        r#"foo.trim().includes("-")"#,
        r#"foo.trim().startsWith("-", 1)"#,
        r#"foo.trim().endsWith("-", 1)"#,
        r#"foo.trim(" ").startsWith("-")"#,
        "foo.trim().startsWith(prefix)",
        "foo.trim().endsWith(suffix)",
        r#"foo.trim().startsWith("foo ")"#,
        "foo.trim().startsWith(`foo `)",
        r#"foo.trim().endsWith(" foo")"#,
        "foo.trim().endsWith(` foo`)",
        "const modes = new Set(['foo']); modes.clear(); value.trim().startsWith(modes.size ? 'x' : 'x ')",
        "const modes = new Set(['foo']); modes.clear(); value.trim().endsWith((modes.size && 'x') || suffix)",
        "const object = {value: true}; Object.defineProperty(object, 'value', {get() { return false; }}); value.trim().startsWith(object.value ? 'x' : suffix)",
        "const modes = new Set(['foo']); modes.clear(); value.trim().startsWith((modes.size ? 'x' : 'x ') as string)",
        r#"const prefix = "foo "; foo.trim().startsWith(prefix)"#,
        r#"const suffix = " foo"; foo.trim().endsWith(suffix)"#,
        r#"foo.trim().startsWith("foo" + " ")"#,
        "foo.trim().startsWith(/foo/)",
        r#"foo.trim().endsWith(Symbol("foo"))"#,
        r#"const value = {trim() { return "ok"; }}; value.trim().startsWith("o")"#,
        r#"const value = []; value.trim().startsWith("-")"#,
        r#"const value = 1; value.trim().startsWith("-")"#,
        r#"foo.trim().startsWith("foo " as const)"#,
        "foo.trim().startsWith(...argumentsArray)",
        "foo.trim().endsWith(...argumentsArray)",
        r#"foo.trim().startsWith("-", ...positions)"#,
        r#"foo.trim().endsWith("-", ...positions)"#,
        r#"foo.trim().startsWith?.("-")"#,
        r#"foo.trim().endsWith?.("-")"#,
        r#"foo.trim?.().startsWith("-")"#,
        r#"foo.trim?.().endsWith("-")"#,
        r#"foo?.trim().startsWith("-")"#,
        r#"foo.trim()?.startsWith("-")"#,
        r#"foo?.trim()?.startsWith("-")"#,
        r#"foo?.trim().endsWith("-")"#,
        r#"foo.trim()?.endsWith("-")"#,
        r#"foo?.trim()?.endsWith("-")"#,
        r#"foo?.bar.trim().startsWith("-")"#,
        r#"(foo?.bar).trim().startsWith("-")"#,
        r#"(foo?.bar).baz.trim().startsWith("-")"#,
        r#"foo.trim()["startsWith"]("-")"#,
        r#"foo["trim"]().startsWith("-")"#,
        r#"trim().startsWith("-")"#,
        r#"foo.trim.startsWith("-")"#,
        r#"new foo.trim().startsWith("-")"#,
        r#"function foo(value: number[]) { value.trim().startsWith("-"); }"#,
        r#"interface Token { trim(): Token; startsWith(v: string): boolean } function foo(value: Token) { value.trim().startsWith("-"); }"#,
        r#"class Path { trim() { return this; } startsWith(v: string) { return true; } } function foo(value: Path) { value.trim().startsWith("/"); }"#,
        r#"type Id = number; function foo(value: Id) { value.trim().startsWith("-"); }"#,
        r#"function foo(value: number | boolean) { value.trim().startsWith("-"); }"#,
        r#"interface Token { trim(): Token; startsWith(v: string): boolean } const t = next() as Token; t.trim().startsWith("-")"#,
        r#"interface Token { trim(): Token; startsWith(v: string): boolean } function parse(): Token { return null as any; } parse().trim().startsWith("-")"#,
        r#"function foo(a: number, b: boolean[]) { (c ? a : b).trim().startsWith("-"); }"#,
        r#"function foo(value: number) { (bar(), value).trim().startsWith("-"); }"#,
        r#"interface Base { trim(): Base } interface Token extends Base { startsWith(v: string): boolean } function foo(value: Token) { value.trim().startsWith("-"); }"#,
        r#"class Base {} class Path extends Base { trim() { return this; } } function foo(value: Path) { value.trim().startsWith("/"); }"#,
        "function foo(value: `foo`) { value.trim().startsWith(\"-\"); }",
        r#"function f(v: number & {}) { v.trim().startsWith("-"); }"#,
        r#"function f(v: readonly string[]) { v.trim().startsWith("-"); }"#,
        r#"function f<T extends number>(v: T) { v.trim().startsWith("-"); }"#,
        r#"(foo as number).trim().startsWith("-")"#,
        r#"/a/.trim().startsWith("-")"#,
    ];

    let fail = vec![
        r#"foo.trim().startsWith("-")"#,
        r#"foo.trim().endsWith("-")"#,
        "foo.trim().startsWith()",
        "foo.trim().endsWith()",
        r#"" foo ".trim().startsWith("f")"#,
        r#"" foo ".trim().endsWith("o")"#,
        r#"foo.trim().startsWith(" foo")"#,
        r#"foo.trim().endsWith("foo ")"#,
        "foo.trim().startsWith(`foo`)",
        "foo.trim().endsWith(`foo`)",
        r#"const prefix = "foo"; foo.trim().startsWith(prefix)"#,
        r#"const suffix = "foo"; foo.trim().endsWith(suffix)"#,
        r#"foo.trim().startsWith("foo" + "bar")"#,
        r#"import {z} from "other-package"; z.string().trim().startsWith("-")"#,
        r#"import * as z from "other-package"; z.string().trim().startsWith("-")"#,
        r#"import {z} from "zod/mini"; z.string().trim().startsWith("-")"#,
        r#"import z from "zod"; z.string().trim().startsWith("-")"#,
        r#"import {z} from "zod"; z["string"]().trim().startsWith("-")"#,
        r#"import {z} from "zod"; z.string("argument").trim().startsWith("-")"#,
        r#"import {z} from "zod"; z.number().trim().startsWith("-")"#,
        r#"import {z} from "zod"; function foo(z) { z.string().trim().startsWith("-"); }"#,
        r#"import type {z} from "zod"; z.string().trim().startsWith("-");"#,
        r#"import type * as z from "zod"; z.string().trim().endsWith("-");"#,
        r#"import z = require("zod"); z.string().trim().startsWith("-");"#,
        "foo.trim().startsWith(undefined)",
        "foo.trim().endsWith(void 0)",
        "const search = undefined; foo.trim().startsWith(search)",
        "foo.trim().startsWith(123)",
        "foo.trim().endsWith(false)",
        "foo.trim().startsWith(null)",
        "foo.trim().endsWith(1n)",
        r#"(foo).trim().startsWith("-")"#,
        r#"(foo.trim()).startsWith("-")"#,
        r#"if (foo.trim().startsWith("-")) {
                bar();
            }"#,
        r#"foo
                // comment
                .trim/* comment */()
                .startsWith("-")"#,
        r#"function foo(value: string) { value.trim().endsWith("-"); }"#,
        r#"function foo(value: string) { value.trim().startsWith("-" as const); }"#,
        r#"function foo(value: string) { value.trim().endsWith("-" satisfies string); }"#,
        r#"type Text = string; function foo(value: Text) { value.trim().startsWith("-"); }"#,
        r#"type A = A; function foo(value: A) { value.trim().startsWith("-"); }"#,
        r#"function foo(value: string | number) { value.trim().startsWith("-"); }"#,
        "foo.trim().startsWith(-1)",
        r#"function foo(a: string, b: number) { (c ? a : b).trim().startsWith("-"); }"#,
        r#"type A0 = number; type A1 = A0 | A0; type A2 = A1 | A1; type A3 = A2 | A2; type A4 = A3 | A3; type A5 = A4 | A4; type A6 = A5 | A5; type A7 = A6 | A6; type A8 = A7 | A7; function foo(value: A8) { value.trim().startsWith("-"); }"#,
    ];

    let fix = vec![
        (r#"foo.trim().startsWith("-")"#, r#"foo.trimStart().startsWith("-")"#),
        (r#"foo.trim().endsWith("-")"#, r#"foo.trimEnd().endsWith("-")"#),
        ("foo.trim().startsWith()", "foo.trimStart().startsWith()"),
        ("foo.trim().endsWith()", "foo.trimEnd().endsWith()"),
        (r#"" foo ".trim().startsWith("f")"#, r#"" foo ".trimStart().startsWith("f")"#),
        (r#"" foo ".trim().endsWith("o")"#, r#"" foo ".trimEnd().endsWith("o")"#),
        (r#"foo.trim().startsWith(" foo")"#, r#"foo.trimStart().startsWith(" foo")"#),
        (r#"foo.trim().endsWith("foo ")"#, r#"foo.trimEnd().endsWith("foo ")"#),
        ("foo.trim().startsWith(`foo`)", "foo.trimStart().startsWith(`foo`)"),
        ("foo.trim().endsWith(`foo`)", "foo.trimEnd().endsWith(`foo`)"),
        (
            r#"const prefix = "foo"; foo.trim().startsWith(prefix)"#,
            r#"const prefix = "foo"; foo.trimStart().startsWith(prefix)"#,
        ),
        (
            r#"const suffix = "foo"; foo.trim().endsWith(suffix)"#,
            r#"const suffix = "foo"; foo.trimEnd().endsWith(suffix)"#,
        ),
        (r#"foo.trim().startsWith("foo" + "bar")"#, r#"foo.trimStart().startsWith("foo" + "bar")"#),
        (
            r#"import {z} from "other-package"; z.string().trim().startsWith("-")"#,
            r#"import {z} from "other-package"; z.string().trimStart().startsWith("-")"#,
        ),
        (
            r#"import * as z from "other-package"; z.string().trim().startsWith("-")"#,
            r#"import * as z from "other-package"; z.string().trimStart().startsWith("-")"#,
        ),
        (
            r#"import {z} from "zod/mini"; z.string().trim().startsWith("-")"#,
            r#"import {z} from "zod/mini"; z.string().trimStart().startsWith("-")"#,
        ),
        (
            r#"import z from "zod"; z.string().trim().startsWith("-")"#,
            r#"import z from "zod"; z.string().trimStart().startsWith("-")"#,
        ),
        (
            r#"import {z} from "zod"; z["string"]().trim().startsWith("-")"#,
            r#"import {z} from "zod"; z["string"]().trimStart().startsWith("-")"#,
        ),
        (
            r#"import {z} from "zod"; z.string("argument").trim().startsWith("-")"#,
            r#"import {z} from "zod"; z.string("argument").trimStart().startsWith("-")"#,
        ),
        (
            r#"import {z} from "zod"; z.number().trim().startsWith("-")"#,
            r#"import {z} from "zod"; z.number().trimStart().startsWith("-")"#,
        ),
        (
            r#"import {z} from "zod"; function foo(z) { z.string().trim().startsWith("-"); }"#,
            r#"import {z} from "zod"; function foo(z) { z.string().trimStart().startsWith("-"); }"#,
        ),
        (
            r#"import type {z} from "zod"; z.string().trim().startsWith("-");"#,
            r#"import type {z} from "zod"; z.string().trimStart().startsWith("-");"#,
        ),
        (
            r#"import type * as z from "zod"; z.string().trim().endsWith("-");"#,
            r#"import type * as z from "zod"; z.string().trimEnd().endsWith("-");"#,
        ),
        (
            r#"import z = require("zod"); z.string().trim().startsWith("-");"#,
            r#"import z = require("zod"); z.string().trimStart().startsWith("-");"#,
        ),
        ("foo.trim().startsWith(undefined)", "foo.trimStart().startsWith(undefined)"),
        ("foo.trim().endsWith(void 0)", "foo.trimEnd().endsWith(void 0)"),
        (
            "const search = undefined; foo.trim().startsWith(search)",
            "const search = undefined; foo.trimStart().startsWith(search)",
        ),
        ("foo.trim().startsWith(123)", "foo.trimStart().startsWith(123)"),
        ("foo.trim().endsWith(false)", "foo.trimEnd().endsWith(false)"),
        ("foo.trim().startsWith(null)", "foo.trimStart().startsWith(null)"),
        ("foo.trim().endsWith(1n)", "foo.trimEnd().endsWith(1n)"),
        (r#"(foo).trim().startsWith("-")"#, r#"(foo).trimStart().startsWith("-")"#),
        (r#"(foo.trim()).startsWith("-")"#, r#"(foo.trimStart()).startsWith("-")"#),
        (
            r#"if (foo.trim().startsWith("-")) {
                bar();
            }"#,
            r#"if (foo.trimStart().startsWith("-")) {
                bar();
            }"#,
        ),
        (
            r#"foo
                // comment
                .trim/* comment */()
                .startsWith("-")"#,
            r#"foo
                // comment
                .trimStart/* comment */()
                .startsWith("-")"#,
        ),
        (
            r#"function foo(value: string) { value.trim().endsWith("-"); }"#,
            r#"function foo(value: string) { value.trimEnd().endsWith("-"); }"#,
        ),
        (
            r#"function foo(value: string) { value.trim().startsWith("-" as const); }"#,
            r#"function foo(value: string) { value.trimStart().startsWith("-" as const); }"#,
        ),
        (
            r#"function foo(value: string) { value.trim().endsWith("-" satisfies string); }"#,
            r#"function foo(value: string) { value.trimEnd().endsWith("-" satisfies string); }"#,
        ),
        (
            r#"type Text = string; function foo(value: Text) { value.trim().startsWith("-"); }"#,
            r#"type Text = string; function foo(value: Text) { value.trimStart().startsWith("-"); }"#,
        ),
        (
            r#"type A = A; function foo(value: A) { value.trim().startsWith("-"); }"#,
            r#"type A = A; function foo(value: A) { value.trimStart().startsWith("-"); }"#,
        ),
        (
            r#"function foo(value: string | number) { value.trim().startsWith("-"); }"#,
            r#"function foo(value: string | number) { value.trimStart().startsWith("-"); }"#,
        ),
        ("foo.trim().startsWith(-1)", "foo.trimStart().startsWith(-1)"),
        (
            r#"function foo(a: string, b: number) { (c ? a : b).trim().startsWith("-"); }"#,
            r#"function foo(a: string, b: number) { (c ? a : b).trimStart().startsWith("-"); }"#,
        ),
        (
            r#"type A0 = number; type A1 = A0 | A0; type A2 = A1 | A1; type A3 = A2 | A2; type A4 = A3 | A3; type A5 = A4 | A4; type A6 = A5 | A5; type A7 = A6 | A6; type A8 = A7 | A7; function foo(value: A8) { value.trim().startsWith("-"); }"#,
            r#"type A0 = number; type A1 = A0 | A0; type A2 = A1 | A1; type A3 = A2 | A2; type A4 = A3 | A3; type A5 = A4 | A4; type A6 = A5 | A5; type A7 = A6 | A6; type A8 = A7 | A7; function foo(value: A8) { value.trimStart().startsWith("-"); }"#,
        ),
    ];

    Tester::new(NoUnnecessaryStringTrim::NAME, NoUnnecessaryStringTrim::PLUGIN, pass, fail)
        .change_rule_path_extension("ts")
        .expect_fix(fix)
        .test_and_snapshot();
}
