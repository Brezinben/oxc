use std::borrow::Cow;

use oxc_ast::{
    AstKind,
    ast::{ArrayExpressionElement, Expression, IdentifierReference, MemberExpression},
};
use oxc_ast_visit::Visit;
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_semantic::SymbolId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};

use crate::{
    AstNode, ast_util::get_symbol_id_of_variable, context::LintContext, rule::Rule,
    utils::pad_fix_with_token_boundary,
};

const MAXIMUM_ARRAY_LENGTH: f64 = 4_294_967_295.0;

/// A symbol hop budget, shared by both walks of one length. The cycle guard alone does not
/// bound the work: a crafted chain like `const a1 = a0 + a0; const a2 = a1 + a1;` doubles it at
/// each step.
const MAX_RESOLVE_STEPS: u32 = 64;

fn prefer_array_from_range_diagnostic(span: Span) -> OxcDiagnostic {
    OxcDiagnostic::warn("Prefer `Array.from({length}, …)` when creating range arrays.")
        .with_help("Use `Array.from({length: …}, (_, index) => index)` instead.")
        .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct PreferArrayFromRange;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Prefers `Array.from({length}, (_, index) => index)` over materializing
    /// `Array(length).keys()` or `new Array(length).keys()` into an array.
    ///
    /// The rule only reports an array literal whose only element is a spread, or a call to
    /// `Array.from()` with one argument. Lazy iterator use, `values()`, `entries()`, computed
    /// members, optional calls, shadowed `Array` bindings and invalid static lengths such as
    /// `Array(-1)` are ignored.
    ///
    /// ### Why is this bad?
    ///
    /// `[...Array(length).keys()]` creates a sparse array and an iterator only to copy the
    /// iterator into a second array. `Array.from({length}, (_, index) => index)` states the
    /// intent directly.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```js
    /// const indexes = [...Array(length).keys()];
    /// const offsets = Array.from(Array(count + 1).keys());
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```js
    /// const indexes = Array.from({length}, (_, index) => index);
    /// const offsets = Array.from({length: count + 1}, (_, index) => index);
    ///
    /// for (const index of Array(length).keys()) {
    ///   console.log(index);
    /// }
    /// ```
    PreferArrayFromRange,
    unicorn,
    style,
    conditional_fix,
    version = "next",
    short_description = "Prefer `Array.from({length}, …)` when creating range arrays.",
);

impl Rule for PreferArrayFromRange {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let (span, range) = match node.kind() {
            AstKind::ArrayExpression(array_expr) => {
                let [ArrayExpressionElement::SpreadElement(spread)] =
                    array_expr.elements.as_slice()
                else {
                    return;
                };
                (array_expr.span, &spread.argument)
            }
            AstKind::CallExpression(call_expr) => {
                let [argument] = call_expr.arguments.as_slice() else {
                    return;
                };
                let Some(argument) = argument.as_expression() else {
                    return;
                };
                let Expression::StaticMemberExpression(member) =
                    call_expr.callee.without_parentheses()
                else {
                    return;
                };
                if call_expr.optional
                    || member.optional
                    || member.property.name != "from"
                    || !is_global_array(&member.object, ctx)
                {
                    return;
                }
                (call_expr.span, argument)
            }
            _ => return,
        };

        let Some(length) = array_range_length(range, ctx) else {
            return;
        };

        let diagnostic = prefer_array_from_range_diagnostic(span);
        let length_span = length.span();
        // The fix keeps the source of the length only, so any other comment would be lost.
        if ctx
            .comments_range(span.start..span.end)
            .any(|comment| !length_span.contains_inclusive(comment.span))
        {
            ctx.diagnostic(diagnostic);
            return;
        }

        ctx.diagnostic_with_fix(diagnostic, |fixer| {
            let property = if matches!(
                length.without_parentheses(),
                Expression::Identifier(ident) if ident.name == "length"
            ) {
                Cow::Borrowed("length")
            } else {
                Cow::Owned(format!("length: {}", ctx.source_range(length_span)))
            };
            let mut replacement = format!("Array.from({{{property}}}, (_, index) => index)");
            pad_fix_with_token_boundary(ctx.source_text(), span, &mut replacement);
            fixer.replace(span, replacement)
        });
    }
}

/// The length argument of `Array(length).keys()` or `new Array(length).keys()`.
fn array_range_length<'a, 'b>(
    expr: &'b Expression<'a>,
    ctx: &LintContext<'a>,
) -> Option<&'b Expression<'a>> {
    let Expression::CallExpression(keys_call) = expr.get_inner_expression() else {
        return None;
    };
    let Expression::StaticMemberExpression(member) = keys_call.callee.without_parentheses() else {
        return None;
    };
    if keys_call.optional
        || !keys_call.arguments.is_empty()
        || member.optional
        || member.property.name != "keys"
    {
        return None;
    }

    let (callee, arguments) = match member.object.get_inner_expression() {
        Expression::CallExpression(call_expr) if !call_expr.optional => {
            (&call_expr.callee, &call_expr.arguments)
        }
        Expression::NewExpression(new_expr) => (&new_expr.callee, &new_expr.arguments),
        _ => return None,
    };
    let [length] = arguments.as_slice() else {
        return None;
    };
    let length = length.as_expression()?;
    if !is_global_array(callee, ctx) || has_invalid_static_length(length, ctx) {
        return None;
    }
    Some(length)
}

fn is_global_array(expr: &Expression, ctx: &LintContext) -> bool {
    matches!(
        expr.without_parentheses(),
        Expression::Identifier(ident)
            if ident.name == "Array" && ctx.is_reference_to_global_variable(ident)
    )
}

/// Whether `Array.from({length})` could behave differently from `Array(length)`, because
/// `length` is not a valid array length or reads a member. A getter can hide the real value
/// of a member, as in `Object.defineProperty(object, 'value', {get() { … }})`.
fn has_invalid_static_length<'a>(length: &Expression<'a>, ctx: &LintContext<'a>) -> bool {
    let mut walk = BindingWalk { visited: Vec::new(), steps_left: MAX_RESOLVE_STEPS };
    match static_value(length, ctx, &mut walk) {
        Some(StaticValue::Number(value)) => {
            !((0.0..=MAXIMUM_ARRAY_LENGTH).contains(&value) && value.fract() == 0.0)
        }
        Some(StaticValue::Other) => true,
        None => {
            let mut finder = MemberReadFinder { ctx, walk, found: false };
            finder.visit_expression(length);
            finder.found
        }
    }
}

/// A value known without running the code. `Other` is any value that is never a valid array
/// length, or a static value that this rule does not model.
enum StaticValue {
    Number(f64),
    Other,
}

fn static_value<'a>(
    expr: &Expression<'a>,
    ctx: &LintContext<'a>,
    walk: &mut BindingWalk,
) -> Option<StaticValue> {
    match expr.get_inner_expression() {
        Expression::NumericLiteral(literal) => Some(StaticValue::Number(literal.value)),
        Expression::StringLiteral(_)
        | Expression::TemplateLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => Some(StaticValue::Other),
        Expression::Identifier(ident) if ctx.is_reference_to_global_variable(ident) => {
            match ident.name.as_str() {
                "undefined" => Some(StaticValue::Other),
                "NaN" => Some(StaticValue::Number(f64::NAN)),
                "Infinity" => Some(StaticValue::Number(f64::INFINITY)),
                _ => None,
            }
        }
        Expression::Identifier(ident) => {
            let (symbol_id, init) = constant_initializer(ident, ctx)?;
            if walk.steps_left == 0 {
                return Some(StaticValue::Other);
            }
            if walk.visited.contains(&symbol_id) {
                return None;
            }
            walk.steps_left -= 1;
            walk.visited.push(symbol_id);
            let value = static_value(init, ctx, walk);
            walk.visited.pop();
            value
        }
        Expression::UnaryExpression(unary) => {
            // These operators never produce a number, whatever the argument is.
            if matches!(
                unary.operator,
                UnaryOperator::Void
                    | UnaryOperator::Typeof
                    | UnaryOperator::LogicalNot
                    | UnaryOperator::Delete
            ) {
                return Some(StaticValue::Other);
            }
            match (unary.operator, static_value(&unary.argument, ctx, walk)?) {
                (UnaryOperator::UnaryNegation, StaticValue::Number(value)) => {
                    Some(StaticValue::Number(-value))
                }
                (UnaryOperator::UnaryPlus, StaticValue::Number(value)) => {
                    Some(StaticValue::Number(value))
                }
                _ => Some(StaticValue::Other),
            }
        }
        Expression::BinaryExpression(binary) => {
            let operator = binary.operator;
            if operator.is_equality() || operator.is_compare() || operator.is_relational() {
                return Some(StaticValue::Other);
            }
            let left = static_value(&binary.left, ctx, walk)?;
            let right = static_value(&binary.right, ctx, walk)?;
            let (StaticValue::Number(left), StaticValue::Number(right)) = (left, right) else {
                return Some(StaticValue::Other);
            };
            #[expect(clippy::float_cmp, reason = "`1` and `-1` are exact in `f64`")]
            let value = match operator {
                BinaryOperator::Addition => left + right,
                BinaryOperator::Subtraction => left - right,
                BinaryOperator::Multiplication => left * right,
                BinaryOperator::Division => left / right,
                BinaryOperator::Remainder => left % right,
                // Unlike `f64::powf`, JavaScript gives `NaN` for `1 ** NaN` and `1 ** Infinity`.
                BinaryOperator::Exponential
                    if right.is_nan() || (left.abs() == 1.0 && right.is_infinite()) =>
                {
                    f64::NAN
                }
                BinaryOperator::Exponential => left.powf(right),
                _ => return Some(StaticValue::Other),
            };
            Some(StaticValue::Number(value))
        }
        _ => None,
    }
}

/// The initializer of a variable that is never reassigned.
fn constant_initializer<'a>(
    ident: &IdentifierReference<'a>,
    ctx: &LintContext<'a>,
) -> Option<(SymbolId, &'a Expression<'a>)> {
    let symbol_id = get_symbol_id_of_variable(ident, ctx)?;
    let scoping = ctx.scoping();
    // `var x = 1; var x = -1;` redeclares without a mutation.
    if scoping.symbol_is_mutated(symbol_id) || !scoping.symbol_redeclarations(symbol_id).is_empty()
    {
        return None;
    }
    let declaration = ctx.nodes().get_node(scoping.symbol_declaration(symbol_id));
    let AstKind::VariableDeclarator(declarator) = declaration.kind() else {
        return None;
    };
    // `const {value} = object` binds a property, not the initializer.
    if !declarator.id.is_binding_identifier() {
        return None;
    }
    Some((symbol_id, declarator.init.as_ref()?))
}

struct BindingWalk {
    visited: Vec<SymbolId>,
    steps_left: u32,
}

/// Finds a member read in the length expression. Follows bindings that are never reassigned.
struct MemberReadFinder<'c, 'a> {
    ctx: &'c LintContext<'a>,
    walk: BindingWalk,
    found: bool,
}

impl<'a> Visit<'a> for MemberReadFinder<'_, 'a> {
    fn visit_member_expression(&mut self, _member: &MemberExpression<'a>) {
        self.found = true;
    }

    fn visit_identifier_reference(&mut self, ident: &IdentifierReference<'a>) {
        let Some((symbol_id, init)) = constant_initializer(ident, self.ctx) else {
            return;
        };
        if self.walk.steps_left == 0 || self.walk.visited.contains(&symbol_id) {
            self.found = true;
            return;
        }
        self.walk.steps_left -= 1;
        self.walk.visited.push(symbol_id);
        self.visit_expression(init);
        self.walk.visited.pop();
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        "Array.from({length}, (_, index) => index);",
        "Array.from({length: count}, (_, index) => index);",
        "Array.from(Array(length).values());",
        "Array.from(Array(length).entries());",
        "Array.from(Array(length).keys(), index => index);",
        "Array.from(Array(length).keys(), mapFunction);",
        "Array.from(...Array(length).keys());",
        "Array.from?.(Array(length).keys());",
        "Array?.from(Array(length).keys());",
        "NotArray.from(Array(length).keys());",
        "Array.from(array.keys());",
        "Array.from(new Set([1, 2]).keys());",
        "[...Array(length).values()];",
        "[...Array(length).entries()];",
        "[...Array(length).keys(), other];",
        "[other, ...Array(length).keys()];",
        "[...Array[length].keys()];",
        "[...Array(length)['keys']()];",
        "Array['from'](Array(length).keys());",
        "Array.from(Array(length)['keys']());",
        "[...Array(length).keys?.()];",
        "[...Array(length)?.keys()];",
        "[...Array?.(length).keys()];",
        "[...Array(...length).keys()];",
        "[...Array(length, other).keys()];",
        "[...NotArray(length).keys()];",
        "[...new Array(length, other).keys()];",
        "[...new Array(...length).keys()];",
        r#"[...Array("3").keys()];"#,
        r#"[...new Array("3").keys()];"#,
        r#"Array.from(Array("3").keys());"#,
        "[...Array(undefined).keys()];",
        "Array.from(new Array(undefined).keys());",
        "[...Array(null).keys()];",
        "[...Array(true).keys()];",
        "[...Array(1n).keys()];",
        "[...Array(3.5).keys()];",
        "Array.from(Array(3.5).keys());",
        "[...Array(-1).keys()];",
        "[...Array(({value: -1}).value).keys()];",
        "[...Array(2 ** 32).keys()];",
        r#"const length = "3"; [...Array(length).keys()];"#,
        "const length = -1; Array.from(new Array(length).keys());",
        "const object = {value: 3};
            Object.defineProperty(object, 'value', {get() { return -1; }});
            [...Array(object.value).keys()];",
        "for (const index of Array(length).keys()) {}",
        "const Array = value; [...Array(length).keys()];",
        "function foo(Array) { return [...Array(length).keys()]; }",
        "const Array = value; Array.from(Array(length).keys());",
        "function foo(Array) { return Array.from(Array(length).keys()); }",
        "[...NotArray<number>(length).keys()];",
        "[...Array(~0).keys()];",
        r#"[...Array("a" + "b").keys()];"#,
        r#"Array.from(Array(1 + "2").keys());"#,
        "[...Array(void length).keys()];",
        "[...Array(`${3}`).keys()];",
        "[...Array(`3`).keys()];",
        r#"[...Array(-"3").keys()];"#,
        "[...Array(NaN).keys()];",
        "[...Array(1 - 2).keys()];",
        "const length = length; [...Array(length).keys()];",
        "let length = -1; [...Array(length).keys()];",
        r#"let length = "3"; [...Array(length).keys()];"#,
        "const a0 = 1; const a1 = a0 + a0; const a2 = a1 + a1; const a3 = a2 + a2;
            const a4 = a3 + a3; const a5 = a4 + a4; const a6 = a5 + a5; const a7 = a6 + a6;
            const a8 = a7 + a7; [...Array(a8).keys()];",
        "[...Array(1 ** Infinity).keys()];",
        "[...Array(Infinity).keys()];",
        "[...Array(typeof x).keys()];",
        "[...Array(!x).keys()];",
        "[...Array(a === b).keys()];",
        "const a = [1, 2]; [...Array(a.length).keys()];",
    ];

    let fail = vec![
        "[...Array(length).keys()];",
        "[...new Array(length).keys()];",
        "Array.from(Array(length).keys());",
        "Array.from(new Array(length).keys());",
        "Array.from(Array(length).keys(),);",
        "[...Array(count + 1).keys()];",
        "Array.from(Array(count + 1).keys());",
        "[...Array((count + 1)).keys()];",
        "[...Array((count, fallback)).keys()];",
        "Array.from((Array(length).keys()));",
        "[...(Array(length).keys())];",
        "[
                ...Array(
                    length
                ).keys()
            ];",
        "Array.from(
                Array(
                    length
                ).keys()
            );",
        "[...Array(/* keep */ length).keys()];",
        "[.../* keep */Array(length).keys()];",
        "[...Array(length)/* keep */.keys()];",
        "[...Array(length).keys(/* keep */)];",
        "Array.from(/* keep */ Array(length).keys());",
        "[...Array<number>(length).keys()];",
        "[...new Array<number>(length).keys()];",
        "[...Array(length as number).keys()];",
        "[...(Array(length) as number[]).keys()];",
        "[...(new Array(length) as number[]).keys()];",
        "[...(Array(length)!).keys()];",
        "[...(Array(length) satisfies number[]).keys()];",
        "Array.from((Array(length) as number[]).keys());",
        "[...(Array(length).keys() as Iterable<number>)];",
        "[...(Array(length).keys()!)];",
        "[...(<Iterable<number>>Array(length).keys())];",
        "Array.from(Array(length).keys() as Iterable<number>);",
        "function foo() { return[...Array(length).keys()]; }",
        "let length = 3; length = n; [...Array(length).keys()];",
        "var length = 1; var length = -1; [...Array(length).keys()];",
        "[...Array(2 * 3).keys()];",
    ];

    let fix = vec![
        (
            "let length = 3; length = n; [...Array(length).keys()];",
            "let length = 3; length = n; Array.from({length}, (_, index) => index);",
        ),
        (
            "var length = 1; var length = -1; [...Array(length).keys()];",
            "var length = 1; var length = -1; Array.from({length}, (_, index) => index);",
        ),
        ("[...Array(2 * 3).keys()];", "Array.from({length: 2 * 3}, (_, index) => index);"),
        ("[...Array(length).keys()];", "Array.from({length}, (_, index) => index);"),
        ("[...new Array(length).keys()];", "Array.from({length}, (_, index) => index);"),
        ("Array.from(Array(length).keys());", "Array.from({length}, (_, index) => index);"),
        ("Array.from(new Array(length).keys());", "Array.from({length}, (_, index) => index);"),
        ("Array.from(Array(length).keys(),);", "Array.from({length}, (_, index) => index);"),
        ("[...Array(count + 1).keys()];", "Array.from({length: count + 1}, (_, index) => index);"),
        (
            "Array.from(Array(count + 1).keys());",
            "Array.from({length: count + 1}, (_, index) => index);",
        ),
        (
            "[...Array((count + 1)).keys()];",
            "Array.from({length: (count + 1)}, (_, index) => index);",
        ),
        (
            "[...Array((count, fallback)).keys()];",
            "Array.from({length: (count, fallback)}, (_, index) => index);",
        ),
        ("Array.from((Array(length).keys()));", "Array.from({length}, (_, index) => index);"),
        ("[...(Array(length).keys())];", "Array.from({length}, (_, index) => index);"),
        (
            "[
                ...Array(
                    length
                ).keys()
            ];",
            "Array.from({length}, (_, index) => index);",
        ),
        (
            "Array.from(
                Array(
                    length
                ).keys()
            );",
            "Array.from({length}, (_, index) => index);",
        ),
        ("[...Array<number>(length).keys()];", "Array.from({length}, (_, index) => index);"),
        ("[...new Array<number>(length).keys()];", "Array.from({length}, (_, index) => index);"),
        (
            "[...Array(length as number).keys()];",
            "Array.from({length: length as number}, (_, index) => index);",
        ),
        ("[...(Array(length) as number[]).keys()];", "Array.from({length}, (_, index) => index);"),
        (
            "[...(new Array(length) as number[]).keys()];",
            "Array.from({length}, (_, index) => index);",
        ),
        ("[...(Array(length)!).keys()];", "Array.from({length}, (_, index) => index);"),
        (
            "[...(Array(length) satisfies number[]).keys()];",
            "Array.from({length}, (_, index) => index);",
        ),
        (
            "Array.from((Array(length) as number[]).keys());",
            "Array.from({length}, (_, index) => index);",
        ),
        (
            "[...(Array(length).keys() as Iterable<number>)];",
            "Array.from({length}, (_, index) => index);",
        ),
        ("[...(Array(length).keys()!)];", "Array.from({length}, (_, index) => index);"),
        (
            "[...(<Iterable<number>>Array(length).keys())];",
            "Array.from({length}, (_, index) => index);",
        ),
        (
            "Array.from(Array(length).keys() as Iterable<number>);",
            "Array.from({length}, (_, index) => index);",
        ),
        (
            "function foo() { return[...Array(length).keys()]; }",
            "function foo() { return Array.from({length}, (_, index) => index); }",
        ),
        ("[...Array(/* keep */ length).keys()];", "[...Array(/* keep */ length).keys()];"),
        ("[.../* keep */Array(length).keys()];", "[.../* keep */Array(length).keys()];"),
        ("[...Array(length)/* keep */.keys()];", "[...Array(length)/* keep */.keys()];"),
        ("[...Array(length).keys(/* keep */)];", "[...Array(length).keys(/* keep */)];"),
        (
            "Array.from(/* keep */ Array(length).keys());",
            "Array.from(/* keep */ Array(length).keys());",
        ),
    ];

    Tester::new(PreferArrayFromRange::NAME, PreferArrayFromRange::PLUGIN, pass, fail)
        .expect_fix(fix)
        .change_rule_path_extension("ts")
        .test_and_snapshot();
}
