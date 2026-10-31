use oxc_ast::{
    AstKind,
    ast::{
        CallExpression, Class, Expression, IdentifierReference, TSType, TSTypeAnnotation,
        TSTypeName, TSTypeOperatorOperator,
    },
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_semantic::{NodeId, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::UnaryOperator;

use crate::{
    AstNode,
    ast_util::{get_symbol_id_of_variable, outermost_paren_parent},
    context::LintContext,
    rule::Rule,
};

fn prefer_array_slice_diagnostic(span: Span) -> OxcDiagnostic {
    OxcDiagnostic::warn(
        "Prefer `Array#slice()` over `Array#splice()` when reading from the returned array.",
    )
    .with_help(
        "`Array#splice()` removes the elements from the source array. Use `Array#slice()` to read the elements without changing the source array.",
    )
    .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct PreferArraySlice;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Prefers `Array#slice()` over `Array#splice()` when the code only reads from the
    /// returned array, with an index access or with `.at()`.
    ///
    /// ### Why is this bad?
    ///
    /// `Array#splice()` mutates the source array. When the code immediately indexes the returned
    /// elements or reads them with `.at()`, `Array#slice()` expresses the read-only intent without
    /// changing the source array.
    ///
    /// Keep `Array#splice()` when the mutation is part of the operation.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```js
    /// const foo = process.argv.splice(2)[0];
    /// const bar = array.splice(index).at(0);
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```js
    /// const foo = process.argv.slice(2)[0];
    /// const bar = array.slice(index).at(0);
    /// array.splice(index);
    /// array.splice(index, deleteCount)[0];
    /// ```
    PreferArraySlice,
    unicorn,
    suspicious,
    suggestion,
    version = "next",
    short_description = "Prefer `Array#slice()` over `Array#splice()` when reading from the returned array.",
);

impl Rule for PreferArraySlice {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let AstKind::CallExpression(call_expr) = node.kind() else {
            return;
        };
        let Expression::StaticMemberExpression(callee) = call_expr.callee.without_parentheses()
        else {
            return;
        };
        if callee.property.name.as_str() != "splice"
            || callee.optional
            || !is_single_argument_call(call_expr)
            || !is_read_of_returned_array(node, ctx)
        {
            return;
        }
        if (TypeResolver { ctx, visited: Vec::new(), steps: MAX_RESOLVE_STEPS })
            .expression_kind(&callee.object)
            == NotArray
        {
            return;
        }

        let span = callee.property.span;
        ctx.diagnostic_with_suggestion(prefer_array_slice_diagnostic(span), |fixer| {
            fixer.replace(span, "slice").with_message("Use `Array#slice()`.")
        });
    }
}

fn is_single_argument_call(call_expr: &CallExpression) -> bool {
    !call_expr.optional
        && matches!(call_expr.arguments.as_slice(), [argument] if !argument.is_spread())
}

fn is_read_of_returned_array<'a>(node: &AstNode<'a>, ctx: &LintContext<'a>) -> bool {
    let call_span = node.kind().span();
    let Some(parent) = outermost_paren_parent(node, ctx) else {
        return false;
    };
    match parent.kind() {
        AstKind::ComputedMemberExpression(member) => {
            !member.optional
                && member.object.without_parentheses().span() == call_span
                && !is_left_hand_side(parent, ctx)
        }
        AstKind::StaticMemberExpression(member) => {
            member.property.name.as_str() == "at"
                && !member.optional
                && matches!(
                    ctx.nodes().parent_kind(parent.id()),
                    AstKind::CallExpression(at_call)
                        if at_call.callee.span() == member.span && is_single_argument_call(at_call)
                )
        }
        _ => false,
    }
}

fn is_left_hand_side<'a>(node: &AstNode<'a>, ctx: &LintContext<'a>) -> bool {
    let span = node.kind().span();
    let Some(parent) = outermost_paren_parent(node, ctx) else {
        return false;
    };
    match parent.kind() {
        AstKind::AssignmentExpression(assignment) => assignment.left.span() == span,
        AstKind::AssignmentTargetWithDefault(target) => target.binding.span() == span,
        AstKind::AssignmentTargetPropertyProperty(property) => property.binding.span() == span,
        AstKind::UnaryExpression(unary) => unary.operator == UnaryOperator::Delete,
        AstKind::UpdateExpression(_)
        | AstKind::ArrayAssignmentTarget(_)
        | AstKind::AssignmentTargetRest(_) => true,
        _ => false,
    }
}

/// What the syntax tells about a receiver. Upstream normalizes its nullish state to non-target,
/// so the `null` and `undefined` types count as `NotArray`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReceiverKind {
    Array,
    NotArray,
    Unknown,
}

use ReceiverKind::{Array, NotArray, Unknown};

/// A mixed union counts as `NotArray`, because a `splice()` on it can be a custom method.
fn union(kinds: impl IntoIterator<Item = ReceiverKind>) -> ReceiverKind {
    let mut result = Array;
    for kind in kinds {
        match kind {
            NotArray => return NotArray,
            Unknown => result = Unknown,
            Array => {}
        }
    }
    result
}

fn intersection(kinds: impl IntoIterator<Item = ReceiverKind>) -> ReceiverKind {
    let mut result = NotArray;
    for kind in kinds {
        match kind {
            Array => return Array,
            Unknown => result = Unknown,
            NotArray => {}
        }
    }
    result
}

fn known_type_name_kind(name: &str) -> ReceiverKind {
    match name {
        "Array" | "ReadonlyArray" => Array,
        "Int8Array"
        | "Uint8Array"
        | "Uint8ClampedArray"
        | "Int16Array"
        | "Uint16Array"
        | "Int32Array"
        | "Uint32Array"
        | "Float16Array"
        | "Float32Array"
        | "Float64Array"
        | "BigInt64Array"
        | "BigUint64Array"
        | "Map"
        | "ReadonlyMap"
        | "WeakMap"
        | "Set"
        | "ReadonlySet"
        | "WeakSet"
        | "CanvasRenderingContext2D"
        | "OffscreenCanvasRenderingContext2D" => NotArray,
        _ => Unknown,
    }
}

/// A symbol hop budget for one receiver. The cycle guard alone does not bound the work: a
/// crafted chain like `type A1 = A0 | A0; type A2 = A1 | A1; ...` doubles it at each step.
const MAX_RESOLVE_STEPS: u32 = 64;

/// Port of the syntactic part of upstream `isKnownNonArray`, with the options
/// `checkClassHeritage`, `checkClassSyntax` and `treatMixedUnionAsNonTarget`.
struct TypeResolver<'a, 'c> {
    ctx: &'c LintContext<'a>,
    /// Symbols in resolution, to stop on cycles such as `type A = A` or `const a = a`.
    visited: Vec<SymbolId>,
    steps: u32,
}

impl<'a> TypeResolver<'a, '_> {
    fn visit(
        &mut self,
        symbol_id: SymbolId,
        resolve: impl FnOnce(&mut Self, AstKind<'a>) -> ReceiverKind,
    ) -> ReceiverKind {
        if self.steps == 0 || self.visited.contains(&symbol_id) {
            return Unknown;
        }
        self.steps -= 1;
        self.visited.push(symbol_id);
        let declaration = self.ctx.nodes().kind(self.ctx.scoping().symbol_declaration(symbol_id));
        let kind = resolve(self, declaration);
        self.visited.pop();
        kind
    }

    fn expression_kind(&mut self, expr: &Expression<'a>) -> ReceiverKind {
        match expr {
            Expression::ParenthesizedExpression(expr) => self.expression_kind(&expr.expression),
            Expression::TSSatisfiesExpression(expr) => self.expression_kind(&expr.expression),
            Expression::TSNonNullExpression(expr) => self.expression_kind(&expr.expression),
            Expression::TSAsExpression(expr) => {
                self.asserted_kind(&expr.type_annotation, &expr.expression)
            }
            Expression::TSTypeAssertion(expr) => {
                self.asserted_kind(&expr.type_annotation, &expr.expression)
            }
            Expression::SequenceExpression(expr) => {
                expr.expressions.last().map_or(Unknown, |expr| self.expression_kind(expr))
            }
            Expression::ConditionalExpression(expr) => {
                let consequent = self.expression_kind(&expr.consequent);
                union([consequent, self.expression_kind(&expr.alternate)])
            }
            Expression::Identifier(ident) => self.variable_kind(ident),
            Expression::CallExpression(call_expr) => self.return_kind(call_expr),
            Expression::NewExpression(new_expr) => {
                match self.class_reference_kind(&new_expr.callee) {
                    Array => Array,
                    Unknown
                        if matches!(
                            &new_expr.callee,
                            Expression::Identifier(ident) if ident.name.as_str() == "Array"
                        ) =>
                    {
                        Array
                    }
                    _ => NotArray,
                }
            }
            Expression::ThisExpression(this) => self.this_kind(this.node_id()),
            Expression::Super(sup) => self.super_kind(sup.node_id()),
            Expression::ObjectExpression(_)
            | Expression::FunctionExpression(_)
            | Expression::ArrowFunctionExpression(_)
            | Expression::ClassExpression(_)
            | Expression::TemplateLiteral(_) => NotArray,
            // Upstream also treats other static values, such as `1 + 2`, as non-arrays.
            // Only literals occur as receivers in practice.
            _ if expr.is_literal() => NotArray,
            _ => Unknown,
        }
    }

    fn asserted_kind(&mut self, ts_type: &TSType<'a>, expr: &Expression<'a>) -> ReceiverKind {
        match self.type_kind(ts_type) {
            Unknown => self.expression_kind(expr),
            kind => kind,
        }
    }

    fn variable_kind(&mut self, ident: &IdentifierReference) -> ReceiverKind {
        let Some(symbol_id) = get_symbol_id_of_variable(ident, self.ctx) else {
            return Unknown;
        };
        let scoping = self.ctx.scoping();
        if !scoping.symbol_redeclarations(symbol_id).is_empty() {
            return Unknown;
        }
        let is_const = scoping.symbol_flags(symbol_id).is_const_variable();
        self.visit(symbol_id, |this, declaration| match declaration {
            AstKind::VariableDeclarator(declarator) if declarator.id.is_binding_identifier() => {
                match this.annotation_kind(declarator.type_annotation.as_deref()) {
                    Unknown if is_const => {
                        declarator.init.as_ref().map_or(Unknown, |init| this.expression_kind(init))
                    }
                    kind => kind,
                }
            }
            AstKind::FormalParameter(param) if param.pattern.is_binding_identifier() => {
                // An optional parameter can be `undefined`.
                if param.optional {
                    NotArray
                } else {
                    this.annotation_kind(param.type_annotation.as_deref())
                }
            }
            _ => Unknown,
        })
    }

    fn return_kind(&mut self, call_expr: &CallExpression<'a>) -> ReceiverKind {
        let Expression::Identifier(callee) = call_expr.callee.without_parentheses() else {
            return Unknown;
        };
        let Some(symbol_id) = get_symbol_id_of_variable(callee, self.ctx) else {
            return Unknown;
        };
        let ctx = self.ctx;
        let scoping = ctx.scoping();
        if !scoping.symbol_redeclarations(symbol_id).is_empty()
            || scoping.symbol_is_mutated(symbol_id)
        {
            return Unknown;
        }
        let (type_parameters, return_type) =
            match ctx.nodes().kind(scoping.symbol_declaration(symbol_id)) {
                AstKind::Function(function) => (&function.type_parameters, &function.return_type),
                AstKind::VariableDeclarator(declarator)
                    if scoping.symbol_flags(symbol_id).is_const_variable()
                        && declarator.id.is_binding_identifier() =>
                {
                    match declarator.init.as_ref().map(skip_satisfies_and_non_null) {
                        Some(Expression::FunctionExpression(function)) => {
                            (&function.type_parameters, &function.return_type)
                        }
                        Some(Expression::ArrowFunctionExpression(function)) => {
                            (&function.type_parameters, &function.return_type)
                        }
                        _ => return Unknown,
                    }
                }
                _ => return Unknown,
            };
        if type_parameters.is_some() {
            return Unknown;
        }
        self.annotation_kind(return_type.as_deref())
    }

    fn this_kind(&mut self, node_id: NodeId) -> ReceiverKind {
        let ctx = self.ctx;
        let nodes = ctx.nodes();
        for ancestor in nodes.ancestors(node_id) {
            match ancestor.kind() {
                AstKind::Class(class) => return self.class_kind(class),
                kind if is_static_context(kind) => return NotArray,
                AstKind::Function(function) => {
                    let this_param_kind = self.annotation_kind(
                        function
                            .this_param
                            .as_ref()
                            .and_then(|param| param.type_annotation.as_deref()),
                    );
                    if this_param_kind != Unknown {
                        return this_param_kind;
                    }
                    match nodes.parent_kind(ancestor.id()) {
                        AstKind::ObjectProperty(_) => return NotArray,
                        AstKind::MethodDefinition(method) if method.r#static => return NotArray,
                        AstKind::MethodDefinition(_) => {}
                        _ => return Unknown,
                    }
                }
                _ => {}
            }
        }
        Unknown
    }

    fn super_kind(&mut self, node_id: NodeId) -> ReceiverKind {
        let ctx = self.ctx;
        for ancestor in ctx.nodes().ancestors(node_id) {
            match ancestor.kind() {
                kind if is_static_context(kind) => return NotArray,
                AstKind::MethodDefinition(method) if method.r#static => return NotArray,
                AstKind::Class(class) => return self.class_kind(class),
                _ => {}
            }
        }
        Unknown
    }

    fn class_kind(&mut self, class: &Class<'a>) -> ReceiverKind {
        class
            .heritage_expression()
            .map_or(NotArray, |super_class| self.class_reference_kind(super_class))
    }

    fn class_reference_kind(&mut self, expr: &Expression<'a>) -> ReceiverKind {
        match expr.without_parentheses() {
            Expression::Identifier(ident) => {
                let Some(symbol_id) = get_symbol_id_of_variable(ident, self.ctx) else {
                    return known_type_name_kind(ident.name.as_str());
                };
                let is_const = self.ctx.scoping().symbol_flags(symbol_id).is_const_variable();
                self.visit(symbol_id, |this, declaration| match declaration {
                    AstKind::VariableDeclarator(declarator)
                        if is_const && declarator.id.is_binding_identifier() =>
                    {
                        declarator
                            .init
                            .as_ref()
                            .map_or(Unknown, |init| this.class_reference_kind(init))
                    }
                    AstKind::Class(class) => this.class_kind(class),
                    _ => Unknown,
                })
            }
            Expression::ClassExpression(class) => self.class_kind(class),
            _ => Unknown,
        }
    }

    fn annotation_kind(&mut self, annotation: Option<&TSTypeAnnotation<'a>>) -> ReceiverKind {
        annotation.map_or(Unknown, |annotation| self.type_kind(&annotation.type_annotation))
    }

    fn type_kind(&mut self, ts_type: &TSType<'a>) -> ReceiverKind {
        match ts_type {
            TSType::TSParenthesizedType(ts_type) => self.type_kind(&ts_type.type_annotation),
            TSType::TSTypeOperatorType(ts_type)
                if ts_type.operator == TSTypeOperatorOperator::Readonly =>
            {
                self.type_kind(&ts_type.type_annotation)
            }
            TSType::TSTypeReference(reference) => self.type_reference_kind(&reference.type_name),
            TSType::TSUnionType(union_type) => {
                union(union_type.types.iter().map(|ts_type| self.type_kind(ts_type)))
            }
            TSType::TSIntersectionType(intersection_type) => {
                intersection(intersection_type.types.iter().map(|ts_type| self.type_kind(ts_type)))
            }
            TSType::TSArrayType(_) | TSType::TSTupleType(_) => Array,
            TSType::TSBigIntKeyword(_)
            | TSType::TSBooleanKeyword(_)
            | TSType::TSNeverKeyword(_)
            | TSType::TSNullKeyword(_)
            | TSType::TSNumberKeyword(_)
            | TSType::TSStringKeyword(_)
            | TSType::TSSymbolKeyword(_)
            | TSType::TSUndefinedKeyword(_)
            | TSType::TSVoidKeyword(_)
            | TSType::TSLiteralType(_)
            | TSType::TSTypeLiteral(_)
            | TSType::TSFunctionType(_)
            | TSType::TSConstructorType(_) => NotArray,
            _ => Unknown,
        }
    }

    fn type_reference_kind(&mut self, type_name: &TSTypeName<'a>) -> ReceiverKind {
        let TSTypeName::IdentifierReference(ident) = type_name else {
            return Unknown;
        };
        let Some(symbol_id) = get_symbol_id_of_variable(ident, self.ctx) else {
            return known_type_name_kind(ident.name.as_str());
        };
        self.visit(symbol_id, |this, declaration| match declaration {
            AstKind::TSTypeAliasDeclaration(alias) => this.type_kind(&alias.type_annotation),
            AstKind::TSTypeParameter(param) => {
                param.constraint.as_ref().map_or(Unknown, |constraint| this.type_kind(constraint))
            }
            AstKind::TSInterfaceDeclaration(interface) => intersection(
                interface
                    .extends
                    .iter()
                    .map(|heritage| this.type_reference_kind(&heritage.type_name)),
            ),
            AstKind::Class(class) => this.class_kind(class),
            // An imported type with the name of a built-in type is not the built-in type.
            AstKind::ImportSpecifier(specifier)
                if known_type_name_kind(specifier.imported.name().as_str()) != Unknown
                    || known_type_name_kind(specifier.local.name.as_str()) != Unknown =>
            {
                NotArray
            }
            AstKind::ImportDefaultSpecifier(specifier)
                if known_type_name_kind(specifier.local.name.as_str()) != Unknown =>
            {
                NotArray
            }
            _ => Unknown,
        })
    }
}

fn is_static_context(kind: AstKind<'_>) -> bool {
    match kind {
        AstKind::StaticBlock(_) => true,
        AstKind::PropertyDefinition(property) => property.r#static,
        AstKind::AccessorProperty(property) => property.r#static,
        _ => false,
    }
}

/// Upstream unwraps only these two wrappers around a function initializer.
fn skip_satisfies_and_non_null<'b, 'a>(mut expr: &'b Expression<'a>) -> &'b Expression<'a> {
    loop {
        expr = match expr.without_parentheses() {
            Expression::TSSatisfiesExpression(inner) => &inner.expression,
            Expression::TSNonNullExpression(inner) => &inner.expression,
            inner => return inner,
        };
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        "array.splice(index)",
        "array.splice(index, 1)[0]",
        "array.splice(index, deleteCount)[0]",
        "array.splice(index).shift()",
        "array.splice(index).length",
        "array.splice(index).at()",
        "array.splice(index).at(0, extra)",
        "array.splice(index)[0] = value",
        r#"array.splice(index)["length"] = value"#,
        "delete array.splice(index)[0]",
        r#"array["splice"](index)[0]"#,
        "array[splice](index)[0]",
        "array?.splice(index)[0]",
        "array.splice?.(index)[0]",
        "splice(index)[0]",
        "const object = {splice() { return []; }}; object.splice(index)[0]",
        "({splice() { return []; }}).splice(index)[0]",
        "const object = {splice() { return []; }, method() { return this.splice(0)[0]; }}",
        "class Custom { splice() { return []; } method() { return this.splice(0)[0]; } }",
        "class ArraySubclass extends Array { static method() { return this.splice(0)[0]; } }",
        "class Custom { splice() { return []; } } const Array = Custom; class ArraySubclass extends Array {} new ArraySubclass().splice(0)[0]",
        "class Custom { splice() { return []; } } let BaseArray = Array; BaseArray = Custom; class ArraySubclass extends BaseArray {} new ArraySubclass().splice(0)[0]",
        "array.splice(index, 1 as const)[0]",
        "(array as string[])?.splice(index)[0]",
        "declare const set: Set<string>; set.splice(index)[0]",
        "declare const string: string; string.splice(index)[0]",
        "interface Custom { splice(index: number): string[]; } declare const value: Custom; value.splice(index)[0]",
        "interface Custom { splice(index: number): string[]; } declare const value: string[] | Custom; value.splice(index)[0]",
        "interface Custom { splice(index: number): string[]; } declare const value: string[] | Custom; (value as string[] | Custom).splice(index)[0]",
        "interface Custom { splice(index: number): string[]; } function method(this: Custom) { return this.splice(0)[0]; }",
        "class Custom { splice(): string[] { return []; } } const Array = Custom; class ArraySubclass extends Array {} declare const array: ArraySubclass; array.splice(0)[0]",
        "class Custom { splice() { return [1]; } } function getValue(): Custom { return new Custom(); } const value = getValue(); value.splice(0)[0]",
        "interface Custom { splice(index: number): string[]; } function getValue(): string[] | Custom { return []; } const value = getValue(); value.splice(0)[0]",
        // Upstream reports this one only with type information.
        "declare const ArrayConstructor: typeof Array; new ArrayConstructor().splice(0)[0]",
        "[array.splice(0)[0]] = values",
        "[...array.splice(0)[0]] = values",
        "({a: array.splice(0)[0]} = object)",
        "[array.splice(0)[0] = 1] = values",
        "array.splice(0)[0]++",
        "array.splice(0)[0] += 1",
        "class Custom { splice() { return []; } } class Sub extends Custom { m() { return super.splice(0)[0]; } }",
        "class ArraySubclass extends Array { static { this.splice(0)[0]; } }",
        "const value = condition ? new Set() : []; value.splice(0)[0]",
        "function foo(value?: string[]) { value.splice(0)[0]; }",
        "function foo<T extends Set<string>>(value: T) { value.splice(0)[0]; }",
        "const getValue = (): Set<string> => new Set(); getValue().splice(0)[0]",
        r#"import type { Set } from "./set"; declare const value: Set; value.splice(0)[0]"#,
        "(0, new Set()).splice(0)[0]",
        "class ArraySubclass extends Array { static value = this.splice(0)[0]; }",
        "class ArraySubclass extends Array { static value = super.splice(0)[0]; }",
        r#"import Set from "x"; declare const v: Set; v.splice(0)[0]"#,
        "interface I extends Set<string> {} declare const v: I; v.splice(0)[0]",
        "const f = function (): Set<string> { return new Set(); }; f().splice(0)[0]",
    ];

    let fail = vec![
        "process.argv.splice(2)[0]",
        "array.splice(index)[0]",
        "array.splice(index)[offset]",
        "array.splice(index).at(0)",
        "object.array.splice(index)[0]",
        "array.splice(/* comment */ index)[0]",
        "const array = []; array.splice(index)[0]",
        "const BaseArray = Array; class ArraySubclass extends BaseArray {} new ArraySubclass().splice(0)[0]",
        "const ArraySubclass = class extends Array {}; new ArraySubclass().splice(0)[0]",
        "class ArraySubclass extends Array {} new ArraySubclass().splice(0)[0]",
        "class ArraySubclass extends Array {} const array = new ArraySubclass(); array.splice(0)[0]",
        "class ArraySubclass extends Array { method() { return this.splice(0)[0]; } }",
        "array.splice(index as number)[0]",
        "array.splice(<number>index)[0]",
        "array.splice(index!)[0]",
        "array.splice(index satisfies number)[0]",
        "(array as string[]).splice(index)[0]",
        "declare const array: string[]; array.splice(index)[0]",
        "type Strings = string[]; declare const array: Strings; array.splice(index)[0]",
        "declare const value: unknown; value.splice(index)[0]",
        "type Value = Value; declare const value: Value; value.splice(index)[0]",
        "const array = array; array.splice(index)[0]",
        "function method(this: string[]) { return this.splice(0)[0]; }",
        "class ArraySubclass extends Array<number> {} declare const array: ArraySubclass; array.splice(0)[0]",
        "const BaseArray = Array; class ArraySubclass extends BaseArray {} declare const array: ArraySubclass; array.splice(0)[0]",
        "class ArraySubclass extends Array<number> {} const array = new ArraySubclass(); array.splice(0)[0]",
        "function getArray(): string[] { return []; } const array = getArray(); array.splice(0)[0]",
        "for (array.splice(0)[0] of values);",
        "(x as any)!.splice(0)[0]",
        "(x satisfies unknown).splice(0)[0]",
        "declare const x: readonly string[]; x.splice(0)[0]",
        "declare const x: [string]; x.splice(0)[0]",
        "function f<T>(): Set<T> { return new Set(); } f().splice(0)[0]",
        "declare const a0: unknown; const a1 = c ? a0 : a0; const a2 = c ? a1 : a1; const a3 = c ? a2 : a2; const a4 = c ? a3 : a3; const a5 = c ? a4 : a4; const a6 = c ? a5 : a5; const a7 = c ? a6 : a6; const a8 = c ? a7 : a7; const set = new Set(); const value = c ? a8 : set; value.splice(0)[0]",
    ];

    let fix = vec![
        ("process.argv.splice(2)[0]", "process.argv.slice(2)[0]"),
        ("array.splice(index)[0]", "array.slice(index)[0]"),
        ("array.splice(index)[offset]", "array.slice(index)[offset]"),
        ("array.splice(index).at(0)", "array.slice(index).at(0)"),
        ("object.array.splice(index)[0]", "object.array.slice(index)[0]"),
        ("array.splice(/* comment */ index)[0]", "array.slice(/* comment */ index)[0]"),
        ("const array = []; array.splice(index)[0]", "const array = []; array.slice(index)[0]"),
        (
            "const BaseArray = Array; class ArraySubclass extends BaseArray {} new ArraySubclass().splice(0)[0]",
            "const BaseArray = Array; class ArraySubclass extends BaseArray {} new ArraySubclass().slice(0)[0]",
        ),
        (
            "const ArraySubclass = class extends Array {}; new ArraySubclass().splice(0)[0]",
            "const ArraySubclass = class extends Array {}; new ArraySubclass().slice(0)[0]",
        ),
        (
            "class ArraySubclass extends Array {} new ArraySubclass().splice(0)[0]",
            "class ArraySubclass extends Array {} new ArraySubclass().slice(0)[0]",
        ),
        (
            "class ArraySubclass extends Array {} const array = new ArraySubclass(); array.splice(0)[0]",
            "class ArraySubclass extends Array {} const array = new ArraySubclass(); array.slice(0)[0]",
        ),
        (
            "class ArraySubclass extends Array { method() { return this.splice(0)[0]; } }",
            "class ArraySubclass extends Array { method() { return this.slice(0)[0]; } }",
        ),
        ("array.splice(index as number)[0]", "array.slice(index as number)[0]"),
        ("array.splice(<number>index)[0]", "array.slice(<number>index)[0]"),
        ("array.splice(index!)[0]", "array.slice(index!)[0]"),
        ("array.splice(index satisfies number)[0]", "array.slice(index satisfies number)[0]"),
        ("(array as string[]).splice(index)[0]", "(array as string[]).slice(index)[0]"),
        (
            "declare const array: string[]; array.splice(index)[0]",
            "declare const array: string[]; array.slice(index)[0]",
        ),
        (
            "type Strings = string[]; declare const array: Strings; array.splice(index)[0]",
            "type Strings = string[]; declare const array: Strings; array.slice(index)[0]",
        ),
        (
            "declare const value: unknown; value.splice(index)[0]",
            "declare const value: unknown; value.slice(index)[0]",
        ),
        (
            "type Value = Value; declare const value: Value; value.splice(index)[0]",
            "type Value = Value; declare const value: Value; value.slice(index)[0]",
        ),
        (
            "const array = array; array.splice(index)[0]",
            "const array = array; array.slice(index)[0]",
        ),
        (
            "function method(this: string[]) { return this.splice(0)[0]; }",
            "function method(this: string[]) { return this.slice(0)[0]; }",
        ),
        (
            "class ArraySubclass extends Array<number> {} declare const array: ArraySubclass; array.splice(0)[0]",
            "class ArraySubclass extends Array<number> {} declare const array: ArraySubclass; array.slice(0)[0]",
        ),
        (
            "const BaseArray = Array; class ArraySubclass extends BaseArray {} declare const array: ArraySubclass; array.splice(0)[0]",
            "const BaseArray = Array; class ArraySubclass extends BaseArray {} declare const array: ArraySubclass; array.slice(0)[0]",
        ),
        (
            "class ArraySubclass extends Array<number> {} const array = new ArraySubclass(); array.splice(0)[0]",
            "class ArraySubclass extends Array<number> {} const array = new ArraySubclass(); array.slice(0)[0]",
        ),
        (
            "function getArray(): string[] { return []; } const array = getArray(); array.splice(0)[0]",
            "function getArray(): string[] { return []; } const array = getArray(); array.slice(0)[0]",
        ),
        ("for (array.splice(0)[0] of values);", "for (array.slice(0)[0] of values);"),
        (
            "declare const a0: unknown; const a1 = c ? a0 : a0; const a2 = c ? a1 : a1; const a3 = c ? a2 : a2; const a4 = c ? a3 : a3; const a5 = c ? a4 : a4; const a6 = c ? a5 : a5; const a7 = c ? a6 : a6; const a8 = c ? a7 : a7; const set = new Set(); const value = c ? a8 : set; value.splice(0)[0]",
            "declare const a0: unknown; const a1 = c ? a0 : a0; const a2 = c ? a1 : a1; const a3 = c ? a2 : a2; const a4 = c ? a3 : a3; const a5 = c ? a4 : a4; const a6 = c ? a5 : a5; const a7 = c ? a6 : a6; const a8 = c ? a7 : a7; const set = new Set(); const value = c ? a8 : set; value.slice(0)[0]",
        ),
    ];

    Tester::new(PreferArraySlice::NAME, PreferArraySlice::PLUGIN, pass, fail)
        .change_rule_path_extension("ts")
        .expect_fix(fix)
        .test_and_snapshot();
}
