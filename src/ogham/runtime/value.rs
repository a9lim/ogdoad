//! Runtime values and closed function carriers.

use super::*;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Value<E> {
    Element(E),
    Index(i128),
    Bool(bool),
    Function(FunctionValue),
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct FunctionValue {
    pub(crate) binders: Vec<Binder>,
    pub(crate) body: Expr,
    pub(crate) ret: Sort,
    pub(crate) mu_name: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Binder {
    pub(crate) name: String,
    pub(crate) sort: Sort,
}

impl FunctionValue {
    pub(crate) fn binder_names(&self) -> Vec<String> {
        self.binders
            .iter()
            .map(|binder| binder.name.clone())
            .collect()
    }

    pub(crate) fn lambda_expr(&self) -> Expr {
        Expr::Lambda {
            binders: self.binder_names(),
            body: Box::new(self.body.clone()),
        }
    }

    pub(crate) fn to_expr(&self) -> Expr {
        self.mu_name.as_ref().map_or_else(
            || self.lambda_expr(),
            |name| Expr::Block {
                bindings: vec![Binding {
                    name: name.clone(),
                    expr: self.lambda_expr(),
                    recursive: true,
                }],
                body: Box::new(Expr::Ident(name.clone())),
            },
        )
    }
}

pub(crate) fn validation_sample_function(function: &FunctionValue, body: Expr) -> FunctionValue {
    FunctionValue {
        binders: function.binders.clone(),
        body,
        ret: function.ret,
        mu_name: None,
    }
}

pub(crate) fn display_value<E: Display>(value: &Value<E>) -> String {
    match value {
        Value::Element(value) => value.to_string(),
        Value::Index(value) => display_index(*value),
        Value::Bool(value) => value.to_string(),
        Value::Function(function) => {
            let lambda = crate::ogham::unparse::unparse_expr(&function.lambda_expr());
            function
                .mu_name
                .as_ref()
                .map_or(lambda.clone(), |name| format!("{name} =: {lambda}"))
        }
    }
}
