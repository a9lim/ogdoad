//! Canonical display of values as programs.

use super::core::CtorRef;
use super::eval::value::Value;
use super::games::form::display_game_element;
use super::types::DataRegistry;

/// Display a value without a type annotation.
pub fn show_plain(value: &Value, data: &DataRegistry) -> String {
    match value {
        Value::Int(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(|item| show_plain(item, data))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::List(items) => format!(
            "[{}]",
            items
                .iter()
                .map(|item| show_plain(item, data))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Data(value) => {
            let name = ctor_name(&value.ctor, data);
            if value.fields.is_empty() {
                name
            } else {
                format!(
                    "{name}({})",
                    value
                        .fields
                        .iter()
                        .map(|field| show_plain(field, data))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        Value::Winner(w) => ["Left", "Right", "Draw"][*w as usize].to_string(),
        Value::Option(None) => "None".to_string(),
        Value::Option(Some(inner)) => format!("Some({})", show_plain(inner, data)),
        Value::Game(g) => g.display(),
        Value::Form(f) => display_game_element(&f.0),
        Value::Scalar(s) => s.to_string(),
        other => format!("<{}>", other.kind_name()),
    }
}

/// The surface name of a constructor.
pub fn ctor_name(ctor: &CtorRef, data: &DataRegistry) -> String {
    match ctor {
        CtorRef::Data(id, index) => data.get(*id).ctors[*index as usize].0.clone(),
        CtorRef::Winner(w) => ["Left", "Right", "Draw"][*w as usize].to_string(),
        CtorRef::Some => "Some".to_string(),
        CtorRef::None => "None".to_string(),
    }
}
