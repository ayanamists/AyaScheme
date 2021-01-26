module Ast

type Identifier = string

type Expr = 
| Int of int64
| Id of Identifier
| LetExp of ((Identifier * Expr) list) * Expr
| AppExp of Identifier * (Identifier) list
