import LeanTodomvc.JS.Syntax

/-!
# `JSON.stringify` / `JSON.parse`

`localStorage` stores strings, so persistence goes through a (simplified)
model of JSON. Non-JSON values (`undefined`, nodes, functions, host objects)
are stringified as `null`.
-/

namespace JS.Json

def escapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => c.toString

def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

mutual
def stringify : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => quote s
  | .arr vs => "[" ++ ",".intercalate (stringifyList vs) ++ "]"
  | .obj fs => "{" ++ ",".intercalate (stringifyFields fs) ++ "}"
  | _ => "null"
def stringifyList : List Value → List String
  | [] => []
  | v :: vs => stringify v :: stringifyList vs
def stringifyFields : List (String × Value) → List String
  | [] => []
  | (k, v) :: fs => (quote k ++ ":" ++ stringify v) :: stringifyFields fs
end

def skipWs : List Char → List Char
  | c :: cs => if c == ' ' || c == '\n' || c == '\t' || c == '\r' then skipWs cs else c :: cs
  | [] => []

/-- Parse the body of a string literal (after the opening quote). -/
def parseStrBody : List Char → List Char → Option (String × List Char)
  | acc, '"' :: cs => some (String.ofList acc.reverse, cs)
  | acc, '\\' :: c :: cs =>
    let d := match c with
      | 'n' => some '\n' | 'r' => some '\r' | 't' => some '\t'
      | '"' => some '"' | '\\' => some '\\' | '/' => some '/'
      | _ => none
    match d with
    | some d => parseStrBody (d :: acc) cs
    | none => none
  | acc, c :: cs => parseStrBody (c :: acc) cs
  | _, [] => none

def parseDigits : List Char → Nat → Nat × List Char
  | c :: cs, n => if c.isDigit then parseDigits cs (10 * n + (c.toNat - '0'.toNat)) else (n, c :: cs)
  | [], n => (n, [])

def parseNat (cs : List Char) : Option (Nat × List Char) :=
  match cs with
  | c :: _ => if c.isDigit then some (parseDigits cs 0) else none
  | [] => none

def expectLit : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | l :: ls, c :: cs => if l == c then expectLit ls cs else none
  | _ :: _, [] => none

mutual
def parseValue : Nat → List Char → Option (Value × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipWs cs with
    | '"' :: cs => (parseStrBody [] cs).map fun (s, r) => (.str s, r)
    | '[' :: cs =>
      match skipWs cs with
      | ']' :: r => some (.arr [], r)
      | _ => (parseElems fuel cs []).map fun (vs, r) => (.arr vs, r)
    | '{' :: cs =>
      match skipWs cs with
      | '}' :: r => some (.obj [], r)
      | _ => (parseFields fuel cs []).map fun (fs, r) => (.obj fs, r)
    | 't' :: cs => (expectLit "rue".toList cs).map fun r => (.bool true, r)
    | 'f' :: cs => (expectLit "alse".toList cs).map fun r => (.bool false, r)
    | 'n' :: cs => (expectLit "ull".toList cs).map fun r => (.null, r)
    | '-' :: cs => (parseNat cs).map fun (n, r) => (.num (-(n : Int)), r)
    | cs => (parseNat cs).map fun (n, r) => (.num n, r)
def parseElems : Nat → List Char → List Value → Option (List Value × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
    match parseValue fuel cs with
    | none => none
    | some (v, r) =>
      match skipWs r with
      | ',' :: r => parseElems fuel r (v :: acc)
      | ']' :: r => some ((v :: acc).reverse, r)
      | _ => none
def parseFields : Nat → List Char → List (String × Value) →
    Option (List (String × Value) × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
    match skipWs cs with
    | '"' :: cs =>
      match parseStrBody [] cs with
      | none => none
      | some (k, r) =>
        match skipWs r with
        | ':' :: r =>
          match parseValue fuel r with
          | none => none
          | some (v, r) =>
            match skipWs r with
            | ',' :: r => parseFields fuel r ((k, v) :: acc)
            | '}' :: r => some (((k, v) :: acc).reverse, r)
            | _ => none
        | _ => none
    | _ => none
end

/-- `JSON.parse`; `none` means a `SyntaxError` is thrown. -/
def parse (s : String) : Option Value :=
  let cs := s.toList
  match parseValue (2 * cs.length + 2) cs with
  | some (v, r) => if skipWs r == [] then some v else none
  | none => none

end JS.Json
