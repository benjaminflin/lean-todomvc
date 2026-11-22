import LeanTodomvc.System

/-! Pretty-printing of the visible document, for inspecting traces. -/

namespace World
open DOM

/-- Render the subtree at `n` as HTML-like text, omitting hidden subtrees. -/
def pretty (w : World) (n : Nat := 0) (indent : String := "") : String :=
  go w.dom.size n indent
where
  go : Nat → Nat → String → String
    | 0, _, _ => ""
    | f + 1, n, ind =>
      let nd := w.node n
      if nd.tag == "#text" then ind ++ "\"" ++ nd.text ++ "\"\n"
      else if nd.hidden then ind ++ "<" ++ nd.tag ++ " hidden …>\n" else
      let cls := if nd.className.isEmpty then "" else " class=\"" ++ nd.className ++ "\""
      let val := if nd.tag == "input" then
          (if nd.value.isEmpty then "" else " value=\"" ++ nd.value ++ "\"") ++
          (if nd.checked then " checked" else "")
        else ""
      ind ++ "<" ++ nd.tag ++ "#" ++ toString n ++ cls ++ val ++ ">\n" ++
        String.join (nd.children.map fun c => go f c (ind ++ "  "))

end World

def State.pretty (s : State) : String :=
  s.world.pretty ++ "localStorage: " ++ toString s.world.storage ++ "\nerrors: " ++ toString s.errors
