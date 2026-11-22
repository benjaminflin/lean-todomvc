import LeanTodomvc.Proof.Model

/-!
# `JSON.parse` inverts `JSON.stringify` on lists of todos
-/
namespace TodoMVC.Proof
open JS JS.Json

theorem parseDigits_append (ds r : List Char) (n : Nat) (hd : ∀ c ∈ ds, c.isDigit)
    (hr : ∀ c ∈ r.head?, c.isDigit = false) :
    parseDigits (ds ++ r) n = (Nat.ofDigitChars 10 ds n, r) := by
  induction ds generalizing n with
  | nil =>
    cases r with
    | nil => simp [parseDigits]
    | cons c r => simp at hr; simp [parseDigits, hr]
  | cons c ds ih =>
    simp at hd
    simp [parseDigits, hd.1, ih _ hd.2, Nat.ofDigitChars_cons]

theorem parseNat_toDigits (k : Nat) (r : List Char) (hr : ∀ c ∈ r.head?, c.isDigit = false) :
    parseNat (Nat.toDigits 10 k ++ r) = some (k, r) := by
  have hd : ∀ c ∈ Nat.toDigits 10 k, c.isDigit := fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := k) (b := 10))
  have h1 : c.isDigit := hd c (by simp [hc])
  rw [hc] at hd ⊢
  simp only [parseNat, List.cons_append, h1, ite_true]
  rw [← List.cons_append, parseDigits_append _ _ _ hd hr, ← hc, Nat.ofDigitChars_ten_toDigits]

def escList (cs : List Char) : List Char := cs.flatMap fun c => (escapeChar c).toList

theorem parseStrBody_escapeChar (c : Char) (acc rest : List Char) :
    parseStrBody acc ((escapeChar c).toList ++ rest) = parseStrBody (c :: acc) rest := by
  unfold escapeChar
  split
  case h_6 h1 h2 _ _ _ =>
    simp only [Char.toString_eq_singleton, String.toList_singleton, List.cons_append, List.nil_append]
    conv => lhs; unfold parseStrBody
    split <;> simp_all
  all_goals simp [parseStrBody]

theorem parseStrBody_esc (cs acc r : List Char) :
    parseStrBody acc (escList cs ++ '"' :: r) = some (String.ofList (acc.reverse ++ cs), r) := by
  induction cs generalizing acc with
  | nil => simp [escList, parseStrBody]
  | cons c cs ih =>
    simp only [escList, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [parseStrBody_escapeChar, ih]
    simp

theorem skipWs_digit (c : Char) (cs : List Char) (h : c.isDigit) : skipWs (c :: cs) = c :: cs := by
  have : ¬ (c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r') := by
    rintro (rfl | rfl | rfl | rfl) <;> revert h <;> decide
  simp only [not_or] at this
  simp [skipWs, this]

theorem parseValue_digits (f k : Nat) (r : List Char) (hr : ∀ c ∈ r.head?, c.isDigit = false) :
    parseValue (f + 1) (Nat.toDigits 10 k ++ r) = some (.num k, r) := by
  have hd : ∀ c ∈ Nat.toDigits 10 k, c.isDigit := fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := k) (b := 10))
  have h1 : c.isDigit := hd c (by simp [hc])
  have hp := parseNat_toDigits k r hr
  rw [hc] at hp ⊢
  simp only [parseValue, List.cons_append, skipWs_digit _ _ h1]
  split <;> (try (rename_i h; simp at h; obtain ⟨rfl, _⟩ := h; simp [Char.isDigit] at h1))
  simp only [List.cons_append] at hp; simp [hp]

theorem escapeChar_alpha (c : Char) (h : c.isAlpha) : (escapeChar c).toList = [c] := by
  unfold escapeChar
  split <;> first | (revert h; decide) | simp

def boolChars (b : Bool) : List Char := if b then ['t', 'r', 'u', 'e'] else ['f', 'a', 'l', 's', 'e']

def todoChars (t : TodoR) : List Char :=
  "{\"id\":".toList ++ Nat.toDigits 10 t.id.toNat ++ ",\"title\":\"".toList ++ escList t.title.toList ++
    "\",\"completed\":".toList ++ boolChars t.completed ++ ['}']

theorem toList_stringify_todo (t : TodoR) (h : 0 ≤ t.id) : (stringify t.val).toList = todoChars t := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
  rcases t with ⟨id, title, c⟩
  simp only at hk; subst hk
  cases c <;> simp [stringify, stringifyFields, TodoR.val, todoChars, quote, escList, String.toList_join,
    boolChars, Nat.toList_repr, Int.repr, List.flatMap_map, escapeChar_alpha]

theorem parseValue_str (f : Nat) (cs r : List Char) :
    parseValue (f + 1) ('"' :: (escList cs ++ '"' :: r)) = some (.str (String.ofList cs), r) := by
  simp [parseValue, skipWs, parseStrBody_esc]

theorem parseValue_digits_comma (f k : Nat) (r : List Char) :
    parseValue (f + 1) (Nat.toDigits 10 k ++ ',' :: r) = some (.num k, ',' :: r) :=
  parseValue_digits f k _ (by simp)

theorem parseValue_bool (f : Nat) (b : Bool) (r : List Char) :
    parseValue (f + 1) (boolChars b ++ r) = some (.bool b, r) := by
  cases b <;> simp [parseValue, boolChars, skipWs, expectLit]

theorem parseValue_todo (f : Nat) (t : TodoR) (r : List Char) (h : 0 ≤ t.id) :
    parseValue (f + 5) (todoChars t ++ r) = some (t.val, r) := by
  rcases t with ⟨id, title, c⟩
  simp only [todoChars, List.append_assoc]
  rw [parseValue]
  simp [skipWs, parseFields, parseStrBody, parseValue_digits_comma, parseValue_str, parseValue_bool, TodoR.val]
  simp at h; omega

theorem intercalate_comma (x : List Char) (xs : List (List Char)) :
    [','].intercalate (x :: xs) = x ++ (xs.map (',' :: ·)).flatten := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih => rw [List.intercalate_cons_cons, ih]; simp

theorem stringifyList_map (ts : List TodoR) :
    stringifyList (ts.map TodoR.val) = ts.map (stringify ∘ TodoR.val) := by
  induction ts with
  | nil => simp [stringifyList]
  | cons t ts ih => simp [stringifyList, ih]

theorem toList_stringify_todos (ts : List TodoR) (h : ∀ t ∈ ts, 0 ≤ t.id) :
    (stringify (todosVal ts)).toList =
      '[' :: [','].intercalate (ts.map todoChars) ++ [']'] := by
  have : ts.map (fun t => (stringify t.val).toList) = ts.map todoChars :=
    List.map_congr_left fun t ht => toList_stringify_todo t (h t ht)
  simp [todosVal, stringify, stringifyList_map, Function.comp_def, this]

theorem length_todoChars (t : TodoR) : 6 ≤ (todoChars t).length := by
  simp [todoChars]

/-- Elements after the first, each preceded by a comma. -/
theorem parseElems_todos (ts : List TodoR) (h : ∀ t ∈ ts, 0 ≤ t.id) (t : TodoR) (ht : 0 ≤ t.id)
    (acc : List Value) (f : Nat) (r : List Char) :
    parseElems (f + ts.length + 6) (todoChars t ++ (ts.map (',' :: todoChars ·)).flatten ++ ']' :: r) acc =
      some (acc.reverse ++ t.val :: ts.map TodoR.val, r) := by
  induction ts generalizing t acc with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, List.map_nil, List.flatten_nil, List.append_nil]
    rw [show f + 6 = (f + 1 + 5) by omega, parseElems, parseValue_todo _ _ _ ht]
    simp [skipWs]
  | cons t' ts ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons]
    rw [show f + (ts.length + 1) + 6 = (f + ts.length + 1) + 5 + 1 by omega, parseElems,
      List.append_assoc, parseValue_todo _ _ _ ht]
    simp at h
    simp only [List.cons_append, skipWs]
    simp only [show (',' == ' ' || ',' == '\n' || ',' == '\t' || ',' == '\r') = false by decide]
    simp only [Bool.false_eq_true, ite_false]
    rw [ih h.2 t' h.1]
    simp


theorem parseValue_arr (F : Nat) (rest : List Char) :
    parseValue (F + 1) ('[' :: '{' :: rest) = (parseElems F ('{' :: rest) []).map (fun x => (.arr x.1, x.2)) := by
  simp [parseValue, skipWs]

theorem parse_stringify_todos (ts : List TodoR) (h : ∀ t ∈ ts, 0 ≤ t.id) :
    parse (stringify (todosVal ts)) = some (todosVal ts) := by
  unfold parse
  rw [toList_stringify_todos ts h]
  cases ts with
  | nil => simp [parseValue, skipWs, todosVal]
  | cons t ts =>
    simp only [List.map_cons, intercalate_comma, List.map_map, Function.comp_def]
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have hlen : ts.length ≤ ((ts.map (',' :: todoChars ·)).flatten).length := by
      clear h; induction ts with
      | nil => simp
      | cons a as ih => simp at ih ⊢; omega
    have h6 := length_todoChars t
    generalize hL : ('[' :: (todoChars t ++ (ts.map (',' :: todoChars ·)).flatten) ++ [']']).length = L
    have hL' : L = (todoChars t).length + ((ts.map (',' :: todoChars ·)).flatten).length + 2 := by
      rw [← hL]; simp; omega
    have hc : todoChars t = '{' :: (todoChars t).tail := by simp [todoChars]
    rw [show 2 * L + 2 = (2 * L + 1 - ts.length - 6) + ts.length + 6 + 1 by omega, List.cons_append, hc,
      List.cons_append, List.cons_append, parseValue_arr, ← List.cons_append, ← List.cons_append, ← hc,
      show [']'] = ']' :: ([] : List Char) from rfl, parseElems_todos ts h.2 t h.1]
    simp [skipWs, todosVal]

end TodoMVC.Proof
