# lean-todomvc

A [TodoMVC](https://github.com/tastejs/todomvc) app whose behaviour is proved in
Lean 4 against a model of JavaScript and the DOM.

The app is ordinary vanilla JavaScript plus the standard TodoMVC markup. Both
are written inside Lean as data, where they define a transition system:

- **States** are the whole browser state: the DOM (including each element's
  event listeners), the JS global variables and functions, `localStorage`, the
  URL hash, and a log of uncaught errors.
- **Actions** are what a user can do: click, double-click, type into a field,
  press a key, blur a field, edit the URL, or reload the page.
- **The transition function** `δ : State → Action → State` runs the event
  listeners with an interpreter for a fragment of JavaScript. The initial state
  is the result of loading the markup and running the script.

The specification is written in the modal μ-calculus. Its atomic propositions
are predicates on states. They only describe what a user can observe (the
visible DOM and `localStorage`), never the app's internal variables. It follows
the [TodoMVC app spec](https://github.com/tastejs/todomvc/blob/master/app-spec.md).

The same JavaScript can be printed as a real web page and run in a browser.

## What is proved

`TodoMVC.invariant_holds : Sat specInvariant`. This says that every reachable
state satisfies the following properties:

- No listener has thrown an uncaught error.
- The list shows exactly the stored todos that pass the current filter
  (All / Active / Completed).
- `.main` and `.footer` are hidden exactly when there are no todos.
- The counter reads "*n* item(s) left", where *n* is the number of active
  todos.
- "Clear completed" is visible exactly when some todo is completed.
- The toggle-all checkbox is checked exactly when every todo is completed.
- Exactly the filter link for the current route is `.selected`.
- At most one todo is being edited.

The proof uses only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). It does not use `sorry` or `native_decide`.

There are also some checks that do use `native_decide`, which trusts the
compiler to evaluate concrete runs (all in `Spec.lean`):

- `bounded_invariant`: an exhaustive search over every action sequence of
  length 3, starting from several reachable states.
- `canComplete`: a witness that a completed todo is reachable.

The other spec formulas in `Spec.lean` are defined but not yet proved:
`specNewTodo`, `specClearCompleted`, `specToggleAll`, `specPersistence` and
`specRouting`.

### How the proof works

The invariant is about what the user sees, and it is not inductive on its own.
For example, a state can look right while the JS `filter` variable disagrees
with the URL, and then the next render goes wrong. So the proof uses a stronger
invariant, `Rep m s`. It says that the whole browser state `s` is exactly what
the app's `render()` produces from an abstract `Model` `m`, except for the text
the user has typed into input fields. The proof shows three things:

1. Loading the page gives a state satisfying `Rep` (`Proof/Init.lean`). This
   holds for an empty `localStorage` and for one saved by a previous session,
   so it covers both the initial state and reload.
2. Every action preserves `Rep` (`Proof/Dispatch.lean`). Each JS handler is
   specified as a transition on `Model` (`Proof/Handlers.lean`), proved by
   symbolic execution of the interpreter.
3. `Rep` implies each observable property (`Proof/Observe.lean`). This includes
   a proof that `JSON.parse` inverts `JSON.stringify` for the stored todos.

`Proof/Main.lean` then combines these by induction over reachability.

## Running the app

```sh
lake exe todomvc index.html   # or `lake exe todomvc` to print to stdout
```

This writes a single HTML page containing the markup and the script, and you
can open it in any browser. The script is printed from the same syntax tree
that the proofs are about. The printer itself (`Emit.lean`) is not verified.
The page links the standard `todomvc-app-css` stylesheet from unpkg.

## Building

```sh
lake exe cache get   # download prebuilt Mathlib
lake build           # check every proof
```

## Layout

| File | Contents |
| --- | --- |
| `LeanTodomvc/JS/Syntax.lean`, `JS/Notation.lean` | JS syntax and the `[js\| … ]` / `js_function` notation |
| `LeanTodomvc/JS/Interp.lean` | The interpreter (`partial_fixpoint`; divergence is `none`) |
| `LeanTodomvc/JS/Json.lean` | `JSON.stringify` / `JSON.parse` |
| `LeanTodomvc/DOM.lean` | The DOM as an arena of nodes, plus `querySelector`, `textContent`, etc. |
| `LeanTodomvc/System.lean` | States, actions and the transition function |
| `LeanTodomvc/App.lean` | The TodoMVC markup and script |
| `LeanTodomvc/Mu.lean` | The modal μ-calculus, `AG`/`EF`, and a sound bounded checker |
| `LeanTodomvc/Spec.lean` | Observations, the invariant, spec formulas and bounded checks |
| `LeanTodomvc/Emit.lean`, `Main.lean` | Printing the app as HTML + JS |
| `LeanTodomvc/Proof/` | The unbounded proof (see above) |

## Limitations

The guarantee only covers the model:

- **JavaScript** is a fragment: integers instead of IEEE doubles, a small set
  of built-in methods, and no prototypes or closures beyond `bind`.
- **The DOM** has no focus model. In particular, re-rendering does not fire
  `blur` on the edit field it removes, as a real browser would.
- **Events** have no bubbling or capture.
- **The emitted page** is produced by an unverified printer.
