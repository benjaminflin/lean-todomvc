# Overall goal

We are going to build a semi-formally verified version of the TodoMVC app
using a model of javascript and the dom. We will try to follow the specification
provided [here](https://github.com/tastejs/todomvc/blob/master/app-spec.md).

## Transition System and Modal $\mu$-calculus

It will consist of a transition system ($\delta : S \to A \to S$) where the state contains:

- The DOM (and the state of each element, including `onClick` handlers)
- The javascript state, more or less the mapping from each variable to its value
- What is stored in `localStorage`

Actions will basically only include clicking and typing events on different
elements in the DOM.

The initial state of this transition system will be determined by the javascript code 
and the html markup. 

Where possible, the specification should be made in the modal mu-calculus where atomic
propositions are replaced with predicates on the state.

