# Coq-tips
Some tips for poor programmers who have to use Coq for their projects.

## Naming conventions
Naming in Coq is a messy chaos. I personally use following convention.
* `PascalCase` for types
* `camelCase` for propositions and functions
* `snake_case` for lemmas and theorems
* `SCREAMING_SNAKE_CASE` for local hypothesis in proof mode

This gives sane name especially for lemmas involving several functions. e.g. `zipWith_length` instead of `zip_with_length`

## Syntactic problems
### Notation and implicit arguments
You may encounter a mysterious failure of unification. e.g. `eapply` fails though the conclusion of the given term and the goal seems equal.
In that case, try using `Set Printing All` to disable all notation and implicit arguments.
### Syntactically huge terms
Sometimes the term you want to refer which is contained in the context or the proof goal is syntactically too huge.
`match` and `match goal` tactics are very useful in such situation.

If you want to refer a subterm of the goal, use `match goal`.
```coq
match goal with
| ... => ...
end
```

If you want to refer a subterm of the type of a variable in the context, use combination of `match` and `type of`.
```coq
match type of H with
| ... => ... 
end.
```

## Mixing proof terms and tactics
There are several useful features for mixing tactics with manually written proof terms.
### `refine` tactic
Similar to `exact`, but holes are allowed.
### `Program Definition` and `Program Fixpoint`
To leave holes in a definition, or to obligate the proof of the termination of recursive definition.
### `ltac:(tac)`
Filling a hole in an expression by invoking a tactic.

## Normalization of proof terms
### `Qed` and `Defined`
It's okay to use proof mode for defining computable functions, but you must end the proof with `Defined` instead of `Qed`.
Otherwise, it won't reduce.
### `lia`
`lia` generates opaque proof term.
```coq
Lemma one_le_one : 1 <= 1.
Proof. lia. Defined.

Goal one_le_one = le_n 1.
Proof. reflexivity. (* fail *) Qed.
```

## Universe problems
`Set Printing Universes` and `Print Universes` are useful for debugging universe problems.

### Ban `Definition`
Types defined by `Definition` are not a subject to template polymorphism.
Use `Record` instead of `Definition` for defining generic types (i.e. types that quantify over `Type` universes).
`Notation` can also be an alternative solution.

See the following example.
```coq
Definition mylist1 := list.
Definition mylist2 (A : Type) := list A.
Record mylist3 (A : Type) := { car : list A; }.

Check [mylist1 nat] : list Type. (* fail *)
Check [mylist2 nat] : list Type. (* pass *)
Check mylist2 nat : Set. (* fail *)
Check mylist3 nat : Set. (* pass *)
```

## Other pitfalls

### `:>`
The meaning of `:>` when it is used in a record definition is completely different from the meaning when it is used in a class definition.
* In record definition, it declares the field as a coercion.
* In class definition, it declares the field as an instance of it's type (when the type of that field is also a class).
Note that this syntax is a subject to change. The `::` syntax will replace the usage of `:>` for instance declaration.

See also [defining-record-types](https://coq.inria.fr/refman/language/core/records.html#defining-record-types)
