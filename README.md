# Coq-tips
A tip for poor programmers who have to use Coq for their projects.

## Notation and implicit arguments
You may encounter a mysterious failure of unification. e.g. `eapply` fails though the given term and the goal seems equal.
In that case, try using `Set Printing All` to disable all notation and implicit arguments.

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
`Set Printing Universes.` and `Print Universes.` are useful for debugging universe problems.

### Ban `Definition`
Types defined by `Definition` are not a subject to template polymorphism.
Use `Record` instead of `Definition` for defining generic types (i.e. types that quantifies over `Type` universes).
`Notation` can also be an alternative solution.

See the follwing example.
```coq
Definition mylist1 := list.
Definition mylist2 (A : Type) := list A.
Record mylist3 (A : Type) := { car : mylist A; }.

Check [mylist1 nat] : list Type.
Check [mylist2 nat] : list Type.
Check mylist2 nat : Set.
Check mylist3 nat : Set.
```
