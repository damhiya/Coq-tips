# Coq-tips
A tip for poor programmers who have to use Coq for their projects.

## Universe problems
`Set Printing Universes.` and `Print Universes.` are useful for debugging universe problems.

### Ban `Definition`
Use `Record` instead of `Definition` for defining generic types (i.e. types that quantifies over `Type` universe).
`Notation` can also be an alternative solution.
See the follwing example
```coq
Definition mylist1 := list.
Definition mylist2 (A : Type) := list A.
Record mylist3 (A : Type) := { car := mylist A; }.

Check [mylist1 nat] : list Type.
Check [mylist2 nat] : list Type.
Check mylist2 nat : Set.
Check mylist3 nat : Set.
```
