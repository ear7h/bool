# bool

`bool` is WIP boolean algebra calulator and proof assitant.

Currently it can list and equate truth tables for a formaulas and apply some of
the boolean algebra theorems to manupulate such formulas.

## Goal

The end goal is to have a command line utility or parse that can check and
display reductions of boolean formulas.

Such a session might look like:


```
(B+(BC)) (B + 0)'
    =~>             0 // ok
```

```
(B+(BC)) (B + 0)'
    =~>             BB'
    =complement>    0 // ok
```

```
(B+(BC)) (B + 0)'
    =demorgan>      (B+(BC))B'1
    =~>             BB'
    =complement>    0 // ok
```

```
(B+(BC)) (B + 0)'
    =demorgan>      (B+(BC))B'1
    =idempotent>    (B+(BC))B // fail
    =~>             BB'
    =complement>    0
```

```
(B+(BC)) (B + 0)'
    =demorgan>      (B+(BC))B'1
    =idempotent>    (B+(BC))B'
    =cover>         BB'
    =complement>    0 // ok
```

This syntax and workflow are inspired by
[elsa](https://github.com/ucsd-progsys/elsa/) a lambda calculus proof
assistant.

