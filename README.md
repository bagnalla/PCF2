# PCF2
A Haskell implementation of a Programming Computable Functions (PCF) interpreter with a Hindley-Milner style type system.

This is a statically typed lambda calculus with Booleans, natural numbers, and a fix operator for general recursion. It is based on material from "Types and Programming Languages" by Benjamin Pierce. The evaluation strategy is call-by-value.

[Stack](https://docs.haskellstack.org/en/stable/README/) (>= 1.4.0) is required. See example.cf for an example program. To run it, type "stack build && stack exec PCF2-exe example.cf" in the root project directory.

Some basic logical and arithmetic functions are defined in prelude.cf. They can be imported by using 'import prelude'. The import feature is very basic -- it simply inlines the imported file in the place of the import command. Imported files can't import other files, so if they depend on other files you must make sure to import them manually and in the correct order.

A program is a sequence of commands, each of which is either a bind or eval command (not counting imports).
* bind - assign a term to a name in the global environment, so that the name may appear free in the terms of subsequent commands.
* eval - evaluate a term. Guaranteed by the type system to reduce to a value, given that it doesn't diverge.

The result of the last command is displayed by the interpreter. It can be either bind or eval -- the result of a bind is a (Id, Term) pair; the result of an eval is the value resulting from reducing a term.
