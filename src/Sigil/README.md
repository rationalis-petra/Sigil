# sigil Directory

This directory contains an implementations of all major components of the sigil
langauge. It is divided into 6 subcomponents:

+ **Abstract** : Contains a description of the abstract syntax tree and
  environments, with some common typeclass instances (Eq, Pretty etc.). It also
  contains a description of unification formulas, and contains some functions
  for manipulating terms like substitution and alpha equality.
+ **Concrete** : Concrete contains a small number of files which instantiate the
  abstract syntax tree for various purposes, e.g. parsing
+ **Parse** : Contains the parser for sigil
+ **Analysis** : Various algorithms which analyse and/or transform the sigil
  Syntax tree (e.g. typechecking, name resolution or totality checking).
+ **Interpret** : This module contains an abstract description of an
  interpreter, which is capable of evaluating a syntax tree and solving a
  unification problem. It then contains several implementations, including a
  simple tree-walking interpreter, and more advanced interpreters making use of
  various backends (like the JVM, bytecode, JIT etc.)
+ **Compile** : Contains everything necessary to generate programs in various
  backends. 
+ **Image** (Not implemented): In the future, Interpreter backends will be
  capable of reflecting their current state into a data-structure, which can
  then be serialized-deserialized via an `image` file, enabling individuals to
  halt & resume sessions/programs.

Note that each sigil mode (compilation/interactive/server) ties these components
together differently.

