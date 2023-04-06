# Glyph Directory

This directory contains an implementations of all major components of the Glyph
langauge. It is divided into 6 subcomponents:

+ **Abstract** : Contains a description of the abstract syntax tree and
  environments, with some common typeclass instances (Eq, Pretty etc.). It also
  contains various extensions to the syntax tree in the 'decorations' folder.
+ **Concrete** : Concrete contains a small number of files which instantiate the
  abstract syntax tree for various purposes, e.g. parsing
+ **Parse** : Contains the parser for Glyph
+ **Analysis** : Various algorithms which analyse and/or transform the Glyph
  Syntax tree (e.g. typechecking, name resolution or totality checking).
+ **Interpret** : Contains everything related to live evaluation of the
  syntax-tree, including a tree-walking interpeter, higher order unification
  algorithm and JIT compiler.
+ **Compile** : Contains everything necessary to generate programs in various
  backends.

Note that each Glyph mode (compilation/interactive/server) ties these components
together differently.
