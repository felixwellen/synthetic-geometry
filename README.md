# Synthetic Geometry
So far, this formalization project is only about synthetic algebraic geometry.
A good place to start is [here](SyntheticGeometry/Spec.lagda.md).

# How to check/work on the code in this repo
In ```~/.agda/libraries``` there should be a line ```PATH/cubical.agda-lib```, where PATH is the path to the root of the clone of the cubical library you want to use.
Right now, this project builds on this PR 

[https://github.com/agda/cubical/pull/680](https://github.com/agda/cubical/pull/680)

on the cubical agda library.

# Practicalities
The agda-mode (of Emacs) is not loaded for '.lagda.md'-files which we use here, so you might want to add something like the following to your .emacs (after agda-mode setup):

```lisp
;; also load agda-mode for .lagda.md
(add-to-list 'auto-mode-alist '("\\.l?agda.md\\'" . agda2-mode))
(modify-coding-system-alist 'file "\\.l?agda.md\\'" 'utf-8)
```