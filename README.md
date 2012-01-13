Copyright (C) 2011 Daniel P. Friedman, Oleg Kisselev,
Claire E. Alvis, Jeremiah J. Willcock, Kyle M. Carter, William E. Byrd

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.


----------------------------------------------------------------------------

The cKanren library (found in ck.scm) imports Chez Scheme paramters. 
In order to use a different implementation of parameters, simply change 
that import to the library of your choice (one alternative is SRFI 39).

----------------------------------------------------------------------------

Usage:
-----

Here are some examples for using cKanren and miniKanren. These require
that cKanren be in your current directory, or alternative in your
libdirs path (if your implementation supports such a feature). For
instance, with Chez Scheme:

    mv cKanren /usr/lib/scheme/
    scheme --libdirs ".:/usr/lib/scheme" --program my-minikanren-program.ss

Or:

    mv cKanren /usr/lib/scheme/
    export CHEZSCHEMELIBDIRS="$CHEZSCHEMELIBDIRS:/usr/lib/scheme"
    scheme --program my-minikanren-program.ss

Here are some exmaples of importing:

    (library (foo)
      (export bar)
      (import 
        (cKanren miniKanren)
        (cKanren mk)
        (cKanren tree-unify))
      
      ;; your miniKanren code)

And another:

    (library (baz)
      (export bar)
      (import 
        (cKanren ck)
        (cKanren miniKanren)
        (cKanren mk)
        (cKanren tree-unify))
      
      ;; your cKanren code)

As long as you're using an R6RS scheme, you should also be able to use
load. However, using load has seen numerous problems in several users
experiences. A few examples that seems to work are below:

    ;; Presumes cKanren is in your current directory.
    (cd "cKanren")
    (load "ck.scm")
    (load "miniKanren.scm")
    (load "mk.scm")
    (load "tree-unify.scm")
    (cd "..")
    ;; your code

Or:

    ;; the files must be in or symlinked in your current directory
    (load "ck.scm")
    (load "miniKanren.scm")
    (load "mk.scm")
    (load "tree-unify.scm")
    ;; your code

