Copyright (C) 2013-4 Claire Alvis

Copyright (C) 2011-2013 Daniel P. Friedman, Oleg Kiselyov,
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

cKanren
=======

This library implements miniKanren (http://minikanren.org) with an
extensible framework for defining constraints.

How to install
--------------

cKanren can be installed as a collection within Racket (http://racket-lang.org)
as follows:

* `git clone git://github.com/calvis/cKanren.git`
* `cd cKanren/cKanren`
* `raco link .`
* `raco setup cKanren`

After setup finishes, you will be able to use miniKanren, `#lang
cKanren`, and all constraint libraries that ship with cKanren.

For users
---------

If you are interested in writing miniKanren programs, you can
`(require cKanren/miniKanren)` for standard miniKanren definitions.
You can also require constraint libraries like `neq` as `(require
cKanren/neq)`.  

Stable constraint libraries
---------------------------

The following libraries have been tested extensively.

* Tree unification              `cKanren/tree-unify`
* Disequality constraints       `cKanren/neq`
* Absento, symbolo, and numbero `cKanren/absento`

All other constraints libraries are experimental.

