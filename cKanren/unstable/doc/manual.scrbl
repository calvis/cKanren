#lang scribble/doc

@(require (except-in scribble/manual var)
          racket/base
          scribble/eval
          racket/contract)

@(require (for-label cKanren/ck) 
          (for-label racket/base))

@title{cKanren}

cKanren is a framework for defining constraints in miniKanren.  The
following is a description of all building blocks available to
constraint writers, and convenience definitions that can be
re-exported for the user.

@(define ck-eval (make-base-eval))
@(interaction-eval #:eval ck-eval (require cKanren/ck))

@section{Variables}
@(declare-exporting cKanren/ck)

@defproc[(var [x symbol?]) var?]
Creates a new variable.  Use sparingly.

@defproc[(var? [x any/c?]) boolean]{ Returns @racket[#t] if @racket[x]
is a @racket[var], @racket[#f] otherwise. }

@defform[#:literals (name)
         (define-var-type name display-str)]

Defines a new kind of constrained variable that displays
@racket[display-str] before it's value.  This should be used instead
of @racket[var] wherever possible.

@examples[
#:eval ck-eval
(define-var-type nom "a")
(define new-nom (nom 'my-nom))
new-nom
(and (var? new-nom) (nom? new-nom))
]

@section{Goals}
@(declare-exporting cKanren/ck)

A function that operates on values in cKanren is called a
@deftech{goal}.  Each goal takes the state of the program as an
argument, and returns a possibly infinite stream of new states.  A
goal that produces at least one new state @deftech{succeeds}, whereas
an unsatisfiable goal @deftech{fails} and produces no answers.  The
state is represented as a @tech{package} of information, the structure
of which we will discuss later on.  

@defform*[#:literals (:)
          [(lambdag@ (a) body ...+)
           (lambdag@ (a : s) body ...+)
           (lambdag@ (a : s c) body ...+)]]{

Produces a goal.  The current package, @racket[a], can be split up
into its individual parts by providing identifiers for @racket[s] and
@racket[c].  }

@defproc[(goal? [x any/c]) boolean]{ Returns @racket[#t] if
@racket[x] is a goal created with @racket[lambdag@], @racket[#f]
otherwise. }

@defthing[succeed goal?]{ The simplest goal that @tech{succeeds}. }
@defthing[fail goal?]{ The simplest goal that @tech{fails}. }

@defthing[prt goal?]{ A goal that print out the current state of the
program and succeeds. }

@defproc*[([(prtm [str string?]) goal?]
           [(prtm [format-str string?] [args any/c?] ...) goal?])]{

Returns a goal that prints @racket[str] or the result of
@racket[(printf format-str args ...)] and then succeeds. }

@defform[(run num (q) goal ...+)]

Runs each @racket[goal] with a new variable @racket[q].  The result is
either a list containing @racket[num] values for @racket[q], or all
possible answers for @racket[q] when @racket[num] is @racket[#f].

@defform[(run* (q) goal ...)]
Short-hand for @racket[(run #f (q) goal ...)]

@examples[
#:eval ck-eval
(run* (q) fail)
(run* (q) succeed)
(run* (q) (prtm "(╯°□°）╯︵ ┻━┻"))
(run* (q) "I am not a goal :(")
(run* (q) (lambdag@ (a) (printf "here's an empty a: ~s\n" a) a))
]

The result @racket['()] means that there are no values for @racket[q]
that satisfy the goals in the body.  Alternatively, @racket['(__.0)]
means that when the program finishes, @racket[q] can be anything.
This answer makes sense because @racket[succeed] does not contain any
information.

@defform[(fresh (x ...) goal ...+)]{

Produces a new goal that is the conjunction of the goals in the body
where each @racket[x] is a @deftech{fresh} (read "unconstrained")
lexically-scoped variable.  }

@defform[(fresh-aux constructor (x ...) goal ...+)]{

Introduces each @racket[x] as @racket[(constructor 'x)] instead of as
a normal cKanren variable.  }

@examples[
#:eval ck-eval
(define-var-type pony "mlp")
(define-syntax-rule (new-pony (anypony ...) goals ...)
  (fresh-aux pony (anypony ...) goals ...))
(run* (q) 
  (new-pony (pinkie-pie rainbow-dash)
    (prtm "~s\n" (list pinkie-pie rainbow-dash))))
]

@defform/subs[(conde clause ...+)
              ([clause [goal ...+] [#:name id goal ...+]])]{

Branches and evaluates each @racket[clause] independently.  The named
clause form is described in a later section.  }

@examples[
#:eval ck-eval
(run* (q) 
  (conde 
    [(prtm "this line generates one answer\n")]
    [(prtm "this line generates another!\n")]))
]
Note that both answers are returned together at the end.

@section{Constraints} 
@(declare-exporting cKanren/ck)

A @deftech{constraint} is simply imitation-@tech{goal} that can
return at most one output state.  This implies any language feature
that returns a goal, like @racket[fresh] and @racket[conde], cannot be
used inside a constraint.  Unlike goals, constraints can be stored for
later evaluation.  

@defform*[#:literals (:)
          [(lambdam@ (a) body ...+)
           (lambdam@ (a : s) body ...+)
           (lambdam@ (a : s c) body ...+)]]{

Equivalent to @racket[lambdag@] except that a constraint is produced
instead of a goal.  }

@defthing[identitym constraint?]
The simplest succeeding constraint.

@defthing[mzerom constraint?]
The simplest failing constraint.

@defproc[(bindm [a a?] [fm constraint?]) (maybe a?)]{ Functionally
equivalent to @racket[(fm a)], but so much prettier. }

@defproc[(composem [fm constraint?] ...) constraint?]{ Composes an
arbitrary number of constraints together, threading through the state
from left to right. }

@defstruct[oc ([proc constraint?] [rator symbol?] [rands list?])]{

The stored version of a constraint.  @racket[proc] is an instance of
the constraint @racket[rator] called on @racket[rands].  When an
@racket[oc] is printed out, the @racket[proc] is hidden.  }

@defform[(build-oc op args ...)]{

Builds an @racket[oc], where @racket[proc] is @racket[(op args ...)],
@racket[rator] is @racket['op], and @racket[rands] is @racket[`(,args
...)]. }

@examples[
#:eval ck-eval
(define (my-constraint x y) identitym)
(build-oc my-constraint 5 6)
]

@section{The Package}
@(declare-exporting cKanren/ck)

All of the information generated by a cKanren program is contained in
a @deftech{package}.  There are at most four parts to any package: the
@tech{substitution}, @tech{constraint store}, @tech{queue}, and
@tech{path}.  These structures will be talked about in more depth in
the section about @secref{Constraints}.

@subsection{Substitution}

The @deftech{substitution} (abbreviated @racket[s]) contains all
mappings of variables to ground terms.  It contains at most one
binding for every variable, but it is not idempotent.  An association
list can always be used as a substitution, but the internal
representation may change.

@defproc[(walk [v any/c?] [s s?]) any]{

Retrieves the binding for @racket[v] in @racket[s].  If @racket[v] is
not a @racket[var?], or has no binding in @racket[s], it is returned
unchanged.  If @racket[v] is bound to a variable @racket[u] in
@racket[s], then @racket[(walk v s)] is returned.  }

@examples[
#:eval ck-eval
(let ([x (var 'x)] [y (var 'y)] [z (var 'z)])
  (walk x `((,x . ,y) (,z . 5) (,y . ,z))))
]

@defproc[(update-s [u any/c?] [v any/c?]) constraint?]{

Safely extends the substitution with a binding of @racket[u] to
@racket[v] when @racket[u] is a @racket[var?].  If neither @racket[u]
nor @racket[v] are variables, @racket[update-s] will fail if @racket[u] and
@racket[v] are not @racket[equal?].

Successfully extending the substitution will trigger any constraints
that reference @racket[u] or @racket[v], a process that will be
described in a later section. }

@examples[
#:eval ck-eval
(run* (q) (update-s q 5))
(run* (q)
  (conde
   [(update-s q 'x)]
   [(update-s q 'y)]))
(define (best-pony pony)
  (update-s pony 'pinkie-pie))
(run* (q) (best-pony q))
(run* (q) (best-pony q) (update-s q 'fluttershy))
] 

The last example fails because @racket[q] cannot be
@racket['pinkie-pie] and @racket['fluttershy] simultaneously.

If you think @racket[(update-s _arg ...)] can get a little wordy, 
you're right!  cKanren ships with a much more expressive
way to update the substitution called @deftech{unification}, which
will be described in an appendix of this guide at some point.

@subsection{Constraint Store}

The @deftech{constraint store} holds constraints stored as
@racket[oc]s.

@defproc[(update-c [oc oc?]) constraint?]{ Adds @racket[oc] to the
constraint store if it contains any unground @racket[var?]s. }

@examples[
#:eval ck-eval
(define (fail-if-ground x)
  (lambdam@ (a : s)
    (let ([x (walk x s)])
      (cond
       [(not (var? x)) #f]
       [else (bindm a (update-c (build-oc fail-if-ground x)))]))))
(run* (q) (fail-if-ground q) prt) ] 

What happens if @racket[q] is ground after a @racket[fail-if-ground]
constraint is placed in the constraint store?  How is our stored
constraint notified that @racket[q] is changed?

@defproc[(run-constraints [x* list?] [ocs list?]) constriant?]{

Runs any constraint in @racket[ocs] that mentions any variable in
@racket[x*].  }

@examples[
#:eval ck-eval
(run* (q)
  (fail-if-ground q)
  prt
  (update-s q 5))
]

Updating the substitution with a new binding will rerun the
@racket[fail-if-ground] @racket[oc] that contains @racket[q].

@defproc[(replace-c [new-c c?]) constraint?]{ Wipes out the existing
constraint store and replaces it with @racket[new-c].  Use with
caution.}

@defproc[(filter/rator [sym symbol?] [c c?]) list?]{ Returns a list of
every @racket[oc] such that @racket[(eq? (oc-rator oc) sym)]. }

@defproc[(filter-not/rator [sym symbol?] [c c?]) list?]{ Returns a list of
every @racket[oc] such that @racket[(not (eq? (oc-rator oc) sym))]. }

@defproc[(filter-memq/rator [symls list?] [c c?]) list?]{ Returns a
list of every @racket[oc] such that @racket[(memq (oc-rator oc)
symls)]. }

@defproc[(filter-not-memq/rator [sym symbol?] [c c?]) list?]{ Returns a list of
every @racket[oc] such that @racket[(not (memq (oc-rator oc) symls))]. }

@subsection{Queue}

The @deftech{queue} is where all lazy goals are stored.  As a
constraint writer or user, you do not have to think about this.

@subsection{Path} The @deftech{path} is a list of the path the package
has taken through the program.  It will be empty until it passes
through a @racket[conde] in @racket[debug] mode.

@defform[(debug expr ...)]{ Turns on debugging (path-tracking) for
condes inside the expression. Any packages printed within will also
display the path they took through the program.  }

@examples[
#:eval ck-eval
(debug
 (run* (q)
   (conde
    [#:name first
     (update-s q 5)
     prt]
    [#:name second
     (update-s q 6)])))
]

The package that is displayed indicates the answer with @racket[q] 
bound to @racket[5] traveled through the @racket[conde] clause named
@racket[first].

