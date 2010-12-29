;;; -*- mode: clojure; coding: utf-8 -*-
;;;
;;;            Loops — Common Lisp Iterate macro for Clojure
;;;
;;;                 Copyright 1989 by Jonathan Amsterdam
;;;         Adapted to ANSI Common Lisp in 2003 by Andreas Fuchs
;;;         Adapted to Clojure in 2010 by Roman Zaharov @zahardzhan <zahardzhan@gmail.com>
;;;
;;; Permission to use, copy, modify, and distribute this software and its
;;; documentation for any purpose and without fee is hereby granted,
;;; provided that this copyright and permission notice appear in all
;;; copies and supporting documentation, and that the name of M.I.T. not
;;; be used in advertising or publicity pertaining to distribution of the
;;; software without specific, written prior permission. M.I.T. makes no
;;; representations about the suitability of this software for any
;;; purpose.  It is provided "as is" without express or implied warranty.

;;; M.I.T. DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE, INCLUDING
;;; ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS, IN NO EVENT SHALL
;;; M.I.T. BE LIABLE FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR
;;; ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS,
;;; WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION,
;;; ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS
;;; SOFTWARE.
;;;
;;; FIXES:
;;; (v. 1.2-ansi)
;;;  2004-11-30 - Joerg Hoehle: a dozen small fixes to various functions
;;;  2003-12-16 - Tested a bit more, implemented FOR-HASHTABLE and
;;;               FOR-PACKAGES (FOR-PACKAGE) iteration CLtS-style
;;;               using (with-{package,hashtable}-iterator)
;;;  2003-12-16 - ported iterate-1.2 to ANSI Common Lisp (in the form
;;;               of SBCL). Extremely untested. Works for simple
;;;               examples, though.
;;; (v. 1.2)
;;;  6/14/91  - fixed generation of previous code
;;;  5/6/91   - improved code generated for COLLECT and ADJOINING
;;;  4/10/91  - added *binding-context?* to correctly determine when inside
;;;	        a binding context
;;;  12/20/90 - fixed ,. bug in IN-HASHTABLE
;;;  3/3/91 - no longer generates loop-end and loop-step tags if they're not
;;;           used, to avoid compiler warnings from some compilers (Allegro)
;;;  3/4/91 - treat cond as a special form for allegro
;;;  (v. 1.1.1)
;;;
;;;
;;; OUTSTANDING PROBLEMS & QUESTIONS:
;;; - What happens if there are two contradictory declarations 
;;;   about a variable's type?  We just take the second one. CLM 
;;;   doesn't say, but presumably this is an error. Let's say it is.
;;;
;;; - Is there a more general way to do synonyms that still allows
;;;   some specificity to particular clauses?  Right now, all we allow
;;;   is for the first words of clauses to have synonyms.
;;;
;;; - We should look at function type declarations, at least at the
;;;   result type, and record them.
;;;
;;; - Consider adding an if-never keyword to find...max/min
;;;
;;; - Consider allowing accumulation variables to be generalized
;;;   variables, acceptable to setf.
;;;
;;; - Consider parsing type declarations of the form (vector * integer),
;;;   to generate types for internal variables.
;;;
;;; - Vector destructuring?
;;;
;;;
;;; TODO: 
;;;  - do I walk &optional and &key code in lambda-lists?
;;;  - try binding *macroexpand-hook* in walk
;;;  - track down PREVIOUS bug in Symbolics and sparc lucid
;;;
;;;  - reducing and accum: RESULT-TYPE
;;;  - rethink types 
;;;  - how to type result var?
;;;  - (for var concatenate (from 1 to 10) (in '(a b c)) (next (gensym)))
;;;  -       (if (< var 10) 
;;;		 (next [from-to])
;;;		 (if lst
;;;		     (next [in])
;;;		     (gensym)))
;;;  - for var choose, for var repeatedly
;;;
;;; For CL version 2:
;;;  - variable info from environments
;;;  - macro info     "     " (so we can support macrolet)
;;;  - use errors for EOF
;;;  - change WALK and FREE-VARIABLES to take symbol macros into account
;;;  - array indices are fixnums
;;;  - type REAL for extremum clauses
;;;
;;; Maybe:
;;;  - decls can appear not at top level, as long as they appear before use.
;;;  - extremum and find-extremum should do reductions when possible
;;;  - optimize collections, hashtables, packages for lispms 
;;;  - fix :using-type-of to check for supplied ???
;;;  - for-in should allow numerical keywords (from, to, etc.)...?
;;;
;;;
;;; TO TEST: 
;;;  - leaving driver code where it is
;;;  - typing
;;;  - macroexpand & walk after-each
;;;  - check for duplicate keywords in defclause, defmacro-clause

(ns loops
  (:use [clojure.walk :only [macroexpand-all]]
        [clojure.contrib.def :only [defvar]]
        [clojure.set :only [union difference]])
  (:require clojure.walk))

(declare walk-next walk-nnext walk-do)

(defvar special-forms*
  '{ ;; def var loop recur throw try monitor-enter monitor-exit
    eval walk-nnext
    fn* walk-fn
    if walk-next
    let* walk-let
    do walk-do
    quote nil
    ;; load-time-value nil
    ;; locally walk-cdr-with-declarations
    ;; labels walk-flet
    ;; return-from walk-cddr
    ;; throw walk-cdr 
    ;; catch walk-cdr

    ;; Finally some cases where code compiled from the macroexpansion
    ;; may not be as good as code compiled from the original form:
    ;; -- and iterates own expansion becomes more readable
    ;; and walk-cdr
    ;; or walk-cdr
    }
  "An alist of lisp special forms and the functions for handling them.
   nil as function means leave form as-is.")

(defn special-form? [form]
  (boolean (find special-forms* form)))

(defn symbol-name [s]
  (symbol (name s)))

(defn symbolize
  "Remove namespace prefixes from symbols in the tree."
  [form]
  (clojure.walk/walk (fn [item] (cond (symbol? item) (symbol-name item)
                                     (seq? item) (symbolize item)
                                     :else item))
                     identity form))

(defn macro? [sym]
  (boolean (:macro (meta (resolve sym)))))

(defn clause-error [& message]
  (throw (new Exception (apply str message))))

(defn genvar
  "Something like gensym."
  ([] (gensym (str "auto__")))
  ([name]
     (gensym (str name "__auto__"))))

(defmacro with-return [expr & body]
  `(do (do ~@body)
       ~expr))

(defmacro let-return [[form val] & body]
  `(let [~form ~val]
     (with-return ~form
       (do ~@body))))

(defvar *result-var* nil
  "*result-var* is bound to a gensym before the clauses of an iterate
   form are processed.  In the generated code, the gensym is bound to
   nil before any other bindings are performed.  Clauses are free to
   generate code that sets the value of *result-var*.")

(defvar clause* nil
  "*clause* is bound to each entire iterate clause before the clause
   is processed.  Mostly for error output (see clause-error).")

(defvar clauses*)

(defvar bindings* nil
  "For the use of make-binding-internal, to pass back bindings.
   if-1st-time also uses it to create first-time variables.")

(defvar binding-context?* false
  "binding-context?* a misnomer, should be named *declaration-context*, is
   bound to T inside a form that allows declarations (flet, labels).  We used
   to just see if *internal-variables* was non-nil, but that's wrong--you can
   be inside a binding context that binds no variables.")

(defvar internal-variables* #{}
  "This is a list of variable-lists containing the variables made by
   internal let's or other binding forms.  It is used to check for
   the error of having iterate try to bind one of these variables at
   top-level.  E.g.
   (iterate (for i from 1 to 10)
            (let ((a nil))
              (collect i into a)))
   is an error.")

(defvar *accum-var-alist* nil
  "This is how we get multiple accumulations into the same variable to
   come out right.  See make-accum-var-binding.  It's an alist
   of (accum-var kind <possibly other info>).  The currently used
   kinds are:
   :collect     for collect, nconc, append, etc.
   :increment   for count, sum and multiply
   :max         for maximize
   :min         for minimize
   :if-exists   for always/never/thereis and finding such-that
   Note that we do not check for type conflict in the re-use of these
   variables.")

(defvar *block-name* nil
  "Name of the block for this iterate form.  Used in generating
   return statements.")

(defvar loop-step-used?* false)

(defvar loop-stop-used?* false)

(defvar top-level?* false
  "*top-level?* is bound to T at top-level (i.e. before any forms that
   contain clauses inside them, like IF, LET, etc.) and to NIL inside
   such forms.  It is useful to ensure that certain forms
   (particularly iteration drivers) occur only at top-level.")

(defvar walk)

(defvar code*
  {:init ()
   :body ()
   :step ()
   :stop ()})

(defn top-level-check []
  (when-not @top-level?*
    (clause-error "Clause can occur only at top-level")))

(defn alter-var [var fun & args]
  (var-set var (apply fun @var args)))

(defn internal-variable? [var]
  (contains? internal-variables* var))

(defn check-internal-variables [var]
  (when (internal-variable? var)
    (clause-error "The variable " var ", which Iterate would like to
     bind, already has a binding in a context internal to the iterate
     form.  Give the variable another name.")))

(defn var-binding [var]
  (when-let [bind (find @bindings* var)]
    (key bind)))

(defn add-binding [var value]
  (cond (var-binding var) (clause-error "Duplicate variable: " var)
        :else (do (check-internal-variables var)
                  (swap! bindings* assoc var value))))

(defn make-binding-internal
  "This returns true if it actually created a binding, else false."
  [var value]
  (cond (nil? var) false
        (not (symbol? var)) (clause-error "The variable " var " is not a symbol")
        :else (with-return true
                (add-binding var value))))

(defn make-binding
  "This creates a binding of VAR to VALUE."
  [var value]
  (make-binding-internal var value))

(defn make-default-binding
  "This makes a random binding of VAR (i.e. you should not depend on
  the binding's value)."
  [var]
  (make-binding-internal var nil))

(defn make-var-and-binding [name value]
  (let-return [var (genvar name)]
    (make-binding-internal var value)))

(defn make-var-and-default-binding [name]
  (let-return [var (genvar name)]
    (make-binding-internal var nil)))

(defvar return-code hash-map)

(defn return-code-modifying-body [fun stuff body-modify-fun]
  (let [code (fun stuff)]
    (update-in code [:body] body-modify-fun)))

(defmacro with-loops [& body]
  (list 'binding '[bindings* (atom {})
                   internal-variables* #{}
                   binding-context?* false
                   clause* nil
                   loop-step-used?* (atom false)
                   loop-stop-used?* (atom false)
                   top-level?* true]
        `(do ~@body)))

(defmacro loops [& body]
  `(with-loops
     (walk ~body)))

(defn starts-clause? [symbol]
  (or (some #(= symbol (first (:pattern %))) @clauses*)
      (= symbol 'generate)))

(defn clause? [form] ;; is-iterate-clause?
  (and (seq? form)
       (symbol? (first form))
       (starts-clause? (first form))))

(defn doify ;; prognify
  "If more than one form, and the first is a list, then insert a PROGN.
  Be careful to not copy forms."
  [forms]
  (if (seq (rest forms))
    (if (and (list? (first forms))
             (not= (first forms) 'fn*))
      (conj forms 'do)
      forms)
    (first forms)))

(defn function?
  "Form is valid fn* declaration: (fn* name? ([bindings] forms*)*)"
  [[fn** & fspecs :as form]]
  (and (seq form)
       (= fn** 'fn*)
       (or (not (seq fspecs))
           (and (symbol? (first fspecs))
                (every? seq (rest fspecs)))
           (every? seq fspecs))))

(def clauses*
     (atom
      [{:pattern '(repeat n)
        :context (fn [n]
                   (and (true? @top-level?*) (integer? n)))
        :walker  (fn [n]
                   (top-level-check)
                   (let [count-var (make-var-and-default-binding 'count)]
                     (reset! loop-stop-used?* true)
                     (return-code :init `((var-set ~count-var ~n))
                                  :body `((if (<= @~count-var 0) (recur :stop)))
                                  :step `((var-set ~count-var (dec @~count-var))))))}]))

(declare walk-arglist walk-special-form walk-fspec process-clause)

(defn walk [form]
  (cond (not (seq? form))
        (return-code :body (list form))

        (symbol? (first form))
        (cond (special-form? (first form)) ;; handle special operators that any code walker must recognize
              (walk-special-form form)

              (starts-clause? (first form)) ;; recognize clauses.
              (process-clause form)

              (macro? (first form)) ;; expand macros
              (walk (symbolize (macroexpand-all form)))

              :function-call
              (return-code-modifying-body walk-arglist (rest form) #(list (conj %1 (first form)))))

        (function? (first form)) ;; function call with a fn* as first symbol
        (let [fn-code (walk (first form))
              args-code (walk-arglist (rest form))]
          (assoc (merge-with concat (dissoc fn-code :body) (dissoc args-code :body))
            :body (list (conj (:body args-code) (:body fn-code)))))

        ;; TODO: must walk fn-bodies like ((x))
        :else (clause-error "The form " form " is not a valid Lisp expression.")))

(defn walk-list-conjoining
  ([lst walker] (walk-list-conjoining lst walker #(do %2)))
  ([lst walker body-during]
     (loop [forms lst, codes code*]
       (if-not (seq forms) codes
               (let [form (first forms)
                     code (walker form)
                     body (:body code)
                     code-with-updated-body (assoc code :body (body-during form body))]
                 (recur (rest forms) (merge-with concat codes code)))))))

(defn walk-list [forms]
  (walk-list-conjoining forms walk))

(defn walk-arglist [args]
  (binding [top-level?* false]
    (walk-list-conjoining args walk #(if (clause? %1) (list (doify %2)) %2))))

(defn add-internal-var
  "VAR can be a symbol or a list (symbol ...)."
  [var]
  (conj internal-variables* (if (seq? var) (first var) var)))

(defn lambda-list-vars
  "Return the variables in the lambda list of fn* form, omitting & symbol."
  [lambda-list]
  (remove (partial = '&) lambda-list))

(defn add-internal-vars ;; TODO: list of LET bindings
  "VARS could be a lambda-list, a list of LET bindings, or just a list of
  variables; all will work"
  [vars]
  (union internal-variables* (set (lambda-list-vars vars))))

(defn walk-fsign [[args & forms]]
  (binding [top-level?* false
            binding-context?* true
            internal-variables* (add-internal-vars args)]
    (let [{:as code :keys [body init step stop]} (walk-list forms)]
      (return-code :body `((~args ~@body)) :init init :step step :stop stop))))

(defn walk-fspec ;; TODO: walk all fspecs, not first one
  "Works for lambdas and function specs in flet and labels.
  FORM = (name? ([args] & body)*)
  We only walk at the body.  The args are set up as internal variables.
  Declarations are kept internal to the body."
  [[head & tail :as form]]
  (if-not (seq form) (return-code :body ())
          (if (symbol? head) ;; if head is function name
            (binding [internal-variables* (add-internal-var head)]
              (return-code-modifying-body identity (walk-list-conjoining tail walk-fsign)
                                          #(conj %1 head)))
            (walk-list-conjoining (apply list head tail) walk-fsign))))

(defn walk-special-form
  [form]
  (binding [clause* form]
    (let [walker (get special-forms* (first form))]
      (if-not walker (return-code :body (list form))
              (apply @(resolve walker) ; get function by it's symbol name
                     form)))))

(defn walk-next ;; walk-cdr in original
  "This is for anything where only the car isn't to be walked."
  [head & tail]
  (return-code-modifying-body walk-arglist tail #(list (conj %1 head))))

(defn walk-nnext ;; walk-cddr in original
  "This is for anything where the first two elements aren't to be walked."
  [head neck & tail]
  (return-code-modifying-body walk-arglist tail #(list (conj %1 neck head))))

(defn walk-do
  "The only difference between this and walk-next is that top-level* is not
  bound.  This is so macros can return DOs of things.  It's exactly like
  the definition of \"top-level\" in lisp. 
  (Also, just for looks, this returns nil if the do is empty.)"
  [do* & stuff]
  (return-code-modifying-body walk-list stuff
                              #(if-not (seq %1) ()
                                       (list (conj %1 do*)))))

(defn walk-fn [fn** & fspec]
  (return-code-modifying-body walk-fspec fspec #(list (conj %1 fn**))))


(defn walk-let-binding [name form]
  (let [{:as code :keys [body init step stop]} (walk form)]
    (return-code :body (list name (doify body))
                 :init init :step step :stop stop)))

(defn walk-let-bindings [[name form :as bindings]]
  (if-not (seq bindings) (return-code :body ())
          (let [binding-code (walk-let-binding name form)]
            (binding [internal-variables* (add-internal-var name)]
              (let [bindings-code (walk-let-bindings (nnext bindings))]
                (assoc (merge-with concat (dissoc binding-code :body) (dissoc bindings-code :body))
                  :body (conj (:body bindings-code)
                              (second (:body binding-code))
                              (first (:body binding-code)))))))))

(defn walk-let
  "The bindings or body may contain iterate clauses.
  Important: the decls go inside this let, not at top-level.
  It is an error to use a variable in the let bindings as the
  target of an accumulation (i.e. INTO), because iterate will try
  to make a top-level binding for that variable.  The same goes for
  other variables that might be so bound."
  [let** bindings & body]
  (binding [top-level?* false]
    (let [bindings-code (walk-let-bindings bindings)]
      (binding [binding-context?* true
                internal-variables* (add-internal-vars (map first (partition 2 (:body bindings-code))))]
        (let [body-code (walk-list body)]
          (return-code :body (list `(~let** ~(apply vector (:body bindings-code)) ~@(:body body-code)))
                       :init (concat (:init bindings-code) (:init body-code))
                       :step (concat (:step bindings-code) (:step body-code))
                       :stop (concat (:stop bindings-code) (:stop body-code))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

(comment
  (with-loops (walk '(fn f [head & tail]
                       {:pre (number? head)}
                       (let [sqr (* head head)]
                         (list sqr tail)))))
(with-loops (walk-fspec (rest (macroexpand-all '(fn )))))
(with-loops (walk-fspec (rest (macroexpand-all '(fn ([i] i) ([i j & [ks]] i j))))))
(with-loops (walk-fspec (rest (macroexpand-all '(fn f ([i] i) ([i j & [ks]] i j))))))
)
