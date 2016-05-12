;Author Chi Zhang & Nate Briggs

;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?  
  [var-exp        ; variable references
   (id symbol?)]
  [lit-exp        ; "Normal" data.  Did I leave out any types?
  (datum
    (lambda (x)
      (ormap 
        (lambda (pred) (pred x))
        (list number? vector? boolean? symbol? string? pair? null?))))]
  [if-exp
  (test-exp expression?)
  (then-exp expression?)
  (else-exp expression?)]
  [one-if-exp
  (test-exp expression?)
  (then-exp expression?)]
  [let-exp
    (arguments (list-of (lambda (y)
                          (and (pair? y)
                               (= 2 (length y))
                               (symbol? (1st y))
                               (expression? (2nd y))))))
    (bodies (list-of expression?))]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of expression?))]
  [lambda-exp
    (arguments (list-of symbol?))
    (bodies (list-of expression?))]
  [single-lambda-exp
    (argument symbol?)
    (bodies (list-of expression?))]
  [il-lambda-exp ;improper list
    (arguments (list-of symbol?))
    (more-arguments symbol?)
    (bodies (list-of expression?))
    (num-of-args number?)]
  [cond-exp
    (test-exp expression?)
    (then-exp (list-of expression?))
    (next-cond-exp expression?)]
  [and-exp
    (exps (list-of expression?))]
  [or-exp
    (exps (list-of expression?))]
  [case-exp
    (test-exp expression?)
    (ans-exp (list-of expression?))
    (then-exp (list-of expression?))
    (next-case-exp expression?)]
  [begin-exp
    (exps (list-of expression?))]
  [while-exp
    (test-exp expression?)
    (bodies (list-of expression?))]
  [named-let-exp
    (name symbol?)
    (arguments (list-of (lambda (y)
                          (and (pair? y)
                               (= 2 (length y))
                               (symbol? (1st y))
                               (expression? (2nd y))))))
    (bodies (list-of expression?))]
  [letrec-exp
    (proc-names (list-of symbol?))
    (idss (list-of (list-of symbol?)))
    (bodies (list-of expression?))
    (letrec-body (list-of expression?))]
  [set!-exp
    (var symbol?)
    (value expression?)]
  [define-exp
    (var symbol?)
    (value expression?)])

	
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of box?))
   (env environment?))
  (recursively-extended-env-record
    (proc-names (list-of symbol?))
    (idss (list-of (list-of symbol?)))
    (bodies (list-of expression?))
    (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
    (vars (list-of symbol?))
    (code (list-of scheme-value?))
    (env environment?)
    (num-of-args number?)])
	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(or (number? datum)
           (boolean? datum)
           (string? datum)
           (null? datum)
           (vector? datum))
       (lit-exp datum)]
      [(and (pair? datum)
            (equal? (1st datum) 'quote))
      (lit-exp (2nd datum))]
      [(pair? datum)
       (cond
         [(equal? 'if (1st datum))
         (cond
         	[(eq? 4 (length datum)) (if-exp (parse-exp (2nd datum))
                                     (parse-exp (3rd datum))
                                     (parse-exp (3rd (cdr datum))))]
         	[else (one-if-exp (parse-exp (2nd datum))
         			(parse-exp (3rd datum)))])]
         [(equal? 'let (1st datum)) 
          (cond
            [(list? (2nd datum))
             (let-exp (map (lambda (x)
                             (list (1st x)
                               (parse-exp (2nd x))))
                        (2nd datum))
               (map parse-exp (cddr datum)))]
            [else
              (named-let-exp (2nd datum)
                (map (lambda (x)
                       (list (1st x)
                         (parse-exp (2nd x))))
                  (3rd datum))
                (map parse-exp (cdddr datum)))])]
         [(equal? 'lambda (1st datum)) 
          (cond
            [(symbol? (2nd datum))
             (single-lambda-exp (2nd datum)
               (map parse-exp (cddr datum)))]
            [(and (not (list? (2nd datum)))
                  (pair? (2nd datum)))
             (letrec ((find-vars
                        (lambda (ls)
                          (if (pair? (cdr ls))
                              (list (cons (1st ls)
                                      (1st (find-vars (cdr ls))))
                                (2nd (find-vars (cdr ls))))
                              (list (cons (1st ls) '()) (cdr ls))))))
               (let ([args (find-vars (2nd datum))])
                 (il-lambda-exp (1st args)
                   (2nd args)
                   (map parse-exp (cddr datum))
                   (length (1st args)))))]
            [else
              (lambda-exp (2nd datum)
                (map parse-exp (cddr datum)))])]
         [(equal? 'begin (1st datum))
          (begin-exp (map parse-exp (cdr datum)))]
         [(equal? 'cond (1st datum))
          (letrec ((create-cond-exp
                     (lambda (exp)
                       (if (equal? 'else (caar exp))
                           (begin-exp (map parse-exp (cdar exp)))
                           (cond-exp (parse-exp (caar exp))
                             (map parse-exp (cdar exp))
                             (create-cond-exp (cdr exp)))))))
            (create-cond-exp (cdr datum)))]
         [(equal? 'and (1st datum))
          (and-exp (map parse-exp (cdr datum)))]
         [(equal? 'or (1st datum))
          (or-exp (map parse-exp (cdr datum)))]
         [(equal? 'case (1st datum))
          (let ((test (parse-exp (2nd datum))))
            (letrec ((create-case-exp
                       (lambda (exp)
                         (if (equal? 'else (caar exp))
                             (begin-exp (map parse-exp (cdar exp)))
                             (case-exp test
                               (map parse-exp (caar exp))
                               (map parse-exp (cdar exp))
                               (create-case-exp (cdr exp)))))))
              (create-case-exp (cddr datum))))]
         [(equal? 'let* (1st datum))
          (letrec ((create-let-exp
                     (lambda (exp)
                       (if (null? exp)
                           (map parse-exp (cddr datum))
                           (let-exp (list (caar exp)
                                      (parse-exp (cadar exp)))
                             (create-let-exp (cdr exp)))))))
            (create-let-exp (2nd datum)))]
         [(equal? 'letrec (1st datum))
          (letrec-exp (map 1st (2nd datum))
            (map 2nd (map 2nd (2nd datum)))
            (map (lambda (x)
                   (parse-exp (3rd x))) (map 2nd (2nd datum)))
            (map parse-exp (cddr datum)))]
          [(equal? 'while (1st datum))
            (while-exp (parse-exp (2nd datum))
                        (map parse-exp (cddr datum)))]
          [(equal? 'set! (1st datum))
            (set!-exp (2nd datum)
                      (parse-exp (3rd datum)))]
          [(equal? 'define (1st datum))
            (define-exp (2nd datum)
                        (parse-exp (3rd datum)))]
         [else (app-exp (parse-exp (1st datum))
                 (map parse-exp (cdr datum)))])]

       [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))








;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map box vals) env)))

(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (recursively-extended-env-record
      proc-names idss bodies old-env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (deref (apply-env-ref env sym succeed fail))))

(define apply-env-ref
  (lambda (env var succeed fail)
    (if (equal? global-env env)
      (cases environment env
        (extended-env-record (syms vals env)
          (let ((pos (list-find-position var syms)))
            (if (number? pos)
              (succeed (list-ref vals pos))
              (fail))))
        (else
          (eopl:error 'apply-env-ref "you should not see this message!")))
      (cases environment env
        (empty-env-record ()
         (apply-env-ref global-env var succeed fail))
        (extended-env-record (syms vals env)
          (let ((pos (list-find-position var syms)))
            (if (number? pos)
              (succeed (list-ref vals pos))
              (apply-env-ref env var succeed fail))))
        (recursively-extended-env-record
          (proc-names idss bodies old-env)
          (let ([pos (list-find-position var proc-names)])
            (if (number? pos)
                (closure (list-ref idss pos)
                  (list (list-ref bodies pos))
                  env
                  (+ 1 (length idss)))
                (apply-env-ref old-env var succeed fail))))))))

(define deref
  (lambda (ref)
    (if (box? ref)
     (unbox ref)
     ref)))

(define set!-ref
  (lambda (ref value)
    (if (box? ref)
      (set-box! ref value)
      (eopl:error 'set!-ref "ref is not a box: ~a" ref))))





;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [let-exp (arguments bodies)
        (app-exp (lambda-exp (map 1st arguments) (map syntax-expand bodies))
          (map 2nd arguments))]
      [letrec-exp (proc-names idss bodies letrec-body)
        (letrec-exp proc-names idss (map syntax-expand bodies) (map syntax-expand letrec-body))]
      [named-let-exp (name arguments bodies)
        (syntax-expand (letrec-exp (list name) (list (map 1st arguments)) bodies (list (app-exp (var-exp name) (map 2nd arguments)))))]
      [lambda-exp (arguments bodies)
        (lambda-exp arguments (map syntax-expand bodies))]
      [var-exp (id)
        exp]
      [lit-exp (datum)
        exp]
      [if-exp (test-exp then-exp else-exp)
        (if-exp (syntax-expand test-exp)
          (syntax-expand then-exp)
          (syntax-expand else-exp))]
      [one-if-exp (test-exp then-exp)
        (one-if-exp (syntax-expand test-exp)
          (syntax-expand then-exp))]
      [app-exp (rator rands)
        (app-exp (syntax-expand rator)
          (map syntax-expand rands))]
      [single-lambda-exp (argument bodies)
        (single-lambda-exp argument
          (map syntax-expand bodies))]
      [il-lambda-exp (arguments more-arguments bodies num-of-args)
        (il-lambda-exp arguments
          more-arguments
          (map syntax-expand bodies)
          num-of-args)]
      [cond-exp (test-exp then-exp next-cond-exp)
        (cond-exp (syntax-expand test-exp)
          (map syntax-expand then-exp)
          (syntax-expand next-cond-exp))]
      [and-exp (exps)
        (and-exp (map syntax-expand exps))]
      [or-exp (exps)
        (or-exp (map syntax-expand exps))]
      [case-exp (test-exp ans-exp then-exp next-case-exp)
        (case-exp (syntax-expand test-exp)
          (map syntax-expand ans-exp)
          (map syntax-expand then-exp)
          (syntax-expand next-case-exp))]
      [begin-exp (exps)
        (begin-exp (map syntax-expand exps))]
      [while-exp (test-exp bodies)
        (while-exp (syntax-expand test-exp)
          (map syntax-expand bodies))]
      [set!-exp (var value)
        (set!-exp var (syntax-expand value))]
      [define-exp (var value)
        (define-exp var (syntax-expand value))])))









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form env)
    (eval-exp form env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
				(apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if id is in the environment 
           (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
		          "variable not found in environment: ~s" id)))] 
      [app-exp (rator rands)
      (let ([proc-value (eval-exp rator env)]
            [args (eval-rands rands env)])
      (apply-proc proc-value args))]
      [if-exp (test-exp then-exp else-exp) (if (eval-exp test-exp env)
                                              (eval-exp then-exp env)
                                              (eval-exp else-exp env))]
      [one-if-exp (test-exp then-exp)
      (if (eval-exp test-exp env)
      	(eval-exp then-exp env))]
      [lambda-exp (arguments bodies) (closure arguments
                                       bodies
                                       env
                                       (length arguments))]
      [single-lambda-exp (argument bodies)
        (closure (list argument)
          bodies
          env
          0)]
      [il-lambda-exp (arguments more-arguments bodies num-of-args)
        (closure (append arguments (list more-arguments))
          bodies
          env
          num-of-args)]
      [cond-exp (test-exp then-exp next-cond-exp)
        (if (eval-exp test-exp env)
            (let ((evals (map (lambda (x)
                                (eval-exp x env)) then-exp)))
              (list-ref evals (- (length evals) 1)))
            (eval-exp next-cond-exp env))]
      [and-exp (exps)
        (letrec ((eval-and
                   (lambda (ls)
                     (if (null? (cdr ls))
                         (if (car ls)
                             (car ls)
                             #f)
                         (if (car ls)
                             (eval-and (cdr ls))
                             #f)))))
          (eval-and (map (lambda (x)
                           (eval-exp x env)) exps)))]
      [or-exp (exps)
        (letrec ((eval-or
                   (lambda (ls)
                     (if (null? ls)
                         #f
                         (if (car ls)
                             (car ls)
                             (eval-or (cdr ls)))))))
          (eval-or (map (lambda (x)
                           (eval-exp x env)) exps)))]
      [case-exp (test-exp ans-exp then-exp next-case-exp)
        (if (member (eval-exp test-exp env) (map (lambda (x)
                                                   (eval-exp x env)) ans-exp))
            (letrec ((good-map
                       (lambda (ls ret)
                         (if (null? ls)
                             ret
                             (good-map (cdr ls) (eval-exp (car ls) env))))))
              (good-map then-exp 0))
            (eval-exp next-case-exp env))]
      [begin-exp (exps)
        (letrec ((good-map
                   (lambda (ls ret)
                     (if (null? ls)
                         ret
                         (good-map (cdr ls) (eval-exp (car ls) env))))))
          (good-map exps 0))]
      [while-exp (test-exp bodies)
        (letrec ([while-loop (lambda ()
                                (cond
                                  [(eval-exp test-exp env) (eval-bodies bodies env) (while-loop)]
                                  [else #f]))])
          (while-loop))]
      [letrec-exp (proc-names idss bodies letrec-body)
        (eval-bodies letrec-body (extend-env-recursively proc-names idss bodies env))]
      [set!-exp (var value)
        (set!-ref
          (apply-env-ref env var (lambda (x) x) (lambda () (eopl:error 'set! "You shouldn't see this: ~a" exp)))
          (eval-exp value env))]
      [define-exp (var value)
        (apply-env-ref global-env var (lambda (x) (set!-ref x (eval-exp value global-env)))
                                      (lambda () (set! global-env (extend-env
                                                  (cons var (2nd global-env))
                                                  (cons (eval-exp value global-env) (map deref (3rd global-env)))
                                                  (empty-env)))))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list



(define eval-bodies
  (lambda (body env)
    (cond 
      [(null? body)
       (eopl:error 'eval-exp "let and lambda expressions need a body!")]
      [(null? (cdr body))
       (eval-exp (1st body) env)]
      [else
        (eval-exp (1st body) env)
        (eval-bodies (cdr body) env)])))      
        
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (vars code env num-of-args)
        (letrec ((new-args-creator
                   (lambda (ls num)
                     (if (null? ls)
                         ls
                         (if (= num 0)
                             (list ls)
                             (cons (car ls) (new-args-creator (cdr ls) (- num 1))))))))
          (let ([new-env (extend-env vars (new-args-creator args num-of-args) env)])
            (eval-bodies code new-env)))]
           			; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(eqv? append list-tail quotient + - * / add1 sub1 zero? not = < > <= >= cons car cdr list null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline caaar caadr caar cadar caddr cadr cdaar cdadr cddar cdddr cddr apply map))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

(define global-env
  (extend-env            
     *prim-proc-names*   
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))


(define reset-global-env
  (lambda ()
    (set! global-env (extend-env            
     *prim-proc-names*   
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))))


; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
       [(cadar) (car (cdr (car (1st args))))]
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(=) (= (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(cons) (cons (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) (apply list args)]
      [(null?) (null? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (apply eq? args)]
      [(equal?) (apply equal? args)]
      [(atom?) (atom? (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(list?) (apply list? args)]
      [(pair?) (pair? args)]
      [(procedure?) (proc-val? (car args))]
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)]
      [(make-vector) (make-vector (1st args) (2nd args))];later
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (apply vector? args)]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display args)];later
      [(newline) (newline)];later
      [(map) (map (lambda (x) (apply-proc (1st args) (list x))) (cadr args))]
      [(apply) (apply (lambda x (apply-proc (1st args) x)) (cadr args))]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cddr) (cddr (1st args))]
      [(cdar) (cdar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cddar) (cddar (1st args))]
      [(caadr) (caadr (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(cadar) (cadar (1st args))]
      [(caaar) (caaar (1st args))]
      [(cdddr) (cdddr (1st args))]
      [(quotient) (quotient (1st args) (2nd args))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [(append) (append (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
            "Wrong primitive procedure: ~s" 
            prim-op)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))) init-env)])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x)
    (top-level-eval
      (syntax-expand (parse-exp x)) init-env)))









