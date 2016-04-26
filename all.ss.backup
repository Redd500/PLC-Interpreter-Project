;Author Chi Zhang

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
                               (symbol? (cadar y))
                               (expression? (cadr y))))))
    (bodies (list-of expression?))]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of expression?))]
  [lambda-exp
    (arguments (list-of (lambda (y)
                          (symbol? (cadr y)))))
    (bodies (list-of expression?))]
  [single-lambda-exp
    (argument (lambda (x)
                (symbol? (cadr x))))
    (bodies (list-of expression?))]
  [il-lambda-exp ;improper list
    (arguments (list-of (lambda (x)
                          (symbol? (cadr x)))))
    (more-arguments (lambda (x)
                      (symbol? (cadr x))))
    (bodies (list-of expression?))
    (num-of-args number?)]
  )

	
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
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
         [(equal? 'let (1st datum)) (let-exp (map (lambda (x)
                                                    (list (parse-exp (1st x))
                                                      (parse-exp (2nd x))))
                                               (2nd datum))
                                      (map parse-exp (cddr datum)))]
         [(equal? 'lambda (1st datum)) 
          (cond
            [(symbol? (2nd datum))
             (single-lambda-exp (parse-exp (2nd datum))
               (map parse-exp (cddr datum)))]
            [(and (not (list? (2nd datum)))
                  (pair? (2nd datum)))
             (letrec ((find-vars
                        (lambda (ls)
                          (if (pair? (cdr ls))
                              (list (cons (parse-exp (1st ls))
                                      (1st (find-vars (cdr ls))))
                                (2nd (find-vars (cdr ls))))
                              (list (cons (parse-exp (1st ls)) '()) (parse-exp (cdr ls)))))))
               (let ([args (find-vars (2nd datum))])
                 (il-lambda-exp (1st args)
                   (2nd args)
                   (map parse-exp (cddr datum))
                   (length (1st args)))))]
            [else
              (lambda-exp (map parse-exp (2nd datum))
                (map parse-exp (cddr datum)))])]
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
    (extended-env-record syms vals env)))

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
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env env sym succeed fail)))))))









;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form env)
    ; later we may add things that are not expressions.
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
		          "variable not found in environment: ~s"
			   id)))] 
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
      [let-exp (arguments bodies) (let ([new-env (extend-env (map 2nd (map 1st arguments))
                                                   (map (lambda (x) (eval-exp x env)) (map 2nd arguments))
                                                   env)])
                                      (eval-bodies bodies new-env))]
      [lambda-exp (arguments bodies) (closure (map 2nd arguments)
                                       bodies
                                       env
                                       (length arguments))]
      [single-lambda-exp (argument bodies)
        (closure (list (2nd argument))
          bodies
          env
          0)]
      [il-lambda-exp (arguments more-arguments bodies num-of-args)
        (closure (map 2nd (append arguments (list more-arguments)))
          bodies
          env
          num-of-args)]
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

(define *prim-proc-names* '(+ - * / add1 sub1 zero? not = < > <= >= cons car cdr list null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline caaar caadr caar cadar caddr cadr cdaar cdadr cddar cdddr cddr apply map))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

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
      [else (error 'apply-prim-proc 
            "Wrong primitive procedure: ~s" 
            prim-op)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (pretty-print x) (top-level-eval (parse-exp x) init-env)))









