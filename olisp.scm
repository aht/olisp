#!/usr/bin/env plt-r5rs

(define (atom? e)
  (not (pair? e)))

(define (triplet? e)
  (and (pair? e)
       (pair? (cdr e))))

(define call/cc call-with-current-continuation)

(define error-cont (lambda () '()))

(define (error . rest)
  (display "#error: ")
  (for-each (lambda (m) (display m)) rest)
  (error-cont))

(define (l e) (car e))
(define (m e) (cadr e))
(define (r e) (caddr e))
(define (ll e) (l (l e)))
(define (lr e) (l (r e)))
(define (mr e) (m (r e)))
(define (ml e) (m (l e)))
(define (rl e) (r (l e)))
(define (rr e) (r (r e)))

;;; TODO: nullary operator

(define (evaluate e env)
  (if (atom? e)
      (if (symbol? e)
          (lookup e env)
          e)
      (if (eq? (car e) 'quote)
          (cadr e)
          (case (m e)
            ((:) (if (triplet? e)
                     (cons (evaluate (l e) env)
                           (evaluate (r e) env))
                     (error "missing right-hand side in " e)))
            ((:=) (if (triplet? e)
                     (if (exist? (l e) env)
                         (begin
                           (update! env (l e) (evaluate (r e) env))
                           (lookup (l e) env))
                         (begin
                           (set! env.global (extend env (l e) (evaluate (r e) env)))
                           (lookup (l e) env.global)))
                     (error "missing right-hand side in " e)))
            ((then) (if (and (triplet? (r e))
                             (eq? (mr e) 'else))
                        (if (evaluate (l e) env)
                            (evaluate (lr e) env)
                            (evaluate (rr e) env))
                        (cond ((evaluate (l e) env)
                               (evaluate (r e) env)))))
            ((where) (if (triplet? e)
                         (let ((newenv (extend env
                                               (lr e)
                                               'undefined)))
                           (update! newenv (lr e) (evaluate (rr e) newenv))
                           (evaluate (l e) newenv))
                         (error "missing right-hand side in " e)))
            ((->) (if (triplet? e)
                      (if (triplet? (l e))
                          (case (ll e)
                            ((prefix) (mk-prefix (cadr (l e))
                                                 (r e)
                                                 env))
                            ((postfix) (mk-postfix (cadr (l e))
                                                   (r e)
                                                   env))
                            (else (if (eq? (ml e) 'infix)
                                      (mk-infix (cons (ll e) (rl e))
                                                (r e)
                                                env)
                                      (error "bad left-hand side in infix definition " e))))
                          (error "bad left-hand side in operator definition " e))
                      (error "empty body in operator definition " e)))
            (else
              (let ((first (evaluate (l e) env))
                    (second (evaluate (m e) env)))
                (cond ((postfix? second) ((procedure second) first))
                      ((infix? second) ((procedure second) (cons first (evaluate (r e) env))))
                      ((prefix? first) ((procedure first) (evaluate (m e) env)))
                      (#t (list first second (evaluate (cddr e) env))))))))))

(define (exist? name env)
  (if (pair? env)
      (if (eq? (caar env) name)
          #t
          (exist? name (cdr env)))
      #f))

(define (lookup name env)
  (if (pair? env)
      (if (eq? (caar env) name)
          (cdar env)
          (lookup name (cdr env)))
      (error "no such binding: " name)))

(define (update! env name value)
  (if (pair? env)
      (if (eq? (caar env) name)
          (set-cdr! (car env) value)
          (update! (cdr env) name value))
      (error "no such binding: " name)))

(define (extend env names values)
  (if (atom? names)
      (cons (cons names values) env)
      (cons (cons (car names) (car values))
            (extend env (cdr names) (cdr values)))))

(define (mk-prefix parameter body env)
  (cons 'prefix
        (lambda (value)
          (evaluate body (extend env parameter value)))))

(define (mk-infix parameter-pair body env)
  (cons 'infix
        (lambda (value-pair)
          (evaluate body (extend env parameter-pair value-pair)))))

(define (mk-postfix parameter body env)
  (cons 'postfix
        (lambda (value)
          (evaluate body (extend env parameter value)))))

(define (prefix? op)
  (and (pair? op)
       (eq? (car op) 'prefix)
       (procedure? (cdr op))))

(define (infix? op)
  (and (pair? op)
       (eq? (car op) 'infix)
       (procedure? (cdr op))))

(define (postfix? op)
  (and (pair? op)
       (eq? (car op) 'postfix)
       (procedure? (cdr op))))

(define (procedure op)
  (cdr op))

(define env.global '())

(define-syntax definitial
  (syntax-rules ()
    ((_ name value)
     (set! env.global (extend env.global 'name value)))))

(define-syntax defprefix
  (syntax-rules ()
    ((_ name)
     (definitial name (cons 'prefix (lambda (value) (name value)))))))

(defprefix car)
(defprefix cdr)
(defprefix reverse)
(defprefix not)
(defprefix display)
(defprefix newline)

(define-syntax defpostfix
  (syntax-rules ()
    ((_ name)
     (definitial name (cons 'postfix (lambda (value) (name value)))))))

(defpostfix atom?)
(defpostfix pair?)
(defpostfix null?)

(define-syntax definfix
  (syntax-rules ()
    ((_ name)
     (definitial name
       (cons 'infix
             (lambda (pair)
               (apply name (list (car pair) (cdr pair)))))))
    ((_ name native-name)
     (definitial name
       (cons 'infix
             (lambda (pair)
               (apply native-name (list (car pair) (cdr pair)))))))))

(definfix eq?)
(definfix eqv?)
(definfix equal?)
(definfix =)
(definfix >)
(definfix >=)
(definfix <=)
(definfix <)
(definfix +)
(definfix -)
(definfix *)
(definfix ^ expt)
(definfix /)
(definfix ++ append)

(define-syntax evalinitial
  (syntax-rules ()
    ((_ body)
     (begin (call/cc (lambda (cc)
                       (set! error-cont cc)
                       (evaluate body env.global)))))))

(evalinitial '(1+ := ((prefix arg) -> (arg + 1))))

(evalinitial
 '(up := ((f infix arg) -> (proc
                            where
                            (proc := ((start infix stop) -> ((start <= stop)
                                                             then
                                                             ((start : ((start f arg) proc stop))
                                                              else
                                                              '()))))))))

(evalinitial
 '(down := ((f infix arg) -> (proc
                              where
                              (proc := ((start infix stop) -> ((start >= stop)
                                                               then
                                                               ((start : ((start f arg) proc stop))
                                                                else
                                                                '()))))))))

(evalinitial
 '(.. := ((start infix stop) -> ((start <= stop)
                                 then
                                 ((start (+ up 1) stop)
                                  else
                                  (start (- down 1) stop))))))

(evalinitial
 '(onto := ((f infix list) -> ((loop list)
                               where
                               (loop := ((prefix tail) -> ((tail pair?)
                                                           then
                                                           (((f (car tail)) : (loop (cdr tail)))
                                                            else
                                                            '()))))))))

(evalinitial
 '(across := ((f infix list) -> (((cdr list) loop (car list))
                                   where
                                   (loop := ((tail infix acc) -> (((cdr tail) null?)
                                                                  then
                                                                  ((acc f (car tail))
                                                                   else
                                                                   ((cdr tail)
                                                                    loop
                                                                    (acc f (car tail)))))))))))

(define (toplevel)
  (let loop ()
    (display "> ")
    (let ((e (read)))
      (if (not (eof-object? e))
          (begin (call/cc (lambda (cc)
                            (set! error-cont cc)
                            (display (evaluate e env.global))))
                 (newline)
                 (loop))))))

(toplevel)


#|

(2 * (1 + 3))
; ==> 8

(f := ((x infix y) -> (x + (2 * y))))
(2 f 3)
; ==> 8

(cdr (1 : 2))
; ==> 2

((x := (1 .. 5)) x
; ==> (1 2 3 4 5)

(1+ onto x)
; ==> (2 3 4 5 6)

(* across x)
; ==> 120

(1 (+ up 1/2) 5)
(1 3/2 2 5/2 3 7/2 4 9/2 5)

(quote (foo bar))
; ==> (foo bar)

((1 < 0) then (1
               else
               ((1 > 0) then (quote peano!))))
; ==> peano!

(factorial := (f
               where
               (f := ((postfix n) -> ((n = 0) then (1
                                                    else
                                                    (n * ((n - 1) f))))))))

(factorial := ((postfix n) -> (* across (2 .. n))))

(5 factorial)
; ==> 120

|#
