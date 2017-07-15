(load "mk.scm")

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (begin (printf "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
			    'tested-expression expected produced)
		    (exit))))))))

(define default-env
  '((add1 : (int -> int))
    (sub1 : (int -> int))
    (+    : (int -> (int -> int)))
    (-    : (int -> (int -> int)))
    (*    : (int -> (int -> int)))
    (/    : (int -> (int -> int)))
    (mod  : (int -> (int -> int)))
    (not  : (bool -> bool))
    (=    : (int -> (int -> bool)))
    (<    : (int -> (int -> bool)))
    (<=   : (int -> (int -> bool)))
    (>    : (int -> (int -> bool)))
    (>=   : (int -> (int -> bool)))))

(define (!-o gamma expr type)
  (conde
    ((symbolo expr)
     (lookupo gamma expr type))
    ((numbero expr)
     (== 'int type))       
    ((booleo expr)
     (== 'bool type))
    ((fresh (x e T1 T2)
       (== `(lambda (,x) ,e) expr)
       (== `(,T1 -> ,T2) type)
       (symbolo x)
       (!-o `((,x : ,T1) . ,gamma) e T2)))
    ((fresh (f x e e^ s t-ignore)
       (== `(let ((,f ,e)) ,e^) expr)
       (symbolo f)
       (!-o gamma e t-ignore)
       (!-o `((,f poly ,e ,gamma) . ,gamma) e^ type)))
    ((fresh (f x e s e^ T1 T2)
       (== `(let (((,f ,x) ,e)) ,e^) expr) ; let rec syntax
       (symbolo f)
       (symbolo x)
       (!-o `((,f : (,T1 -> ,T2)) (,x : ,T1) . ,gamma) e T2)
       (!-o `((,f poly (lambda (,x) ,e) ((,f : (,T1 -> ,T2)) . ,gamma)) . ,gamma) e^ type)))
    ((fresh (e1 e2 T)
       (== `(,e1 ,e2) expr)
       (!-o gamma e1 `(,T -> ,type))
       (!-o gamma e2 T)))
    ((fresh (e1 e2 T1 T2)
       (== `(cons ,e1 ,e2) expr)
       (== `(pair ,T1 ,T2) type)
       (!-o gamma e1 T1)
       (!-o gamma e2 T2)))
    ((fresh (e T1 T2)
       (== `(car ,e) expr)
       (!-o gamma e `(pair ,T1 ,T2))
       (==  type T1)))
    ((fresh (e T1 T2)
       (== `(cdr ,e) expr)
       (!-o gamma e `(pair ,T1 ,T2))
       (==  type T2)))
    ((fresh (e1 e2 T)
	(== `(eq? ,e1 ,e2) expr)
	(!-o gamma e1 T)
	(!-o gamma e2 T)
	(==  type 'bool)))
    ((fresh (e1 e2 e3)
       (== `(if ,e1 ,e2 ,e3) expr)
       (!-o gamma e1 'bool)
       (!-o gamma e2 type)
       (!-o gamma e3 type)))))

(define (lookupo gamma x t)
  (fresh ()
    (symbolo x)
    (conde
     ((fresh (e gamma^ _)
	(== `((,x poly ,e ,gamma^) . ,_) gamma)
	(!-o gamma^ e t)))
     ((fresh (_)
	(== `((,x : ,t) . ,_) gamma)))                         
      ((fresh (y _ gamma^)
         (== `((,y . ,_) . ,gamma^) gamma)
         (symbolo y)
         (lookupo gamma^ x t))))))

(define-syntax @
  (syntax-rules  ()
    ((@ f) `(f))
    ((@ f x) `(f x))
    ((@ f x . l) (@ (f x) . l))))

(define-syntax lambdas 
  (syntax-rules ()
    ((lambdas (a) c) `(lambda (a) c))
    ((lambdas (a b ...) c) `(lambda (a) ,(lambdas (b ...) c)))))

(define-syntax typeo
  (syntax-rules ()
    ((typeo expr v) (!-o default-env expr v))))

(test "lambdas"
      (run 1 (q) (typeo (lambdas (x y z) 10) q))
      '((_.0 -> (_.1 -> (_.2 -> int)))))

(test "3-args"
      (run 1 (q) (typeo `((lambda (f) ,(@ f 1 2 3)) (lambda (x) (lambda (y) (lambda (z) ,(@ + x ,(@ + y z)))))) q))
      '(int))

; only works for unary

(test "!-rec-1"
  (run 1 (q) (typeo `(let (((f x) ,(@ + 1 (f x)))) f) q))
  '((_.0 -> int)))

(test "!-rec-2"
  (run 1 (q) (typeo `(let (((f x) (f ,(@ + x 1)))) f) q))
  '((int -> _.0)))

(test "!-rec-3"
  (run 1 (q) (typeo `(let (((f x) ,(@ + (f ,(@ + x 1)) 1))) f) q))
  '((int -> int)))

(test "!-rec-4"
      (run 1 (q) (typeo '(let (((f x) x)) (cons (f #t) (f 19))) q))
      '((pair bool int)))

(test "!-1"
  (run 1 (q) (typeo '(lambda (y) y) q))
  '((_.0 -> _.0)))

(test "!-2"
  (run 1 (q) (typeo '((lambda (y) y) (lambda (z) z)) q))
  '((_.0 -> _.0)))

(test "!-3"
  (run 1 (q) (typeo '((lambda (y) y) (lambda (z) (lambda (w) (w z)))) q))
  '((_.0 -> ((_.0 -> _.1) -> _.1))))

(test "!-4"
  (run 1 (q) (typeo '(lambda (y) (y y)) q))
  '())

(test "!-5"
  (run 1 (q) (typeo '5 q))
  '(int))

(test "!-6"
  (run 1 (q) (typeo '#t q))
  '(bool))

(test "!-10"
  (run 1 (q) (typeo '(if #t 3 4) q))
  '(int))

(test "!-pair-1"
  (run 1 (q) (typeo '(cons 3 #t) q))
  '((pair int bool)))

(test "!-pair-4"
  (run 1 (q) (typeo '(cons (cons #f 6) (cons 3 #t)) q))
  '((pair (pair bool int) (pair int bool))))

(test "!-pair-100-let"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f (cons (f 5) (f #t)))) q))
  '((pair int bool)))

(test "!-pair-100-lambda"
  (run 1 (q) (typeo '((lambda (f) (f (cons (f 5) (f #t)))) (lambda (x) x)) q))
  '())

(test "!-12"
  (run 1 (q) (typeo '(let ((x 3)) #t) q))
  '(bool))
  
(test "!-13"
  (run 1 (q) (typeo '(let ((x 3)) x) q))
  '(int))
  
(test "!-14"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f 5)) q))
  '(int))

(test "!-16"
  (run 1 (q) (typeo '(let ((f (lambda (x) (x x)))) 3) q))
  '())
  
(test "!-18"
;;; test from http://okmij.org/ftp/ML/generalization.html
  (run 1 (q) (typeo '(lambda (x) (let ((y (lambda (z) z))) y)) q))
  '((_.0 -> (_.1 -> _.1))))

(test "!-15a"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f 5)) q))
  '(int))

(test "!-15b"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f #t)) q))
  '(bool))

(test "!-15c-pair"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f (cons 5 #t))) q))
  '((pair int bool)))

(test "!-15d-pair"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f (f (cons 5 #t)))) q))
  '((pair int bool)))

  (test "!-15h-let"
    (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f (f 5))) q))
    '(int))

  (test "!-15h-lambda"
    (run 1 (q) (typeo '((lambda (f) (f (f 5))) (lambda (x) x)) q))
    '(int))

  (test "!-15f"
    (run 1 (q) (typeo '(let ((f (lambda (x) x))) (if (f 5) (f 6) (f 7))) q))
    '())

  (test "!-15f2-let"
    (run 1 (q) (typeo '(let ((f (lambda (x) x))) (if (f #t) (f 6) (f 7))) q))
    '(int))

  (test "!-15f2-lambda"
    (run 1 (q) (typeo '((lambda (f) (if (f #t) (f 6) (f 7))) (lambda (x) x)) q))
    '())

  (test "!-15f3-let"
    (run 1 (q) (typeo '(let ((f (lambda (x) x))) (if #t (f 6) (f 7))) q))
    '(int))

  (test "!-15f3-lambda"
    (run 1 (q) (typeo '((lambda (f) (if #t (f 6) (f 7))) (lambda (x) x)) q))
    '(int))

(test "!-15g"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (if (f #t) (f 6) (f 7))) q))
  '(int))

(test "!-15-pair-let"
  (run 1 (q) (typeo '(let ((f (lambda (x) x))) (f (cons (f 5) (f #t)))) q))
  '((pair int bool)))

(test "!-15-pair-lambda"
  (run 1 (q) (typeo '((lambda (f) (f (cons (f 5) (f #t)))) (lambda (x) x)) q))
  '())

(test "!-let-env-1"
  (run 1 (q) (typeo `(let ((x #t)) (let ((f (lambda (a) a))) (let ((y 7)) (let ((x 5)) ,(@ + (f x) (f y)))))) q))
  '(int))

(test "!-let-env-2"
  (run 1 (q) (typeo '(let ((x #t)) (let ((f (lambda (a) a))) (let ((y 7)) (+ (f x) (f y))))) q))
  '())

(test "!-let-env-3"
  (run 1 (q) (typeo `(let ((x 5)) (let ((f (lambda (a) a))) (let ((y 7)) ,(@ + (f x) (f y))))) q))
  '(int))

(test "!-let-env-4"
  (run 1 (q) (typeo `(let ((x 5)) (let ((f (lambda (a) x))) (let ((y #t)) ,(@ + (f x) (f y))))) q))
  '(int))

(test "!-let-env-5"
  (run 1 (q) (typeo '(let ((f 5)) (let ((f f)) f)) q))
  '(int))

(test "!-let-env-6"
  (run 1 (q) (typeo '(let ((x 5)) (let ((f (lambda (x) x))) (f #f))) q))
  '(bool))

(test "!-let-env-7a"
  (run 1 (q) (typeo '(let ((x 5)) (let ((f (lambda (y) x))) (let ((x #t)) (f x)))) q))
  '(int))

(test "!-let-env-7b"
  (run 1 (q) (typeo '((lambda (x) (let ((f (lambda (y) x))) (let ((x #t)) (f x)))) 5) q))
  '(int))

(test "!-let-env-7c"
  (run 1 (q) (typeo '((lambda (x) (let ((f (lambda (y) x))) ((lambda (x) (f x)) #t))) 5) q))
  '(int))

(test "!-let-env-7d"
  (run 1 (q) (typeo '((lambda (x) ((lambda (f) ((lambda (x) (f x)) #t)) (lambda (y) x))) 5) q))
  '(int))


;;; Tests from https://github.com/namin/TAPL-in-miniKanren-cKanren-core.logic/blob/master/clojure-tapl/tapl/test/tapl/test/letpoly.clj  
  (test "!-40"
    (run 1 (q) (typeo '(lambda (x) (lambda (y) (x y))) q))
    '(((_.0 -> _.1) -> (_.0 -> _.1))))

  (test "!-41"
    (run 1 (q) (typeo '(lambda (f) (lambda (a) ((lambda (d) f) (f a)))) q))
    '(((_.0 -> _.1) -> (_.0 -> (_.0 -> _.1)))))

  (test "!-42"
    (run 1 (q) (typeo '(let ((a (lambda (x) x))) a) q))
    '((_.0 -> _.0)))

  (test "!-43"
    (run 1 (q) (typeo '(let ((a (lambda (x) x))) (a a)) q))
    '((_.0 -> _.0)))

  (test "!-44"
    (run 1 (q) (typeo '(lambda (a) (let ((b a)) b)) q))
    '((_.0 -> _.0)))

  (test "!-45"
    (run 1 (q) (typeo '(lambda (f) (lambda (a) (let ((id (lambda (x) x))) ((lambda (d) (id f)) ((id f) (id a)))))) q))
    '(((_.0 -> _.1) -> (_.0 -> (_.0 -> _.1)))))

  (test "!-46"
    (run 1 (q) (typeo '(lambda (f) (lambda (a) (let ((id (lambda (a) a))) ((lambda (d) (id f)) ((id f) (id a)))))) q))
    '(((_.0 -> _.1) -> (_.0 -> (_.0 -> _.1)))))
  
  (test "!-21"
    (run 1 (q) (typeo '(let ((f (lambda (x) x))) f) q))
    '((_.0 -> _.0)))
  
  (test "!-23"
;;; self-application via let polymorphism.  I guess that's a thing???
    (run 1 (q)
      (typeo '(let ((f (lambda (x) 5))) (f f)) q))
    '(int))

  (test "!-23b"
;;; self-application without let poly doesn't type check!
    (run 1 (q)
      (typeo '((lambda (f) (f f)) (lambda (x) 5)) q))
    '())

  (test "!-23c"
    (run 1 (q)
      (typeo '((lambda (x) (x x)) (lambda (x) (x x))) q))
    '())

  (test "!-23d"
;;; self-application via let polymorphism.  I guess that's a thing???    
    (run 1 (q)
      (typeo '(let ((f (lambda (x) x))) (f f)) q))
    '((_.0 -> _.0)))

  (test "!-23e"
;;; self-application without let poly doesn't type check!    
    (run 1 (q)
      (typeo '((lambda (f) (f f)) (lambda (x) x)) q))
    '())

  (test "!-23f"
;;; omega still doesn't typecheck    
    (run 1 (q)
      (typeo '(let ((f (lambda (x) (x x)))) (f f)) q))
    '())
  
  (test "!-23g"
    (run 1 (q)
      (typeo '((lambda (x) (x x)) (lambda (x) (x x))) q))
    '())

  (test "!-23h"
    (run 1 (q)
      (typeo '(let ((f (lambda (x) (x 5)))) (f f)) q))
    '())
  
  
  (test "!-29"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             5)
          q))
    '(int))

  (test "!-30"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               5))
          q))
    '(int))

  (test "!-31"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f1 5)))
          q))
    '(int))

  (test "!-37"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               f1))
          q))
    '((_.0 -> _.0)))
  
  (test "!-36"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               f0))
          q))
    '((_.0 -> _.0)))
  
  (test "!-32"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f0 5)))
          q))
    '(int))

  (test "!-33"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f0 (f1 5))))
          q))
    '(int))

  (test "!-34"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f0 (f0 (f1 (f1 (f0 (f1 (f0 5)))))))))
          q))
    '(int))
  
  (test "!-28"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) f0)))
               5))
          q))
    '(int))
  
  (test "!-27"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 y))))
               5))
          q))
    '(int))
  
  (test "!-26"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               5))
          q))
    '(int))
  
  (test "!-25"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               f1))
          q))
    '((_.0 -> _.0)))

  (test "!-25a"
    (run 1 (q)
      (fresh (lam)
        (== `(let ((f ,lam)) (f (cons (f 5) (f #t)))) q)
        (typeo q '(pair int bool))))
    '(((let ((f (lambda (_.0) _.0))) (f (cons (f 5) (f #t)))) (sym _.0))))

  ; (test "!-25b"
  ;   (run 1 (q)
  ;     (fresh (lam)
  ;       (== `(let ((f ,lam)) (f (cons (f 5) (f #t)))) q)
  ;       (typeo q '(pair int bool))))
  ;   '(((let ((f (lambda (_.0) _.0))) (f (cons (f 5) (f #t))))
  ;      (sym _.0))
  ;     ((let ((f (lambda (_.0) (cons _.1 #f))))
  ;        (f (cons (f 5) (f #t))))
  ;      (num _.1) (sym _.0))
  ;     ((let ((f (lambda (_.0) (let ((_.1 _.2)) _.0))))
  ;        (f (cons (f 5) (f #t))))
  ;      (=/= ((_.0 _.1))) (num _.2) (sym _.0 _.1))
  ;     ((let ((f (lambda (_.0) (let ((_.1 #f)) _.0))))
  ;        (f (cons (f 5) (f #t))))
  ;      (=/= ((_.0 _.1))) (sym _.0 _.1))
  ;     ((let ((f (lambda (_.0) (cons _.1 #t))))
  ;        (f (cons (f 5) (f #t))))
  ;      (num _.1) (sym _.0))
  ;     ((let ((f (lambda (_.0) (let ((_.1 #t)) _.0))))
  ;        (f (cons (f 5) (f #t))))
  ;      (=/= ((_.0 _.1))) (sym _.0 _.1))
  ;     ((let ((f (let ((_.0 _.1)) (lambda (_.2) _.2))))
  ;        (f (cons (f 5) (f #t))))
  ;      (num _.1) (sym _.0 _.2))
  ;     ((let ((f (let ((_.0 #f)) (lambda (_.1) _.1))))
  ;        (f (cons (f 5) (f #t))))
  ;      (sym _.0 _.1))
  ;     ((let ((f (let ((_.0 #t)) (lambda (_.1) _.1))))
  ;        (f (cons (f 5) (f #t))))
  ;      (sym _.0 _.1))
  ;     ((let ((f (lambda (_.0) (let ((_.1 _.0)) _.0))))
  ;        (f (cons (f 5) (f #t))))
  ;      (=/= ((_.0 _.1))) (sym _.0 _.1))))

  (test "!-30a"
    (run 1 (q)
      (typeo '(let ((f0 (lambda (x) (cons x x))))
                 (f0 (lambda (z) z))) q))
    '((pair (_.0 -> _.0) (_.0 -> _.0))))

  (test "!-30b"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) (cons x x))))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (f1 (lambda (z) z))))
          q))
    '((pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))

  (test "!-30c"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) (cons x x))))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (f2 (lambda (z) z)))))
          q))
    '((pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))))

  (test "!-30d"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) (cons x x))))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (f3 (lambda (z) z))))))
          q))
    '((pair (pair (pair (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))) (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))))) (pair (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))) (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))))) (pair (pair (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))) (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))))) (pair (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))) (pair (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))))) (pair (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))) (pair (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0))) (pair (pair (_.0 -> _.0) (_.0 -> _.0)) (pair (_.0 -> _.0) (_.0 -> _.0)))))))))))

;;; This test returns after several minutes, producing an absurdly gigantic type!
#|
(test "!-30e"
  (run 1 (q)
    (typeo
         '(let ((f0 (lambda (x) (cons x x))))
            (let ((f1 (lambda (y) (f0 (f0 y)))))
              (let ((f2 (lambda (y) (f1 (f1 y)))))
                (let ((f3 (lambda (y) (f2 (f2 y)))))
                  (let ((f4 (lambda (y) (f3 (f3 y)))))
                    (f4 (lambda (z) z)))))))
         q))
  '???)
|#

  (test "!-24a"
    (run 1 (q)
      (typeo '(let ((f0 (lambda (x) x)))
                 (f0 (lambda (z) z))) q))
    '((_.0 -> _.0)))

  (test "!-24b"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (f1 (lambda (z) z))))
          q))
    '((_.0 -> _.0)))

  (test "!-24c"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (f2 (lambda (z) z)))))
          q))
    '((_.0 -> _.0)))

  (test "!-24d"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (f3 (lambda (z) z))))))
          q))
    '((_.0 -> _.0)))

#!eof

;; these tests take too long to terminate!

  (test "!-24e"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (let ((f4 (lambda (y) (f3 (f3 y)))))
                     (f4 (lambda (z) z)))))))
          q))
    '((_.0 -> _.0)))  

  (test "!-24f"
    (run 1 (q)
      (typeo
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (let ((f4 (lambda (y) (f3 (f3 y)))))
                     (let ((f5 (lambda (y) (f4 (f4 y)))))
                       (f5 (lambda (z) z))))))))
          q))
'((_.0 -> _.0)))
