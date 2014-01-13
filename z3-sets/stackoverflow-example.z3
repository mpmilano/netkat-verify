;simple function, equivalent to or
(define-fun my-or ((x Bool) (y Bool)) Bool (or x y))
(assert (forall ((x Bool) (y Bool)) (= (my-or x y) (or x y))))
(check-sat)

;mapping or with map works just fine
(define-sort Set () (Array Int Bool))
(declare-const a Set)
(assert ( = a ((_ map or) a a) ))
(check-sat)

;fails with error
(assert ( = a ((_ map my-or) a a) ))

