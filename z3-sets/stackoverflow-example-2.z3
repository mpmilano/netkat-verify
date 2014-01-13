(define-fun my-or-impl ((x Bool) (y Bool)) Bool (or x y))
(declare-fun my-or (Bool Bool) Bool)
(assert (forall ((x Bool) (y Bool)) (= (my-or x y) (my-or-impl x y))))
(check-sat)

