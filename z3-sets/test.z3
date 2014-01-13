(define-sort Set (T) (Array T Bool))
(declare-const a (Set Int))
(declare-const b (Set Int))
(declare-const c (Set Int))
(declare-const x Int)
(push)
(assert (not (= ((_ map and) a b) ((_ map not) ((_ map or) ((_ map not) b) ((_ map not) a))))))
(check-sat)
(pop)
(push) 
(assert (and (select ((_ map and) a b) x) (not (select a x))))
(check-sat)
(pop)
(push) 
(assert (and (select ((_ map or) a b) x) (not (select a x))))
(check-sat)
(get-model)
(assert (and (not (select b x))))
(check-sat)
(define-fun set-untion ((x (Set Int)) (y (Set Int))) (Set Int) 
  ((_ map or) x y))

(define-fun to-map ((x Int) (y Int)) Int (+ x y))


(declare-fun fxpt (Int Int) Int )


(define-fun recr ((x Int) (y Int)) Int (recr (+ x y) y))

(assert (= recr fxpt))
