;; Values
(define-sort Value () Int)

;; Fields
(declare-datatypes () 
  ((Field 
      Switch 
      Port )))

(declare-datatypes () 
  ((Packet (mk-packet (switch-value Value)
                      (port-value Value)
                      (hist-value(List Value))))))

(declare-datatypes ()
  ((Policy (pol-filter (filter-field Field) (filter-value Value))
           (pol-modify (modify-field Field) (modify-value Value))
           (pol-dup)
           (pol-one)
           (pol-seq (seq-left Policy) (seq-right Policy))
           (pol-union (union-left Policy) (union-right Policy))
           (pol-star (star-pol Policy))
           (pol-zero))))

(declare-rel Eval (Policy Packet Packet))

(declare-rel Fun (Policy))

;; One 
(assert (forall ((h Packet))
                 (Eval pol-one h h)))

;; Zero 
;; NB: Only if you are interested in this packet you know that it can't evaluate!
(assert (forall ((h1 Packet) (h2 Packet)) 
             (not (Eval pol-zero h1 h2))))

;; Union
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h2 Packet))
      (iff (or (Eval p h1 h2) (Eval q h1 h2)) (Eval (pol-union p q) h1 h2))))

;; Sequence
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h2 Packet) (h3 Packet))
            (iff (and (Eval p h1 h2) (Eval q h2 h3)) (Eval (pol-seq p q) h1 h3))))

;; Star
(assert (forall ((p Policy) (h1 Packet) (h2 Packet))
           (iff (Eval (pol-union pol-one (pol-seq p (pol-star p))) h1 h2) (Eval (pol-star p) h1 h2))))

;; Dup
(assert (forall ((h1 Packet))
      (Eval pol-dup h1 (mk-packet (switch-value h1)
                                  (port-value h1)
                                  (insert (switch-value h1) (hist-value h1))))))

;; Filter 
(assert (forall ((h1 Packet) (v Value))
             (iff (= (switch-value h1) v) (Eval (pol-filter Switch v) h1 h1))))

(assert (forall ((h1 Packet) (v Value))
             (iff (= (port-value h1) v) (Eval (pol-filter Port v) h1 h1))))

;; Modify 
(assert (forall ((h1 Packet) (v Value))
              (Eval (pol-modify Switch v) h1 (mk-packet v (port-value h1) (hist-value h1)))))

(assert (forall ((h1 Packet) (v Value))
              (Eval (pol-modify Port v) h1 (mk-packet (switch-value h1) v (hist-value h1)))))

;; Functional

(assert (Fun pol-one))
(assert (Fun pol-zero))
(assert (forall ((f Field) (v Value))
                (Fun (pol-filter f v))))
(assert (forall ((f Field) (v Value))
                (Fun (pol-modify f v))))
(assert (forall ((p Policy) (q Policy))
                (implies (and (Fun p) (Fun q))
                         (Fun (pol-seq p q)))))
(assert (Fun pol-dup))

;; There are other special cases where we get a function, for example
;; if p equiv q and (Fun p) then (Fun (pol-union p q))

(assert (forall ((p Policy) (h1 Packet) (h2 Packet) (h3 Packet))
                (implies (and (Fun p) )
                         (implies (and (Eval p h1 h2)
                                       (Eval p h1 h3))
                                  (= h2 h3)))))

;; Min axiom propagation 
(assert (forall ((h Packet) (p Policy) (q Policy))
           (implies (Min (pol-union p q) h) (and (Min p h) (Min q h)))))

(assert (forall ((h Packet) (h1 Packet) (p Policy) (q Policy))
           (implies (Min (pol-seq p q) h) 
                    (and (Min p h)
                         (implies (Eval p h h1) (Min q h1))))))

(assert (forall ((h Packet) (p Policy))
        (implies (Min (pol-star p) h) (Min (pol-union pol-one (pol-seq p (pol-star p))) h))))

;; Main
(declare-var h1 Packet)
(declare-var h2 Packet)
(declare-var p0 Policy)

(assert (= p0 (pol-seq (pol-modify Switch 1) (pol-modify Switch 2))))
(assert (= h1 (mk-packet 0 0 nil)))
(assert (= h2 (mk-packet 2 0 nil)))

;(assert (Min p0 h1))
;(assert (Eval p0 h1 h2))

(check-sat)
(get-model)

