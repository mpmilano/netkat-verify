
;; Values
(define-sort Value () Int)


;; Fields
(declare-datatypes () 
  ((Field 
      Switch 
      InPort 
      ;; EthType 
      ;; EthSrc 
      ;; EthDst 
      ;; Vlan 
      ;; VlanPcp 
      ;; IPProto 
      ;; IP4Src 
      ;; IP4Dst 
      ;; TCPSrcInPort 
      ;; TCPDstInPort
      )))

(declare-datatypes () 
  ((Packet (mk-packet (switch-value Value)
                      (port-value Value)
                      (hist-value(List Value)))))) ;; Just a history of switches


(declare-datatypes ()
  ((Policy (pol-filter (filter-field Field) (filter-value Value))
           (pol-modify (modify-field Field) (modify-value Value))
           (pol-dup)
           (pol-neg (neg-pol Policy))
           (pol-one)
           (pol-seq (seq-left Policy) (seq-right Policy))
           (pol-union (union-left Policy) (union-right Policy))
           (pol-star (star-pol Policy))
           (pol-zero))))

(declare-rel Eval (Policy Packet Packet))

(declare-rel Min (Policy Packet))

;; One 
(assert (forall ((h Packet)) (Eval pol-one h h)))

;; Zero 
;; NB: Only if you are interested in this packet you know that it can't evaluate!
(assert (forall ((h1 Packet) (h2 Packet)) 
    (implies (Min pol-zero h1)
             (not (Eval pol-zero h1 h2)))))

(assert (forall ((h1 Packet) (h2 Packet) (p Policy))
    (implies (Min (pol-neg p) h1)
             (iff (Eval p h1 h2) (not (Eval (pol-neg p) h1 h2))))))

;; Union
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h2 Packet))
   (implies (Min (pol-union p q) h1)
      (iff (or (Eval p h1 h2) (Eval q h1 h2)) (Eval (pol-union p q) h1 h2))
      )))

;; Sequence, one direction 
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h2 Packet) (h3 Packet))
   (implies (Min (pol-seq p q) h1)
            (implies (and (Eval p h1 h2) (Eval q h2 h3)) (Eval (pol-seq p q) h1 h3))
        )))

;; Reverse axiom for sequence, note the ugly nested existential
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h3 Packet))
   (implies (Min (pol-seq p q) h1)
            (implies (Eval (pol-seq p q) h1 h3)
                     (exists ((h2 Packet)) (and (Eval p h1 h2) (Eval q h2 h3)))))))

;; Star
(assert (forall ((p Policy) (h1 Packet) (h2 Packet))
   (implies (Min (pol-star p) h1)
           (iff (Eval (pol-union pol-one (pol-seq p (pol-star p))) h1 h2) (Eval (pol-star p) h1 h2))
        )))

;; Dup -- causes loop!
(assert (forall ((h1 Packet) (p Policy))
   (! (implies (and (= p pol-dup) (Min pol-dup h1))
       (Eval pol-dup h1 (mk-packet (switch-value h1)
                                   (port-value h1)
                                   (insert (switch-value h1) (hist-value h1)))))
   :pattern (pol-dup))))


;; Filter 
(assert (forall ((h1 Packet)) (implies (Min (pol-filter Switch (switch-value h1)) h1) (Eval (pol-filter Switch (switch-value h1)) h1 h1))))
(assert (forall ((h1 Packet)) (implies (Min (pol-filter InPort (port-value h1))     h1) (Eval (pol-filter InPort   (port-value h1)) h1 h1))))

;; Modify 

(assert (forall ((h1 Packet) (v Value)) (implies (Min (pol-modify Switch v) h1) (Eval (pol-modify Switch v) h1 (mk-packet v (port-value h1) (hist-value h1))))))
(assert (forall ((h1 Packet) (v Value)) (implies (Min (pol-modify InPort v) h1) (Eval (pol-modify InPort v) h1 (mk-packet (switch-value h1) v (hist-value h1))))))

;; Eval functional

(assert (forall ((h1 Packet) (f Field) (v Value) (h2 Packet) (h3 Packet))
        (implies (Min (pol-filter f v) h1)
                 (implies (and (Eval (pol-filter f v) h1 h2)
                              (Eval (pol-filter f v) h1 h3))
                          (= h2 h3)))))

(assert (forall ((h1 Packet) (f Field) (v Value) (h2 Packet) (h3 Packet))
        (implies (Min (pol-modify f v) h1)
                 (implies (and (Eval (pol-modify f v) h1 h2)
                              (Eval (pol-modify f v) h1 h3))
                          (= h2 h3)))))


(assert (forall ((h1 Packet) (h2 Packet) (h3 Packet))
        (implies (Min pol-one h1)
                 (implies (and (Eval pol-one h1 h2)
                              (Eval pol-one h1 h3))
                          (= h2 h3)))))


;; Min axiom propagation
(assert (forall ((h Packet) (p Policy) (q Policy))
           (implies (Min (pol-union p q) h) (or (Min p h) (Min q h)))))

(assert (forall ((h Packet) (h1 Packet) (p Policy) (q Policy))
           (implies (Min (pol-seq p q) h) 
                         (and (Min p h)
                            (implies (Eval p h h1)  (Min q h1))))))

(assert (forall ((h Packet) (p Policy))
        (implies (Min (pol-star p) h) (Min (pol-union pol-one (pol-seq p (pol-star p))) h))))

(assert (forall ((h Packet) (p Policy))
        (implies (Min (pol-neg p) h) (Min p h))))


;; (assert (Min (pol-modify Switch 1) (mk-packet 0 0 nil)))
;; (assert (Min (pol-modify Switch 2) (mk-packet 1 0 nil)))
;; (assert (Eval (pol-modify Switch 1) (mk-packet 0 0 nil) (mk-packet 1 0 nil)))
;; (assert (Eval (pol-modify Switch 2) (mk-packet 1 0 nil) (mk-packet 2 0 nil)))
;; Tests

(assert (Min (pol-star (pol-seq (pol-filter Switch 1) (pol-modify Switch 3))) (mk-packet 1 1 nil)))
(assert (Eval (pol-star (pol-seq (pol-filter Switch 1) (pol-modify Switch 3))) (mk-packet 1 1 nil) (mk-packet 2 2 nil)))
(check-sat)
;This is the program corresponding to smallest-possible-star
