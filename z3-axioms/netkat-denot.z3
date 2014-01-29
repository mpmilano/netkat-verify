;; Values
(define-sort Value () Int)

;; Fields
(declare-datatypes () 
  ((Field 
      Switch 
      Port 
      ;; EthType 
      ;; EthSrc 
      ;; EthDst 
      ;; Vlan 
      ;; VlanPcp 
      ;; IPProto 
      ;; IP4Src 
      ;; IP4Dst 
      ;; TCPSrcPort 
      ;; TCPDstPort
      )))

(declare-datatypes () 
  ((Packet (mk-packet (switch-value Value)
                      (port-value Value)
                      (hist-value(List Value)))))) ;; Just a history of switches

;; A modify function
(declare-fun Modify (Field Value Packet) Packet)

(assert (forall ((v Value) (p Packet)) 
     (= (Modify Switch v p) (mk-packet v (port-value p) (hist-value p)))))

(assert (forall ((v Value) (p Packet)) 
     (= (Modify Port v p)   (mk-packet (switch-value p) v (hist-value p)))))


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
(declare-rel Min (Policy Packet))

;; One 
(assert (forall ((h Packet)) (Eval pol-one h h)))

;; Zero 
;; NB: Only if you are interested in this packet you know that it can't evaluate!
(assert (forall ((h1 Packet) (h2 Packet)) 
    (implies (Min pol-zero h1)
             (not (Eval pol-zero h1 h2)))))

;; Union
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h2 Packet))
   (implies (Min (pol-union p q) h1)
      (iff (or (Eval p h1 h2) (Eval q h1 h2)) (Eval (pol-union p q) h1 h2))
      )))

;; Sequence
(assert (forall ((p Policy) (q Policy) (h1 Packet) (h2 Packet) (h3 Packet))
   (implies (Min (pol-seq p q) h1)
            (iff (and (Eval p h1 h2) (Eval q h2 h3)) (Eval (pol-seq p q) h1 h3))
        )))

;; Star
(assert (forall ((p Policy) (h1 Packet) (h2 Packet))
   (implies (Min (pol-star p) h1)
           (iff (Eval (pol-union pol-one (pol-seq p (pol-star p))) h1 h2) (Eval (pol-star p) h1 h2))
        )))

;; Dup -- causes loop!
(assert (forall ((h1 Packet))
   (implies (Min pol-dup h1)
      (Eval pol-dup h1 (mk-packet (switch-value h1)
                                  (port-value h1)
                                  (insert (switch-value h1) (hist-value h1)))))))


;; Filter 
(assert (forall ((h1 Packet)) (implies (Min (pol-filter Switch (switch-value h1)) h1) (Eval (pol-filter Switch (switch-value h1)) h1 h1))))
(assert (forall ((h1 Packet)) (implies (Min (pol-filter Port (port-value h1))     h1) (Eval (pol-filter Port   (port-value h1)) h1 h1))))

;; Modify 
(assert (forall ((h1 Packet) (v Value)) (implies (Min (pol-modify Switch v) h1) (Eval (pol-modify Switch v) h1 (mk-packet v (port-value h1) (hist-value h1))))))
(assert (forall ((h1 Packet) (v Value)) (implies (Min (pol-modify Port v) h1) (Eval (pol-modify Port v) h1 (mk-packet (switch-value h1) v (hist-value h1))))))

;; Eval functional
(assert (forall ((h1 Packet) (p Policy) (h2 Packet) (h3 Packet))
        (implies (Min p h1)
                 (implies (and (Eval p h1 h2)
                              (Eval p h1 h3))
                          (= h2 h3)))))


;; Min axiom propagation 
(assert (forall ((h Packet) (p Policy) (q Policy))
           (implies (Min (pol-union p q) h) (or (Min p h) (Min p h)))))
(assert (forall ((h Packet) (p Policy) (q Policy))
           (implies (Min (pol-seq p q) h) (and (Min p h) (Min p h)))))
(assert (forall ((h Packet) (p Policy))
        (implies (Min (pol-star p) h) (Min (pol-union pol-one (pol-seq p (pol-star p))) h))))



;; (assert (Min (pol-seq (pol-modify Switch 1) (pol-modify Switch 1)) (mk-packet 0 0 nil)))
;; (assert (Eval (pol-seq (pol-modify Switch 1) (pol-modify Switch 1)) (mk-packet 0 0 nil) (mk-packet 0 0 nil)))



(check-sat)
;; (get-model)

