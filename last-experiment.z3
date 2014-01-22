

(declare-datatypes 
 () 
 ((Packet
   (packet
    (Switch (_ BitVec 3))     (InPort (_ BitVec 3))))))  


(declare-datatypes
 ()
 ((Hist
  (mk-hist (head-hist Packet) (tail-hist (_ BitVec 16))))))

(define-fun hist-head ((x Hist)) Packet (head-hist x))

(define-fun tail-equal ((x Hist) (y Hist)) Bool
   (= (tail-hist x) (tail-hist y)))


(declare-rel _r31 (Hist Hist))
(declare-rel _r30 (Hist Hist))
(declare-rel _r29 (Hist Hist))
(declare-rel _r28 (Hist Hist))
(declare-rel _r27 (Hist Hist))
(declare-rel _r26 (Hist Hist))
(declare-rel _r25 (Hist Hist))
(declare-rel _r24 (Hist Hist))
(declare-rel _r23 (Hist Hist))
(declare-rel _r22 (Hist Hist))
(declare-rel _r21 (Hist Hist))
(declare-rel _r20 (Hist Hist))
(declare-rel _r19 (Hist Hist))
(declare-rel _r18 (Hist Hist))
(declare-rel _r17 (Hist Hist))
(declare-rel _r16 (Hist Hist))
(declare-rel _r15 (Hist Hist))
(declare-rel _r14 (Hist Hist))
(declare-rel _r13 (Hist Hist))
(declare-rel _r12 (Hist Hist))
(declare-rel _r11 (Hist Hist))
(declare-rel _r10 (Hist Hist))
(declare-rel _r9 (Hist Hist))
(declare-rel _r8 (Hist Hist))
(declare-rel _r7 (Hist Hist))
(declare-rel _r6 (Hist Hist))
(declare-rel _r5 (Hist Hist))
(declare-rel _r4 (Hist Hist))
(declare-rel _r3 (Hist Hist))
(declare-rel _r2 (Hist Hist))
(declare-rel _r1 (Hist Hist))
(declare-rel _r0 (Hist Hist))
(define-fun packet_equals_except_InPort ((x Packet) (y Packet)) Bool (equals (Switch x) (Switch y)))
(define-fun packet_equals_except_Switch ((x Packet) (y Packet)) Bool (equals (InPort x) (InPort y)))

;end initial declarations, commence dependent declarations
;
(define-fun mod_InPort ((x Packet) (y Packet) (v (_ BitVec 3))) Bool (and (packet_equals_except_InPort x y) (equals (InPort y) v)))
(define-fun mod_Switch ((x Packet) (y Packet) (v (_ BitVec 3))) Bool (and (packet_equals_except_Switch x y) (equals (Switch y) v)))
(define-fun Switch-equals ((x Packet) (v (_ BitVec 3))) Bool (equals (Switch x) v))
(define-fun InPort-equals ((x Packet) (v (_ BitVec 3))) Bool (equals (InPort x) v))

;End Definitions, Commence SAT expressions
;
(declare-var inhist Hist)
(declare-var midhist Hist)
(declare-var outhist Hist)
(declare-var the_packet_a Packet)
(declare-var the_packet_b Packet)
(declare-rel q (Hist Hist))



;rule that puts it all together
;
(rule (=>
       (and (= (_ bv42 16) (tail-hist inhist))
            (and (= (_ bv42 16) (tail-hist outhist))
                 (and (and (Switch-equals (hist-head inhist) (_ bv1 3)) (InPort-equals (hist-head inhist) (_ bv1 3))) (and (and (Switch-equals (hist-head outhist) (_ bv2 3)) (InPort-equals (hist-head outhist) (_ bv2 3))) (_r0 inhist outhist))))) (q inhist outhist)))

;syntactically-generated rules
;

;filter switch = 0 and port = 0

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv0 3)) (InPort-equals (hist-head inhist) (_ bv0 3))) (equals inhist outhist)) (_r5 inhist outhist)))

;(id;
; (filter switch = 0 and port = 0; (switch := 1; port := 1) |
;  (filter switch = 1 and port = 1; (switch := 2; port := 2) |
;   (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;    (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;     filter switch = 4 and port = 4; (switch := 5; port := 5))))))*

;this is a star
(rule (=> (equals inhist outhist) (_r0 inhist outhist)))
(rule (=> (and (_r1 inhist midhist) (_r0 midhist outhist)) (_r0 inhist outhist)))

;port := 2

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv2 3)) (tail-equal inhist outhist)) (_r14 inhist outhist)))

;switch := 2; port := 2

;this is a seq
(rule (=> (and (_r13 inhist midhist) (_r14 midhist outhist)) (_r12 inhist outhist)))

;filter switch = 2 and port = 2

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv2 3)) (InPort-equals (hist-head inhist) (_ bv2 3))) (equals inhist outhist)) (_r17 inhist outhist)))

;filter switch = 2 and port = 2; (switch := 3; port := 3)

;this is a seq
(rule (=> (and (_r17 inhist midhist) (_r18 midhist outhist)) (_r16 inhist outhist)))

;switch := 1; port := 1

;this is a seq
(rule (=> (and (_r7 inhist midhist) (_r8 midhist outhist)) (_r6 inhist outhist)))

;filter switch = 1 and port = 1; (switch := 2; port := 2) |
;(filter switch = 2 and port = 2; (switch := 3; port := 3) |
; (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;  filter switch = 4 and port = 4; (switch := 5; port := 5)))

;this is a par
(rule (=> (_r10 inhist outhist) (_r9 inhist outhist)))
(rule (=> (_r15 inhist outhist) (_r9 inhist outhist)))

;id;
;(filter switch = 0 and port = 0; (switch := 1; port := 1) |
; (filter switch = 1 and port = 1; (switch := 2; port := 2) |
;  (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;   (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;    filter switch = 4 and port = 4; (switch := 5; port := 5)))))

;this is a seq
(rule (=> (and (_r2 inhist midhist) (_r3 midhist outhist)) (_r1 inhist outhist)))

;filter switch = 1 and port = 1; (switch := 2; port := 2)

;this is a seq
(rule (=> (and (_r11 inhist midhist) (_r12 midhist outhist)) (_r10 inhist outhist)))

;port := 3

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv3 3)) (tail-equal inhist outhist)) (_r20 inhist outhist)))

;filter switch = 3 and port = 3; (switch := 4; port := 4) |
;filter switch = 4 and port = 4; (switch := 5; port := 5)

;this is a par
(rule (=> (_r22 inhist outhist) (_r21 inhist outhist)))
(rule (=> (_r27 inhist outhist) (_r21 inhist outhist)))

;id

;this is a filter
(rule (=> (and true (equals inhist outhist)) (_r2 inhist outhist)))

;filter switch = 0 and port = 0; (switch := 1; port := 1)

;this is a seq
(rule (=> (and (_r5 inhist midhist) (_r6 midhist outhist)) (_r4 inhist outhist)))

;switch := 3

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv3 3)) (tail-equal inhist outhist)) (_r19 inhist outhist)))

;filter switch = 0 and port = 0; (switch := 1; port := 1) |
;(filter switch = 1 and port = 1; (switch := 2; port := 2) |
; (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;  (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;   filter switch = 4 and port = 4; (switch := 5; port := 5))))

;this is a par
(rule (=> (_r4 inhist outhist) (_r3 inhist outhist)))
(rule (=> (_r9 inhist outhist) (_r3 inhist outhist)))

;filter switch = 2 and port = 2; (switch := 3; port := 3) |
;(filter switch = 3 and port = 3; (switch := 4; port := 4) |
; filter switch = 4 and port = 4; (switch := 5; port := 5))

;this is a par
(rule (=> (_r16 inhist outhist) (_r15 inhist outhist)))
(rule (=> (_r21 inhist outhist) (_r15 inhist outhist)))

;port := 4

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv4 3)) (tail-equal inhist outhist)) (_r26 inhist outhist)))

;filter switch = 3 and port = 3; (switch := 4; port := 4)

;this is a seq
(rule (=> (and (_r23 inhist midhist) (_r24 midhist outhist)) (_r22 inhist outhist)))

;switch := 5; port := 5

;this is a seq
(rule (=> (and (_r30 inhist midhist) (_r31 midhist outhist)) (_r29 inhist outhist)))

;switch := 1

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv1 3)) (tail-equal inhist outhist)) (_r7 inhist outhist)))

;port := 1

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv1 3)) (tail-equal inhist outhist)) (_r8 inhist outhist)))

;switch := 4; port := 4

;this is a seq
(rule (=> (and (_r25 inhist midhist) (_r26 midhist outhist)) (_r24 inhist outhist)))

;filter switch = 1 and port = 1

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv1 3)) (InPort-equals (hist-head inhist) (_ bv1 3))) (equals inhist outhist)) (_r11 inhist outhist)))

;switch := 2

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv2 3)) (tail-equal inhist outhist)) (_r13 inhist outhist)))

;switch := 3; port := 3

;this is a seq
(rule (=> (and (_r19 inhist midhist) (_r20 midhist outhist)) (_r18 inhist outhist)))

;filter switch = 3 and port = 3

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv3 3)) (InPort-equals (hist-head inhist) (_ bv3 3))) (equals inhist outhist)) (_r23 inhist outhist)))

;filter switch = 4 and port = 4

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv4 3)) (InPort-equals (hist-head inhist) (_ bv4 3))) (equals inhist outhist)) (_r28 inhist outhist)))

;port := 5

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv5 3)) (tail-equal inhist outhist)) (_r31 inhist outhist)))

;switch := 5

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv5 3)) (tail-equal inhist outhist)) (_r30 inhist outhist)))

;filter switch = 4 and port = 4; (switch := 5; port := 5)

;this is a seq
(rule (=> (and (_r28 inhist midhist) (_r29 midhist outhist)) (_r27 inhist outhist)))

;switch := 4

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv4 3)) (tail-equal inhist outhist)) (_r25 inhist outhist)))

(query (q inhist outhist) 
:default-relation smt_relation2
:engine PDR
:print-answer true)


;This is the program corresponding to 5
