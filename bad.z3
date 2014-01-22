
(declare-datatypes 
 () 
 ((Packet
   (packet
    (Switch (_ BitVec 3))     (InPort (_ BitVec 3))))))  

(declare-datatypes
 ()
 ((Hist
  (hist-one (one-packet Packet))
  (hist-cons (head-hist Packet) (rest-hist Hist))
)))

(define-fun hist-head ((x Hist)) Packet 
	(ite (is-hist-one x) (one-packet x)
	   (head-hist x))
)

(define-fun tail-equal ((x Hist) (y Hist)) Bool
	(ite (is-hist-one x)
	   (is-hist-one y)
	   (ite (is-hist-cons y)
		  (= (rest-hist x) (rest-hist y))
		  false)))
	   



(declare-rel _r33 (Hist Hist))
(declare-rel _r32 (Hist Hist))
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
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv1 3)) (InPort-equals (hist-head inhist) (_ bv1 3))) (and (and (Switch-equals (hist-head outhist) (_ bv5 3)) (InPort-equals (hist-head outhist) (_ bv5 3))) (_r0 inhist outhist))) (q inhist outhist)))

;syntactically-generated rules
;

;filter switch = 0 and port = 0

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv0 3)) (InPort-equals (hist-head inhist) (_ bv0 3))) (equals inhist outhist)) (_r7 inhist outhist)))

;port := 2

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv2 3)) (tail-equal inhist outhist)) (_r15 inhist outhist)))

;filter switch = 2 and port = 2

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv2 3)) (InPort-equals (hist-head inhist) (_ bv2 3))) (equals inhist outhist)) (_r18 inhist outhist)))

;filter switch = 2 and port = 2; (switch := 3; port := 3)

;this is a seq
(rule (=> (and (_r18 inhist midhist) (_r19 midhist outhist)) (_r17 inhist outhist)))

;switch := 1; port := 1

;this is a seq
(rule (=> (and (_r9 inhist midhist) (_r10 midhist outhist)) (_r8 inhist outhist)))

;filter switch = 1 and port = 1; (switch := 2; port := 2)

;this is a seq
(rule (=> (and (_r12 inhist midhist) (_r13 midhist outhist)) (_r11 inhist outhist)))

;port := 3

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv3 3)) (tail-equal inhist outhist)) (_r21 inhist outhist)))

;switch := 3

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv3 3)) (tail-equal inhist outhist)) (_r20 inhist outhist)))

;filter switch = 2 and port = 2; (switch := 3; port := 3) |
;(filter switch = 3 and port = 3; (switch := 4; port := 4) |
; filter switch = 4 and port = 4; (switch := 5; port := 5))

;this is a par
(rule (=> (_r17 inhist outhist) (_r16 inhist outhist)))
(rule (=> (_r22 inhist outhist) (_r16 inhist outhist)))

;port := 4

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv4 3)) (tail-equal inhist outhist)) (_r27 inhist outhist)))

;switch := 5; port := 5

;this is a seq
(rule (=> (and (_r31 inhist midhist) (_r32 midhist outhist)) (_r30 inhist outhist)))

;port := 1

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv1 3)) (tail-equal inhist outhist)) (_r10 inhist outhist)))

;filter switch = 1 and port = 1

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv1 3)) (InPort-equals (hist-head inhist) (_ bv1 3))) (equals inhist outhist)) (_r12 inhist outhist)))

;switch := 3; port := 3

;this is a seq
(rule (=> (and (_r20 inhist midhist) (_r21 midhist outhist)) (_r19 inhist outhist)))

;filter switch = 3 and port = 3

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv3 3)) (InPort-equals (hist-head inhist) (_ bv3 3))) (equals inhist outhist)) (_r24 inhist outhist)))

;filter switch = 4 and port = 4

;this is a filter
(rule (=> (and (and (Switch-equals (hist-head inhist) (_ bv4 3)) (InPort-equals (hist-head inhist) (_ bv4 3))) (equals inhist outhist)) (_r29 inhist outhist)))

;id;
;(filter switch = 0 and port = 0; (switch := 1; port := 1) |
; filter switch = 1 and port = 1; (switch := 2; port := 2) |
; (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;  (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;   filter switch = 4 and port = 4; (switch := 5; port := 5))))

;this is a seq
(rule (=> (and (_r3 inhist midhist) (_r4 midhist outhist)) (_r2 inhist outhist)))

;id;
;(filter switch = 0 and port = 0; (switch := 1; port := 1) |
; filter switch = 1 and port = 1; (switch := 2; port := 2) |
; (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;  (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;   filter switch = 4 and port = 4; (switch := 5; port := 5)))) |
;id

;this is a par
(rule (=> (_r2 inhist outhist) (_r33 inhist outhist)))
(rule (=> (_r3 inhist outhist) (_r33 inhist outhist)))

;filter switch = 0 and port = 0; (switch := 1; port := 1) |
;filter switch = 1 and port = 1; (switch := 2; port := 2)

;this is a par
(rule (=> (_r6 inhist outhist) (_r5 inhist outhist)))
(rule (=> (_r11 inhist outhist) (_r5 inhist outhist)))

;filter switch = 0 and port = 0; (switch := 1; port := 1) |
;filter switch = 1 and port = 1; (switch := 2; port := 2) |
;(filter switch = 2 and port = 2; (switch := 3; port := 3) |
; (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;  filter switch = 4 and port = 4; (switch := 5; port := 5)))

;this is a par
(rule (=> (_r5 inhist outhist) (_r4 inhist outhist)))
(rule (=> (_r16 inhist outhist) (_r4 inhist outhist)))

;switch := 2; port := 2

;this is a seq
(rule (=> (and (_r14 inhist midhist) (_r15 midhist outhist)) (_r13 inhist outhist)))

;filter switch = 3 and port = 3; (switch := 4; port := 4) |
;filter switch = 4 and port = 4; (switch := 5; port := 5)

;this is a par
(rule (=> (_r23 inhist outhist) (_r22 inhist outhist)))
(rule (=> (_r28 inhist outhist) (_r22 inhist outhist)))

;id

;this is a filter
(rule (=> (and true (equals inhist outhist)) (_r3 inhist outhist)))

;filter switch = 0 and port = 0; (switch := 1; port := 1)

;this is a seq
(rule (=> (and (_r7 inhist midhist) (_r8 midhist outhist)) (_r6 inhist outhist)))

;filter switch = 3 and port = 3; (switch := 4; port := 4)

;this is a seq
(rule (=> (and (_r24 inhist midhist) (_r25 midhist outhist)) (_r23 inhist outhist)))

;switch := 1

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv1 3)) (tail-equal inhist outhist)) (_r9 inhist outhist)))

;switch := 4; port := 4

;this is a seq
(rule (=> (and (_r26 inhist midhist) (_r27 midhist outhist)) (_r25 inhist outhist)))

;switch := 2

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv2 3)) (tail-equal inhist outhist)) (_r14 inhist outhist)))

;id;
;(filter switch = 0 and port = 0; (switch := 1; port := 1) |
; filter switch = 1 and port = 1; (switch := 2; port := 2) |
; (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;  (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;   filter switch = 4 and port = 4; (switch := 5; port := 5))));
;(id;
; (filter switch = 0 and port = 0; (switch := 1; port := 1) |
;  filter switch = 1 and port = 1; (switch := 2; port := 2) |
;  (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;   (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;    filter switch = 4 and port = 4; (switch := 5; port := 5)))) |
; id) |
;(id;
; (filter switch = 0 and port = 0; (switch := 1; port := 1) |
;  filter switch = 1 and port = 1; (switch := 2; port := 2) |
;  (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;   (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;    filter switch = 4 and port = 4; (switch := 5; port := 5)))) |
; id)

;this is a par
(rule (=> (_r1 inhist outhist) (_r0 inhist outhist)))
(rule (=> (_r33 inhist outhist) (_r0 inhist outhist)))

;port := 5

;this is a mod
(rule (=> (and (mod_InPort (hist-head inhist) (hist-head outhist) (_ bv5 3)) (tail-equal inhist outhist)) (_r32 inhist outhist)))

;switch := 5

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv5 3)) (tail-equal inhist outhist)) (_r31 inhist outhist)))

;filter switch = 4 and port = 4; (switch := 5; port := 5)

;this is a seq
(rule (=> (and (_r29 inhist midhist) (_r30 midhist outhist)) (_r28 inhist outhist)))

;switch := 4

;this is a mod
(rule (=> (and (mod_Switch (hist-head inhist) (hist-head outhist) (_ bv4 3)) (tail-equal inhist outhist)) (_r26 inhist outhist)))

;id;
;(filter switch = 0 and port = 0; (switch := 1; port := 1) |
; filter switch = 1 and port = 1; (switch := 2; port := 2) |
; (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;  (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;   filter switch = 4 and port = 4; (switch := 5; port := 5))));
;(id;
; (filter switch = 0 and port = 0; (switch := 1; port := 1) |
;  filter switch = 1 and port = 1; (switch := 2; port := 2) |
;  (filter switch = 2 and port = 2; (switch := 3; port := 3) |
;   (filter switch = 3 and port = 3; (switch := 4; port := 4) |
;    filter switch = 4 and port = 4; (switch := 5; port := 5)))) |
; id)

;this is a seq
(rule (=> (and (_r2 inhist midhist) (_r33 midhist outhist)) (_r1 inhist outhist)))
(query (q inhist outhist) 
:default-relation smt_relation2
:engine PDR
:print-answer false)


;This is the program corresponding to 5
