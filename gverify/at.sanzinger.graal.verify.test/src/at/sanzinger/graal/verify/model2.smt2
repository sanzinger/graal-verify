(set-logic QF_BV)(declare-fun n1 () (_ BitVec 32))
(declare-fun n2 () (_ BitVec 32))
(declare-fun n4 () (_ BitVec 32))
(declare-fun n5 () Bool)
(declare-fun n9 () (_ BitVec 32))
(declare-fun n10 () (_ BitVec 32))
(declare-fun n11 () (_ BitVec 32))
(assert (= n4 #x00000000))
(assert (= n5 (= n2 n4)))
(assert (= n9 #xffffffff))
(assert (= n10 (bvadd n1 n11)))
(assert (= n11 (bvnot n1)))
