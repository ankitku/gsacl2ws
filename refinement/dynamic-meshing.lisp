(in-package "ACL2S")

(include-book "static-meshing")

;; Dynamic Meshing (DM)
;; An extension of SM that allows for adding/removing mesh neighbors
;; by sending GRAFT or PRUNE

;; State is unchanged, so refinement map is id, we just use sm

(defdata dm-evnt
  (v (list peer verb peer 'PAYLOAD payload-type)
     (list peer 'APP payload-type)
     (list peer verb peer 'IHAVE lopid)
     (list peer verb peer 'IWANT lopid)
     (list peer verb peer 'GRAFT topic)
     (list peer verb peer 'PRUNE topic)
     hbm-evnt))

(encapsulate
  ()
  (local
   (property lop->tlp (x :lop)
             (tlp x)))
  
  ;;have an mcache to advertise for all messages (don't trim)
  ;;send IHAVEs on all HBMs to non mesh, non fanout peers
  (definecd dm-trx (sm :sm-peer-state ev :evnt) :sm-trx-ret
    :ic (sm-peer-state-invp sm)
    (let ((meshes (sm-peer-state-meshes sm)))
      (match ev
        ((& 'RCV p2 'GRAFT top)
	 (sm-trx-ret (mset :meshes (add-sub meshes p2 top) sm) '()))
	((& 'RCV p2 'PRUNE top)
	 (sm-trx-ret (mset :meshes (rem-sub meshes p2 top) sm) '()))
        (& (sm-trx sm ev))))))


;; We define our WEB relation
(definec webb-dm-sm (st1 st2 :sm-peer-state st2) :boolean
  (== (sm-peer-state-seen st1)
      (sm-peer-state-seen st2)))
   
  
;; Proof that webb is a WEB refinement

;; 1. 
(property webb12 (st :sm-peer-state)
          :h (sm-peer-state-invp st)
          (webb-dm-sm st st))

;; 2. Web1 : webb-dm-sm is an equivalence relation because it's an ACL2s equality ==

;; 3. Web2 : L = (lambda (x) (mget :seen x)) returns what is observable
(property web22 (s w :sm-peer-state)
          (=> (webb-dm-sm s w)
              (== (mget :seen s) (mget :seen w))))

;; 4. Web3a
;; Faster but doesn't use defun-sk
;; (property web3a (s :sm-peer-state w :pb-peer-state ev :sm-evnt)
;;           :hyps (^ (webb s w)
;;                    (sm-peer-state-invp s))
;;           (webb (sm-trx-ret-st (sm-trx s ev))
;;                 (pb-trx-ret-st (pb-trx w ev)))
;;           :hints (("Goal" :in-theory (enable webb sm-trx pb-trx))))

(defun web3a-stmt2 (s w v ev)
  (=> (webb-dm-sm s w)
      (webb-dm-sm (sm-trx-ret-st (dm-trx s ev)) v)))

(defun-sk exists-web3a-stmt2 (s w ev)
  (exists v (web3a-stmt2 s w v ev)))

(property web3a2 (s w :sm-peer-state ev :dm-evnt)
          :check-contracts? nil
          :hyps (sm-peer-state-invp s)
          (exists-web3a-stmt2 s w ev)
          :hints (("Goal" :in-theory (enable webb-dm-sm sm-trx)
                   :use ((:instance exists-web3a-stmt2-suff
                                    (v (sm-trx-ret-st (sm-trx w ev))))))))
