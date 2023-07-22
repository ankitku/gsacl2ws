(in-package "ACL2S")

(include-book "pubsub")

;; Static Meshing (SM)
;; This is a very basic gossipsub protocol with infinite size message cache, that
;; also acts as recently-seen. Has maps for fanout and mesh. Meshes are static
;; i.e. there is no dynamically changing mesh structure.
(defdata sm-peer-state
  (record
   (nbr-topicsubs . topic-lop-map)
   (seen . mcache)
   (fanout . topic-lop-map)
   (meshes . topic-lop-map)))


;;TODO :  Pete : defabbrv for ACL2::

;; following invariants should hold for sm-peer-state
(definec sm-peer-state-invp (st :sm-peer-state) :boolean
;peer doesn't subscribe to topics for which it forwards msgs to fanout
  (^ (! (intersectp-equal (acl2::alist-keys (sm-peer-state-meshes st))
                          (acl2::alist-keys (sm-peer-state-fanout st))))
;peer knows what topics are subscribed to by nbrs in fanout
     (subscription-subsetp (sm-peer-state-fanout st)
                           (sm-peer-state-nbr-topicsubs st))
;peer knows what topics are subscribed to by nbrs in each topic mesh
     (subscription-subsetp (sm-peer-state-meshes st)
                           (sm-peer-state-nbr-topicsubs st))))

(check= (sm-peer-state-invp (sm-peer-state '((FM ANKIT MAX) (PL PETE) (SE CRISTINA))
                                           '()
                                           '((PL PETE))
                                           '((SE CRISTINA))))
        t)


(defdata sm-evnt
  (v (list peer verb peer 'PAYLOAD payload-type)
     (list peer 'APP payload-type)
     (list peer verb peer 'IHAVE lopid)
     (list peer verb peer 'IWANT lopid)
     hbm-evnt))

;; refinement thm : 

(encapsulate
  ()
  (local
   (in-theory (enable evntp)))
  (defdata-subtype pb-evnt sm-evnt))

(encapsulate
  ()
  (local
   (in-theory (enable evntp)))
  (defdata-subtype sm-evnt evnt))

;; given that during HBM, gossip is forwarded to a finite subset of non-mesh
;; nbrs, we want the selection to be fair that guarantees eventual gossip fwd
;; to each neighbor

(defdata sm-trx-ret
  (record
   (st . sm-peer-state)
   (evs . loev)))

(in-theory (enable evntp sm-trx-retp payload-typep mcachep loevp))

(create-map* (lambda (nbr p pids) `(,p SND ,nbr IHAVE ,pids))
             lopp
             loevp
             (:fixed-vars ((peerp p) (lopidp pids)))
             (:name mapgossips-snd))

(create-map* (lambda (nbr p pids) `(,p SND ,nbr IHAVE ,pids))
             lopp
             loevp
             (:fixed-vars ((peerp p) (lopidp pids)))
             (:name mapgossips-rcv))

(property flatten-cdrs-tlm (tlm :topic-lop-map)
  (lopp (flatten (strip-cdrs tlm))))

(definecd gossip-emission (p :peer st :sm-peer-state) :loev
  :ic (sm-peer-state-invp st)
  :skip-tests t
  :timeout 600
  (b* ((seen (sm-peer-state-seen st))
       (mesh-nbrs (sm-peer-state-meshes st))
       (fout (sm-peer-state-fanout st))
       (top-nbrs (sm-peer-state-nbr-topicsubs st))
       (gossip-nbrs (set-difference-equal (flatten (strip-cdrs top-nbrs))
                                          (union-equal (flatten (strip-cdrs mesh-nbrs))
                                                       (flatten (strip-cdrs fout)))))
       (pids (remove-duplicates-equal (map* get-pids seen))))
    (app (map* mapgossips-snd gossip-nbrs p pids)
         (map* mapgossips-rcv gossip-nbrs p pids))))

(encapsulate
  ()
  (local
   (property lop->tlp (x :lop)
             (tlp x)))
  
  ;;have an mcache to advertise for all messages (don't trim)
  ;;send IHAVEs on all HBMs to non mesh, non fanout peers
  (definecd sm-trx (st :sm-peer-state ev :evnt) :sm-trx-ret
    :ic (sm-peer-state-invp st)
    (b* ((default-ret (sm-trx-ret st '()))
         (top-nbrs (sm-peer-state-meshes st))
         (fout (sm-peer-state-fanout st))
         (seen (sm-peer-state-seen st)))
      (match ev
        ((p1 'RCV p2 'PAYLOAD pld)
         (b* ((top (payload-type-top pld))
              (fwdnbrs (set-difference-equal
                        ;;send to nbrs on mesh and fanout
                        (app (mget top top-nbrs)
                             (mget top fout))
                        ;; don't forward to nbrs who already saw this msg
                        (app (seen-nbrs pld seen)
                             ;; don't forward to myself and to the sender
                             `(,p1 ,p2)))))
           ;; update seen with myself and the sender
           (sm-trx-ret (mset :seen `((,pld . ,p1) . ((,pld . ,p2) . ,seen)) st)
                       (app (map* fwd-pld-snd fwdnbrs p1 pld)
                            (map* fwd-pld-rcv fwdnbrs p1 pld)))))
        ((p1 'APP pld)
         (b* ((top (payload-type-top pld))
              (tnbrs (set-difference-equal
                      ;; don't forward to nbrs who already saw this msg
                      (app (mget top top-nbrs)
                           (mget top fout))
                      (seen-nbrs pld seen)))
              (fwdnbrs (remove-equal p1 tnbrs)))
           ;; don't forward to myself
           (sm-trx-ret (mset :seen `((,pld . ,p1) . ,seen) st)
                       (app (map* fwd-pld-snd fwdnbrs p1 pld)
                            (map* fwd-pld-rcv fwdnbrs p1 pld)))))
        ((p1 'RCV p2 'IHAVE pids)
         (let ((missing-pids (set-difference-equal pids (map* get-pids seen))))
           (sm-trx-ret st `((,p1 SND ,p2 IWANT ,missing-pids)))))
        ((p1 'RCV p2 'IWANT pids)
         (sm-trx-ret st (map* send-plds (get-plds pids seen) p1 p2)))
        ((p1 'HBM &) ;; we don't care about the time. We just care about
         ;; heartbeat at this level of refinement
         (sm-trx-ret st (gossip-emission p1 st)))
        (& default-ret)))))


;; We now define the refinement map from SM to PB
(definecd sm->pb-refinemap (st :sm-peer-state) :pb-peer-state
  :ic (sm-peer-state-invp st)
  (pb-peer-state (sm-peer-state-nbr-topicsubs st)
                 (sm-peer-state-seen st)))

;; We define our WEB relation
(definecd webb (st1 :sm-peer-state st2 :pb-peer-state) :boolean
  (== (sm-peer-state-seen st1)
      (pb-peer-state-seen st2)))
   
  
;; Proof that webb is a WEB refinement

;; 1. 
(property webb1 (st :sm-peer-state)
          :h (sm-peer-state-invp st)
          (webb st (sm->pb-refinemap st))
          :hints (("Goal" :in-theory (enable sm->pb-refinemap webb))))

;; 2. Web1 : webb is an equivalence relation because it's an ACL2s equality ==

;; 3. Web2 : L = (lambda (x) (mget :seen x)) returns what is observable
(property web2 (s :sm-peer-state w :pb-peer-state)
          (=> (webb s w)
              (== (mget :seen s) (mget :seen w)))
          :hints (("Goal" :in-theory (enable webb sm-peer-statep pb-peer-statep))))

;; 4. Web3a
;; Faster but doesn't use defun-sk
;; (property web3a (s :sm-peer-state w :pb-peer-state ev :sm-evnt)
;;           :hyps (^ (webb s w)
;;                    (sm-peer-state-invp s))
;;           (webb (sm-trx-ret-st (sm-trx s ev))
;;                 (pb-trx-ret-st (pb-trx w ev)))
;;           :hints (("Goal" :in-theory (enable webb sm-trx pb-trx))))

(defun web3a-stmt (s w v ev)
  (=> (webb s w)
      (webb (sm-trx-ret-st (sm-trx s ev)) v)))

(defun-sk exists-web3a-stmt (s w ev)
  (exists v (web3a-stmt s w v ev)))

(property web3a (s :sm-peer-state w :pb-peer-state ev :sm-evnt)
          :check-contracts? nil
          :hyps (sm-peer-state-invp s)
          (exists-web3a-stmt s w ev)
          :hints (("Goal" :in-theory (enable webb sm-trx pb-trx)
                   :use ((:instance exists-web3a-stmt-suff
                                    (v (pb-trx-ret-st (pb-trx w ev))))))))
