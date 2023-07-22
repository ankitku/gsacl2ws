(in-package "ACL2S")

(include-book "../nbrs-topics-state")
(include-book "../msgs-state")

;; A pubsub peer state (PB)
(defdata pb-peer-state
  (record
   (nbr-topicsubs . topic-lop-map)
   (seen . mcache)))

(property pb-peer-state-check-prop (x :pb-peer-state)
  (^ (mcachep (mget :seen x))
     (topic-lop-mapp (mget :nbr-topicsubs x)))
  :hints (("Goal" :in-theory (enable pb-peer-statep)))
  :rule-classes :forward-chaining)
          
(defdata pb-evnt
  (v (list peer verb peer 'PAYLOAD payload-type)
     (list peer 'APP payload-type)))

(encapsulate
  ()
  (local
   (in-theory (enable evntp)))
  (defdata-subtype pb-evnt evnt))

(defdata pb-trx-ret
  (record
   (st . pb-peer-state)
   (evs . loev)))

(create-map* (lambda (nbr p1 pld) `(,p1 SND ,nbr PAYLOAD ,pld))
             lopp
             loevp
             (:name fwd-pld-snd)
             (:fixed-vars ((peerp p1) (payload-typep pld))))

(encapsulate
  ()
  (local
   (in-theory (enable evntp)))
  (create-map* (lambda (nbr p1 pld) `(,nbr RCV ,p1 PAYLOAD ,pld))
               lopp
               loevp
               (:name fwd-pld-rcv)
               (:fixed-vars ((peerp p1) (payload-typep pld)))))

(definecd seen-nbrs (pld :payload-type sns :mcache) :lop
  (match sns
    (() ())
    (((p . peer) . rst) (if (equal p pld)
                            `(,peer . ,(seen-nbrs pld rst))
                          (seen-nbrs pld rst)))))
                   
(encapsulate
  ()
  (local 
   (in-theory (enable evntp pb-trx-retp payload-typep mcachep loevp)))

  (local
   (property p1 (x :lop)
             (tlp x)))

  (definecd pb-trx (st :pb-peer-state ev :evnt) :pb-trx-ret
    (b* ((default-ret (pb-trx-ret st '()))
         (top-nbrs (pb-peer-state-nbr-topicsubs st))
         (seen (pb-peer-state-seen st)))
      (match ev
        ((p1 'RCV p2 'PAYLOAD pld)
         (b* ((top (payload-type-top pld))
              ;; will have to assume that only the virtual network based on
              ;; topics is connected.
              ;; PETE : so, start with simplest case, everyone gets
              ;; messages. Because there may not be a direct path.
              ;; so can show connection in the absence of a direct path.
              ;; what if we want to introduce a new topic? can do that.

              ;; decisions about whether can add or not/ fwd or not/ makes a
              ;; n-dim hyper rectangle.
              (fwdnbrs (set-difference-equal
                        (mget top top-nbrs)
                        ;; don't forward to nbrs who already saw this msg
                        (app (seen-nbrs pld seen)
                             ;; don't forward to myself and to the sender
                             `(,p1 ,p2)))))
           ;; update seen with myself and the sender
           (pb-trx-ret (mset :seen `((,pld . ,p1) . ((,pld . ,p2) . ,seen)) st)
                       (app (map* fwd-pld-snd fwdnbrs p1 pld)
                            (map* fwd-pld-rcv fwdnbrs p1 pld)))))
        ((p1 'APP pld)
         (b* ((top (payload-type-top pld))
              (tnbrs (set-difference-equal
                      ;; don't forward to nbrs who already saw this msg
                      (mget top top-nbrs)
                      (seen-nbrs pld seen)))
              (fwdnbrs (remove-equal p1 tnbrs)))
           ;; don't forward to myself
           (pb-trx-ret (mset :seen `((,pld . ,p1) . ,seen) st)
                       (app (map* fwd-pld-snd fwdnbrs p1 pld)
                            (map* fwd-pld-rcv fwdnbrs p1 pld)))))
        (& default-ret)))))
  
