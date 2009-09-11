
#||
code-injection.lisp: Seshadri, Luk, Qu, and Perrig, in their SecVisor paper, implement
a hypervisor that satisfies a certain set of properties in order to prevent
code injection attacks. In a later paper, the Murphi model checker is used to
formally verify that their hypervisor doesn't violate their properties, but
they never formally verify that the properties given are sufficient for
preventing code injection attacks (perhaps because it's too trivial, or perhaps
because model checking is incapable of proving such a statement.) This file
contains an ACL2 proof that the given properties are sufficient for preventing
code injection attacks. Moreover, a technically weaker (but practically
equivalent) version of the same properties is also sufficient.

kernel-seperation.lisp: This file develops a kernel seperation property based
on the above properties, plus the condition that the kernel's data region is
inaccessable while arbitrary user code is executing (which the SecVisor paper
postulates in the case where a shadow page table is used). This can be
trivially modified to handle the case where user processes can read but not
modify kernel code and data

kernel-seperation-machine.lisp: is a refinement of kernel-seperation.lisp on a
less abstract machine

return-oriented-programming.lisp: allow the attack to use return-to-libc and generalized return
oriented programming, and show that an exploit exists

return-oriented-programming-protection.lisp: prove that protection agaisnt return oriented programming is possible
programming
||#

(in-package "ACL2")
(include-book "misc/records" :dir :system)

;this file is patterned after Sandip Ray's virtual-spec. 

;the user has no access to kernel space, but the kernel can affect user space,
;in 'abstract' terms, a 'concrete' op can do one of these things.

;1. User op: this is some abstract op in user space and a no-op in kernel space

;2. Self contained kernel op: this is some abstract op in kernel space and a
;no-op in user space

;3. Kernel writes user (and possibly itself): this is an abstract op in kernel space and an abstract
;op with non-deterministic I/O in user space

;4. Kernel reads user: this is an abstract op with non-determinsitic I/O in
;kernel space

;5. Kernel reads and writes user: this is a abstract op with non-deterministic
;I/O in both user and kernel space


;;These mappings are more explict than they need to be. This was done to help
;;track down some bugs in the formulation of the correctness properties, and
;;there's really no reason these can't be moved back into the encapsulate block
;;and made abstract


;;nil = kernel op and t = user op

(local
 (defun map-id (id op st-id ld-id)
   (declare (ignore op))
                                          ;uop = user op; kop = kernel op
   (cond (id                    '(t))     ;any uop
         ((and st-id ld-id)     '(t nil)) ;kop which reads and writes user
         (st-id                 '(t nil)) ;kop which writes user
         (ld-id                 '(nil))   ;kop which reads user
         (t                     '(nil)))));kop which only touches kernel

(local
 (defun map-op-io (id op st-id ld-id)
   (declare (ignore op))
    (cond (id                    '(nil))
          ((and st-id ld-id)     '(t t))
          (st-id                 '(t nil))
          (ld-id                 '(t))
          (t                     '(nil)))))

(local
 (defun map-op (id op st-id ld-id)
    (cond (id                    (list op))
          ((and st-id ld-id)     (list op op))
          (st-id                 (list op op))
          (ld-id                 (list op))
          (t                     (list op)))))

(defun cop-listp (cop-list)
  (let* ((cop-item (first cop-list))
         (id (first cop-item))
         (st-id (third cop-item)))
  (cond ((endp cop-list) t)
        ((and (booleanp id) (booleanp st-id)) (cop-listp (rest cop-list)))
        (t nil))))

(encapsulate 
 
 (((abs->conc *) => *)
  ((conc->abs * *) => *)
  ((cop * * * * *) => *)
  ((aop * * *) => *)
;  ((map-id * * *) => *)
;  ((map-op * * *) => *)
  ((valid-abs? *) => *)
  ((valid-conc? *) => *))
  
 ;;this turns an abstract state into a concrete machine state
 (local
  (defun abs->conc (abs)
    (declare (ignore abs))
    nil))

 ;;this rips out the abstract state associated with either user or kernel space
 ;;from a concrete state of the whole machine
 (local
  (defun conc->abs (conc id)
    (declare (ignore conc id))
    nil))

 ;; concrete op - inputs are:
 ;; concrete state
 ;; the id of the operator
 ;; the operation
 ;; the store target of the op
 ;; the load target of the op 
 (local
  (defun cop (conc id op st-id ld-id)
    (declare (ignore conc id op st-id ld-id))
    nil))


 ;;abstract op - inputs are:
 ;;abstract state
 ;;some oracular I/O
 (local 
  (defun aop (abs op io)
    (declare (ignore abs op io))
    nil))

 ;;not actually an invariant
 (local
  (defun valid-abs? (abs)
    (declare (ignore abs))
    nil))

 ;;invariant on concrete machine states
 (local
  (defun valid-conc? (conc)
    (declare (ignore conc))
    nil))

 
 ;;this -1 / -2 nonsense is a sure sign that this is the wrong approach. This
 ;;entire thing could probably be refactored to 1/2 to 1/3 its current size and
 ;;complexity, but it's 4am, and this is just a justification for trying this
 ;;on a less abstract machine, so I'm going to see if I can finish this
 ;;incredibly inelegant version before heading to work, so I can avoid ever
 ;;looking at it again :)

 ;;other changes to make while refactoring:
 ;; 1. don't use nil as an identifier 
 ;; 2. pass around a single variable which contains all the relevant op info,
 ;;instead of using 4 vars for each concrete op and 3 vars for each abstract op

 ;;in retrospect, it probably would have saved time to recast these properties
 ;;in a simpler way. 


 ;;the following two properties capture all combinations listed in 1. - 5., above
 (defthm aop-makes-sense-1
   (let* ((abs-ids (map-id id op st-id ld-id))
          (abs-ops (map-op id op st-id ld-id))
          (abs-ios (map-op-io id op st-id ld-id))
          (abs-op (first abs-ops))
          (abs-io (first abs-ios)))
     (implies (and (valid-conc? conc) 
                   (equal (length abs-ids) 1))
              (equal (conc->abs abs-id (cop conc id op st-id ld-id))
                     (if (equal abs-id id)
                         (aop (conc->abs abs-id conc) abs-op abs-io)
                       (conc->abs abs-id conc))))))

 (defthm aop-makes-sense-2
   (let* ((abs-ids (map-id id op st-id ld-id))
          (abs-ops (map-op id op st-id ld-id))
          (abs-ios (map-op-io id op st-id ld-id))
          (cop-result (cop conc id op st-id ld-id))
          (abs-id-1 (first abs-ids))
          (abs-op-1 (first abs-ops))
          (abs-io-1 (first abs-ios))
          (abs-id-2 (second abs-ids))
          (abs-op-2 (second abs-ops))
          (abs-io-2 (second abs-ios)))
     (implies (and (valid-conc? conc) 
                   (equal (length abs-ids) 2))
              (and (equal (conc->abs abs-id-1 cop-result)
                     (aop (conc->abs abs-id-1 conc) abs-op-1 abs-io-1))
                   (equal (conc->abs abs-id-2 cop-result)
                     (aop (conc->abs abs-id-2 conc) abs-op-2 abs-io-2))))))

 (defthm abs->conc-is-inverse-of-conc->abs
   (implies (valid-abs? abs)
            (equal (conc->abs id (abs->conc abs))
                   (g id abs))))

 ;;the invariant holds
 (defthm cop-is-valid
   (implies (valid-conc? conc)
            (valid-conc? (cop conc id op st-id ld-id))))

;; don't really need this
;; (defthm aop-is-valid
;;   (implies (valid-abs? abs)
;;            (valid-abs? (aop abs op io))))

 ;;we want something satisfying the invariant when we make a conrete machine
 ;;state
 (defthm abs->conc-is-valid
   (implies (valid-abs? abs)
            (valid-conc? (abs->conc abs))))

 )

(defun crun (conc cop-list)
  (let ((cop-item (first cop-list)))
    (if (endp cop-list) 
        conc
      (crun (cop conc (first cop-item) (second cop-item) (third cop-item)
                 (fourth cop-item))
            (rest cop-list)))))

(defthm crun-is-valid
  (implies (valid-conc? conc)
           (valid-conc? (crun conc cop-list))))

(defun arun (abs aop-list)
  (let ((aop-item (first aop-list)))
    (if (endp aop-list)
        abs
      (arun (aop abs (first aop-item) (second aop-item))
            (rest aop-list)))))

#||
(defthmd arun-is-valid
  (implies (valid-abs? abs)
           (valid-abs? (arun abs aop-list))))
||#

(defun relevant-abs-sequence (id cop-list)
  (let* ((cop-item (first cop-list))
         (abs-ids (map-id (first cop-item) (second cop-item) (third cop-item)
                          (fourth cop-item)))
         (abs-ops (map-op (first cop-item) (second cop-item) (third cop-item)
                          (fourth cop-item)))
         (abs-ios (map-op-io (first cop-item) (second cop-item) (third cop-item)
                          (fourth cop-item)))
         (abs-id-1 (first abs-ids))
         (abs-id-2 (second abs-ids))
         (aop-item-1 (list (first abs-ops) (first abs-ios)))
         (aop-item-2 (list (second abs-ops) (second abs-ios))))
    (cond ((endp cop-list) nil)
          ((and (equal (length abs-ids) 2) (equal abs-id-2 id))
           (cons aop-item-2 (relevant-abs-sequence id (rest cop-list))))
          ((equal abs-id-1 id)
           (cons aop-item-1 (relevant-abs-sequence id (rest cop-list))))
          (t (relevant-abs-sequence id (rest cop-list))))))


;these meaningless crock-* theorems were just used for debugging
(defthmd crock
  (let* ((abs-item (relevant-abs-sequence 
                           abs-id
                           (list (list id op st-id ld-id)))))
    (implies (atom op)
             (por (equal (length abs-item) 1)
                  (equal (length abs-item) 0)))))
    

(defthmd crock-ocl-check
  (equal (length (map-id t op st-id ld-id)) 1))

(defthmd crock-op-corr-1
  (IMPLIES (AND (VALID-CONC? CONC)
                (BOOLEANP ID)
                ID)
           (EQUAL (CONC->ABS NIL (COP CONC T OP ST-ID LD-ID))
                  (CONC->ABS NIL CONC))))

(defthm op-corr-lemma-1
  (IMPLIES (AND ST-ID (VALID-CONC? CONC))
           (EQUAL (CONC->ABS NIL (COP CONC NIL OP T NIL))
                  (AOP (CONC->ABS NIL CONC) OP NIL)))
  :hints (("Goal"
           :in-theory (disable aop-makes-sense-2)
           :use ((:instance aop-makes-sense-2
                            (st-id t)
                            (id nil)
                            (ld-id nil))))))

(defthm op-corr-lemma-2
  (IMPLIES (AND ST-ID 
                (VALID-CONC? CONC))
         (EQUAL (CONC->ABS T (COP CONC NIL OP ST-ID LD-ID))
                (AOP (CONC->ABS T CONC) OP T)))
  :hints (("Goal"
           :in-theory (disable aop-makes-sense-2)
           :use ((:instance aop-makes-sense-2
                            (st-id st-id)
                            (id nil))))))

(defthm op-corr-lemma-3
  (IMPLIES (AND ST-ID LD-ID (VALID-CONC? CONC))
           (EQUAL (CONC->ABS NIL (COP CONC NIL OP T LD-ID))
                  (AOP (CONC->ABS NIL CONC) OP T)))
  :hints (("Goal"
           :in-theory (disable aop-makes-sense-2)
           :use ((:instance aop-makes-sense-2
                            (st-id t)
                            (id nil))))))  


;this rewrite rule isn't required to prove run-correspondence, but proving this
;superfluous lemma was invaluable in figuring out that the three lemmas listed
;above are necessary
(defthmd op-correspondence
  (let* ((ras (relevant-abs-sequence 
                           abs-id 
                           (list (list id op st-id ld-id))))
         (abs-item (first ras))
         (abs-op (first abs-item))
         (abs-io (second abs-item)))
    (implies (and (valid-conc? conc)
                  (booleanp id)
                  (booleanp st-id)
                  (booleanp abs-id))
             (equal (conc->abs abs-id (cop conc id op st-id ld-id))
                    (if (not (equal (length ras) 0))
                        (aop (conc->abs abs-id conc) abs-op abs-io)
                      (conc->abs abs-id conc))))))

(defthm run-correspondence
  (implies (and (valid-conc? conc)
                (booleanp abs-id)
                (cop-listp cop-list))
           (equal (conc->abs abs-id (crun conc cop-list))
                  (arun
                   (conc->abs abs-id conc)
                   (relevant-abs-sequence abs-id cop-list)))))

;;!
(defthm seperation-is-sound
  (let ((conc (abs->conc abs)))
    (implies (and (valid-abs? abs)
                  (booleanp abs-id)
                  (cop-listp cop-list))
             (equal (conc->abs abs-id (crun conc cop-list))
                    (arun
                     (conc->abs abs-id conc)
                     (relevant-abs-sequence abs-id cop-list)))))
  :hints (("Goal"
           :in-theory (disable run-correspondence)
           :use ((:instance run-correspondence
                            (conc (abs->conc abs)))))))
           
