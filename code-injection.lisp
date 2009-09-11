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

;set the nth value in a record
(defun sn (key pos val rec)
  (let* ((current-list (g key rec))
         (new-list (update-nth pos val current-list)))
    (s key new-list rec)))

;get the nth value in a record
(defun gn (key pos rec)
  (let* ((current-list (g key rec))
         (current-nth (nth pos current-list)))
    current-nth))

#||
(defun contains-addr (s addrs)
  (if (endp addrs)
      nil
    (if (gn :mem (car addrs) s)
        t
      nil)))
||#
              
;a machine state looks like this              
;((:xpl . , booleanp ) ;flag indicating the machine has been explioted
; (:appr . , (list)) ;list of approved code addresses.
; (:mem . , (list)) ;contents of memory; (not nil) = malicious instruction)
; (:ip  . , natp))   ;the current ip. Not actually constrained to be a natp,
; but we use gn, which calls nth, which has a natp guard
; (:cpl . , booleanp ) ; the current privilege level. true = kernel, nil = user
; making cpl a booleanp doesn't simplify any proofs, so it's left unconstrained
; similarly, the ip isn't required to be a natp

(encapsulate
 (((malicious *) => *)
  ((benign *) => *)
  ((mstep *) => *)
  ((valid-s? *) => *))

 
 (local
  ;;this is what happens when a malicious instructon is executed
  (defun malicious (s)
    (declare (ignore s))
    nil))
 
 ;;this is what happens when a non-malicious instruction is executed
 (local 
  (defun benign (s)
    (declare (ignore s))
    nil))

 ;;this is one step of the machine - could be a malicious or benign instruction
 (local 
  (defun mstep (s)
    (declare (ignore s))
    nil))

 ;;valid machine states obey this invariant
 (local
  (defun valid-s? (s)
    (declare (ignore s))
    nil))


 ;;The properties we want to use are listed below. The text in the comments is
 ;;pulled from the SecVisor paper. "True" properties which didn't end up being
 ;;used are introduced with defthmd.

 ;; P1: Every entry into kernel mode (where an entry into kernel mode occurs at
 ;; the instant the privilege of the CPU changes to kernel mode) should set the
 ;; CPU’s Instruction Pointer (IP) to an instruction within approved kernel
 ;; code.

 ;; P2: After an entry into kernel mode places the IP within approved code, the
 ;; IP should continue to point to approved kernel code until the CPU exits
 ;; kernel mode.

 (defthm |p1 and p2 valid|
   (let* ((ip  (g :ip s))
          (appr (g :appr s))
          (cpl (g :cpl s)))
     (implies (valid-s? s)
              (implies cpl
                       (member ip appr)))))

 ;; P3: Every exit from kernel mode (where we define an exit from kernel mode
 ;; as a control transfer that sets the IP to an address in user memory) should
 ;; set the privilege level of the CPU to user mode.

 (defthm |p3 valid|
   (let* ((nxt-ip  (g :ip nxt-s))
          (nxt-cpl (g :cpl nxt-s))
          (nxt-dpl (gn :dpl nxt-ip nxt-s)))
     (implies (valid-s? nxt-s)
              (implies (not nxt-dpl) (not nxt-cpl)))))



 ;; P4: Memory containing approved code should not be modifiable by any code
 ;; executing on the CPU, but SecVisor, or by any peripheral device. 

 ;; this formulation works, but requires extra work to make later proofs go
 ;; through.  

 ;; (defthmd |appr isn't malicious| 
 ;;   (implies (valid-s? s) 
 ;;            (not (contains-addr s (g :appr s)))))
 

 ;assume the TCB is correct, i.e., that only valid code is approved
 (defthmd |appr isn't malicious 2|
   (let ((appr (g :appr s))
         (ins (gn :mem addr s)))
   (implies (and (member addr appr) (valid-s? s))
            (not ins))))

 ;specific instance of above property
 ;only this specific, weaker, property is actually required
 ;p4 isn't required if we have this prop, and p4 requires this to be
 ;true to in order to be meaningful, so this prop is weaker than p4
 (defthm |appr isn't malicious - specific|
   (let* ((appr (g :appr s))
         (ip (g :ip s))
         (ins (gn :mem ip s)))
     (implies (and (member ip appr) (valid-s? s))
              (not ins))))
 
 (defthm |mstep produces valid state|
   (implies (valid-s? s)
            (valid-s? (mstep s))))

 (defthm |malicious produces valid state|
   (implies (valid-s? s)
            (valid-s? (malicious s))))
 
 

;this logically vacuous property obviates the need for a couple pages of
;annoying lemmas later on
 (defthm |xpl is booleanp|
   (implies (valid-s? s)
            (booleanp (g :xpl s)))
   :rule-classes ((:type-prescription 
                   :typed-term (g :xpl s))))


 ;;a malcious instruction can exploit iff it executes in executable space with
 ;;an elevated privilege level.

 ;;the executable space isn't actually used; since it's never constrained,
 ;;leaving it in here has no effect
 (defthm |exploit conditions|
   (let* ((nxt-s (malicious s))
          (ip (g :ip s))
          (exe (member ip (g :exe s)))
          (cpl (g :cpl s)))
     (implies (valid-s? s)
              (iff
               (pand cpl exe)
               (equal (g :xpl nxt-s) t)))))
 
 (defthm |benign can't exploit|
   (let ((nxt-s (benign s)))
     (not (g :xpl nxt-s))))

 

#||
 ;;if memory contains an malicious instruction, we execute it, otherwise we
 ;;execute an benign instruction. This formulation creates an invalid rewrite
 ;;rule, so we write is a slightly more obscure fashion below

 (defthm |mstep runs instruction|
 (let* ((ip  (g :ip s))
 (ins (gn :mem ip s)))
 (implies (valid-s? s)
 (if ins
 (equal (mstep s apr) (malicious s))
 (equal (mstep s apr) (benign s))))))
 ||#

 (defthm |mstep runs malicious|
   (let* ((ip  (g :ip s))
          (ins (gn :mem ip s)))
     (implies (and (valid-s? s) ins)
              (equal (mstep s) (malicious s)))))
 
 (defthm |mstep runs benign|
   (let* ((ip  (g :ip s))
          (ins (gn :mem ip s)))
     (implies (and (valid-s? s) (not ins))
              (equal (mstep s) (benign s)))))
#||
 (defthm |mstep runs instruction|
   (let* ((ip  (g :ip s))
          (ins (gn :mem ip s)))
     (implies (and (valid-s? s) (not ins))
              (or (equal (mstep s) (benign s))
                  (equal (mstep s) (malicious s)))))
   :rule-classes ((:type-prescription
                   :typed-term (mstep s))))
||#              
 )


;just seeing if this obvious property is provable; apparently ACL2 needs to be
;steered a bit to see it.
(defthmd |xpl requires mal|
  (let* ((ip  (g :ip s))
         (ins (gn :mem ip s)))
    (implies (and (valid-s? s) (not ins))
             (not (g :xpl (mstep s)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable |mstep runs benign|)
           :use ((:instance |mstep runs benign|)))))


;something like this lemma is required to prove |xpl requires cpl|, but this
;generates an illegal rewrite rule, so we'll try proving the contrapositive and
;using that
(defthm |heniously obvious lemma|
  (IMPLIES
   (VALID-S? S)
   (NOT (AND (NOT (EQUAL (G :XPL (MALICIOUS S)) T))
             (G :XPL (MALICIOUS S)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable |malicious produces valid state|)
           :use ((:instance |malicious produces valid state|)))))


(defthm |heniously obvious lemma - contrapositive|
  (IMPLIES
   (AND (NOT (EQUAL (G :XPL (MALICIOUS S)) T))
        (G :XPL (MALICIOUS S)))
   (NOT (VALID-S? S)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable |malicious produces valid state|)
            :use ((:instance |malicious produces valid state|)))))


;a sucessful attack requires an elevated privilege level
(defthm |xpl requires cpl|
   (let* ((nxt-s (malicious s))
          (cpl (g :cpl s)))
     (implies (and (g :xpl nxt-s) (valid-s? s))
              cpl))
  :hints (("Goal"
           :in-theory (disable |exploit conditions|)
           :use ((:instance |exploit conditions|)))))

;elevated privilege level implies that we're running approved code
(defthm |xpl requires appr|
  (let* ((nxt-s (mstep s))
         (xpl (g :xpl nxt-s))
         (appr (g :appr s))
         (ip (g :ip s)))
    (implies (and xpl (valid-s? s))
             (member ip appr)))
  ;;  :otf-flg t
  :hints (("Goal"
           :cases ((not (let* ((ip (g :ip s))
                               (ins (gn :mem ip s)))
                         ins))))))
;;           :do-not '(eliminate-destructors generalize fertilize)
;;           :do-not-induct t)))

;approved code can't cause an exploit
(defthm |appr is safe|
  (let* ((nxt-s (mstep s))
         (xpl (g :xpl nxt-s))
         (appr (g :appr s))
         (ip (g :ip s)))
    (implies (and (member ip appr) (valid-s? s))
             (not xpl)))
  :hints (("Goal" 
           :in-theory (disable |xpl requires appr|))))


;; given any valid machine state, running one step is safe
(set-ignore-ok t)
(defthm |mstep is safe from code injection|
  (let* ((nxt-s (mstep s))
         (xpl (g :xpl nxt-s))
         (appr (g :appr s))
         (ip (g :ip s))
         (ins (gn :mem ip s)))
    (implies (valid-s? s)
             (not xpl)))
  :hints (("Goal"
           :use ((:instance |xpl requires appr|)))
          ("Goal'''"
          :in-theory (disable |xpl requires appr|
                              |appr isn't malicious - specific|
                              |appr isn't malicious 2|))))   
(set-ignore-ok nil)

;; this function returns true if running an arbitrary sequence of steps doesn't
;; allow a code injection attack
(defun running-is-safe (s l)
  (declare (xargs :measure (acl2-count l)))
  (let* ((nxt-s (mstep s))
         (xpl (g :xpl nxt-s)))
    (if (atom l) t
      (if xpl
          nil
        (running-is-safe nxt-s (cdr l))))))

;; code injection attacks can't happen with arbitrary sequences
(defthm |running is safe|
  (implies (valid-s? s)
           (running-is-safe s l)))


;; FIXME:
;1. it would be a lot clearer if the minimal set of required constraints were
;included in the encapsulte
;2. it might be better to have a machine step be a function of the machine
;state and some oracle which indicates if a malicious or a benign 'user' is running
