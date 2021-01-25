; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

;; Brett Sullivan and Mary Ragheb

;; A NZN is an Integer > 0
;; represents a non-zero-nat
(defdata nzn (range integer (0 < _)))

;; gcd: Nat Nat -> Nat
;; greatest common denominator of a and b
(definec gcd2 (a :nat b :nat) :nat
  (if (zp b)
    a
    (gcd2 b (mod a b))))

;; coprimep: Nat Nat -> Boolean
;; a and b are coprime if their gcd is 1
(definec coprimep (a :nat b :nat) :boolean
  (= (gcd2 a b) 1))

;; etf-helper: NZN Nat -> Nat
;; the number of nats in the range [1 x] that are coprime with n
(definec etf-helper (n :nat x :nat) :nat
  (cond ((zp x) 0)
        ((coprimep n x) (1+ (etf-helper n (1- x))))
        (t (etf-helper n (1- x)))))

;; etf: NZN -> Nat
;; the number of nats in the range [1 n] that are coprime with n
(definec etf (n :nzn) :nat
  (if (= n 1)
    1
    (etf-helper n (1- n))))


;; Conjecture:
;; (<= (etf n) n)


;; Lemma 1: helper-bounded-by-x
;; (<= (etf-helper n x) x)

;; Proof by Induction on x.

;;Base-case
(defthm h-bbx-bc (implies (and (nznp n)
                               (natp x))
                          (implies (zp x)
                                   (<= (etf-helper n x) x))))

;; Inductive-case
(defthm h-bbx-ic (implies (and (nznp n)
                               (natp x))
                          (implies (not (zp x))
                                   (implies 
                                    (<= (etf-helper n (1- x)) (1- x))
                                    (<= (etf-helper n x)
                                        x)))))

;; By proving the base-case and the inductive-case, we show the lemma holds
(defthm h-bbx (implies (and (nznp n)
                            (natp x))
                       (<= (etf-helper n x)
                           x)))


;; Lemma 2: n>n-1
;; (<= (etf-helper n (1- n)) (1- n)) -> (<= (etf-helper n (1- n)) n)
(defthm n<n-1 (implies (<= (etf-helper n (1- n))
                           (1- n))
                       (<= (etf-helper n (1- n))
                           n)))

;; Lemma 3: helper-bounded-by-n
;; (<= (etf-helper n (1- n)) n)
(defthm h-bbn (implies (nznp n)
                       (<= (etf-helper n (1- n))
                           n)))


;; Theorem: etf-bounded-by-n 
;; (<= (etf n) n)

;; Broken into 2 sublemmatta 

;; Case 1
(defthm bbn-c1 (implies (nznp n)
                        (implies (= n 1)
                                 (<= (etf n)
                                     n))))

;; Case 2
(defthm bbn-c2 (implies (nznp n)
                        (implies (not (= n 1))
                                 (implies (<= (etf-helper n (1- n))
                                              n)
                                          (<= (etf n)
                                              n)))))

;; By proving the c1 and the c2, we show the theorem holds
(defthm bbn (implies (nznp n)
                     (<= (etf n)
                         n)))#|ACL2s-ToDo-Line|#
