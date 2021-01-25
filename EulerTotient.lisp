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
;; GCD of natural numbers a and b
(definec gcd2 (a :nat b :nat) :nat
  (if (zp b)
    a
    (gcd2 b (mod a b))))

;; Determines if a and b are coprime
(definec coprimep (a :nat b :nat) :boolean
  (= 1 (gcd2 a b)))

;; Euler's Totient function helper
(definec etf-helper (n :nat x :nat) :nat
  (cond ((zp x) 0)
        ((coprimep n x) (1+ (etf-helper n (1- x))))
        (t (etf-helper n (1- x)))))

;; List of numbers between 0 and x that are coprime with n
(definec lc (n :nat x :nat) :tl
  (cond ((zp x) '())
        ((not (coprimep n x)) (lc n (1- x)))
        (t (cons x (lc n (1- x))))))

;; Measure function for etf-acc
(definec etf-acc-measure (n :nat x :nat acc :nat) :nat
  (declare (ignorable n acc))
  x)

;; Euler's Totient function accumulator
(definec etf-acc (n :nat x :nat acc :nat) :nat
  (declare (xargs :measure (if (and (natp n)
                                    (natp x)
                                    (natp acc))
                             (etf-acc-measure n x acc)
                             0)))
  (cond ((zp x) acc)
        ((coprimep n x) (etf-acc n (1- x) (1+ acc)))
        (t (etf-acc n (1- x) acc))))

;; Euler's Totient function
(definec etf (n :nat) :nat
  :ic (> n 0)
  (if (= n 1)
    n
    (etf-acc n (1- n) 0)))

;; Base Case
(thm (implies (and (natp a)
                   (natp b)
                   (natp n)
                   (not (zp n))
                   (coprimep a b)
                   (= n (* a b)))
              (implies (= n 1)
                       (equal (* (etf a) (etf b))
                              (etf n)))))#|ACL2s-ToDo-Line|#


;; Inductive Case
(thm (implies (and (natp a)
                   (natp b)
                   (natp n)
                   (not (zp n))
                   (coprimep a b)
                   (= n (* a b)))
              (implies (not (= n 1))
                       (implies () ;;inductive step here
                        (equal (* (etf a) (etf b))
                               (etf n))))))

;; Goal theorem (does not pass YET)
(thm (implies (and (natp a)
                   (natp b)
                   (natp n)
                   (not (zp n))
                   (coprimep a b)
                   (= n (* a b)))
              (= (* (etf a) (etf b))
                 (etf n))))