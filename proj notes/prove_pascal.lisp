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
#|

Proving Pascal and Pascal's Triangle
(Working Title)

Felicia Zhang
Sarah Coffen

|#

#|
(define (pascal-row-h n m a)
  (cond
    [(> m n) '()]
    [else (let ((a (+ a m)))
            (cons a (pascal-row-h n (add1 m) a)))]))

(define (pascal-row n)
  (pascal-row-h n 1 0))

(define (row-helper prev-row)
  (if (null? (cdr prev-row)) '(1)                   
      (cons (+ (car prev-row) (cadr prev-row))
            (row-helper (cdr prev-row)))))

(define (new-row triangle-list)
  (cons 1 (row-helper (car triangle-list))))

(define (pascal-triangle n)
  (cond
    [(zero? n) '((1))]
    [else (let ([triangle-n-1 (pascal-triangle (- n 1))]) 
            (cons (new-row triangle-n-1) triangle-n-1))]))

|#
:logic

(defdata lon (listof nat))
(defdata llon (listof lon))

(definec pascal-row-h (n :nat m :nat a :nat) :lon
  (if (< n m)
    '()
    (cons (+ a m) (pascal-row-h n (1+ m) (+ a m)))))

(definec pascal-row (n :nat) :lon
  (pascal-row-h n 1 0))

(definec row-helper (prev-row :lon) :lon
  (if (endp (cdr prev-row))
    '(1)
    (cons (+ (car prev-row) (cadr prev-row))
          (row-helper (cdr prev-row)))))

(definec new-row (triangle-list :llon) :lon
  (cons 1 (row-helper (car triangle-list))))

; dummy guess at measure function
(definec measure-pt (n :nat) :nat
 (expt 2 n))
   
(definec pascal-triangle (n :nat) :llon
  (declare (xargs :measure (if (natp n) (measure-pt n) 0)))
  (cond ((zp n) '((1)))
        (t (cons (new-row (pascal-triangle (- n 1)))
                 (pascal-triangle (- n 1))))))

;; For n<2, the output of pascal-triangle doesn't have the third row and is comprised only of 1's
;; n = 0, ((1)); n = 1,((1 1) (1))

(defthm row-helper-empty
  (implies (and (lonp l)
                (or (endp l)
                    (<= (llen l) 1)))
           (equal (row-helper l) '(1))))

(defthm row-helper-length
  (implies (and (lonp l)
                (not (endp l)))
           (equal (llen l) (llen (row-helper l)))))
#|
(defthm row-helper-next
  (implies (and (lonp l)
                (> (llen l) 1)
                (natp n)
                (< n (1- (llen l))))
           (equal (nth n (row-helper l)) (+ (nth n l) (nth (1+ n) l)))))
|#
(thm (implies (natp n)
              (equal (pascal-row n) (pascal-row-h n 1 0))))

(defthm main-base
  (implies (and (natp n) (equal 2 n))
           (equal (nth 0 (pascal-row 1))
                  (nth 2 (nth 0 (pascal-triangle 2))))))
(set-gag-mode nil)
:brr t
(test? (IMPLIES (AND (INTEGERP N)
              (<= 0 N)
              (NOT (ZP N))
              (IMPLIES (AND (NATP (+ -1 N)) (<= 2 (+ -1 N)))
                       (EQUAL (NTH (+ -2 -1 N)
                                   (PASCAL-ROW (+ -1 -1 N)))
                              (NTH 2 (NTH 0 (PASCAL-TRIANGLE (+ -1 N))))))
              (<= 2 N))
         (EQUAL (NTH (+ -2 N) (PASCAL-ROW (+ -1 N)))
                (NTH 2 (NTH 0 (PASCAL-TRIANGLE N))))))

(defdata memo-table (map nat lon))#|ACL2s-ToDo-Line|#


(thm (implies (and (natp n) (<= 2 n))
              (equal (nth (- n 2) (pascal-row (- n 1)))
                     (nth 2 (nth 0 (pascal-triangle n))))))
