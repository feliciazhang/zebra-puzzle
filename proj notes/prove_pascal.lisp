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

Pascal's Triangle

Felicia Zhang
Sarah Coffen

|#


(set-gag-mode nil)
:brr t

#|
Pascal's triangle is a symmetric triangle of nats, where each subsequent
row of the triangle has a length of one longer than the row below it. Each row
starts and ends with a 1, and each value in the triangle is the sum of the two 
numbers below it, as described here: https://www.mathsisfun.com/pascals-triangle.html

In our representation, Pascal's triangle is represented as a list of list of nats,
for instance: (pascal-triangle 4) => ((1 3 3 1) (1 2 1) (1 1) (1))
|#

(defdata lon (listof nat))
(defdata llon (listof lon))
(defdata memo-table (map nat lon))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; TRIANGULAR SEQUENCE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper for generating the triangular sequence
(definec triangular-seq-h (n :nat m :nat a :nat) :lon
  (if (zp n)
    '()
    (cons (+ a m) (triangular-seq-h (1- n) (1+ m) (+ a m)))))

;; Returns a list of n numbers that are the first n numbers of the triangular sequence
;; 1, 3, 6, 10...
(definec triangular-seq (n :nat) :lon
  (triangular-seq-h n 1 0))


(check= (triangular-seq 0) '())
(check= (triangular-seq 1) '(1))
(check= (triangular-seq 4) '(1 3 6 10))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; PASCAL'S TRIANGLE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper for new-row. Generates the next row of a pascal's triangle given the previous row,
;; without the leading 1. Each value is the sum of the the two values "below" it in the previous row
(definec row-helper (prev-row :lon) :lon
  (cond ((endp prev-row) nil)
        ((endp (cdr prev-row)) '(1))
        (t (cons (+ (car prev-row) (cadr prev-row))
                 (row-helper (cdr prev-row))))))

;; Creates the next row of pascal's triangle given the triangle so far, where the row starts
;; and ends with 1s, and each value is the sum of the the two values "below" it in the previous row
(definec new-row (triangle-list :llon) :lon
  (cons 1 (row-helper (car triangle-list))))

;; measure function for pascal-triangle
(definec measure-pt (n :nat) :nat
  n)#|ACL2s-ToDo-Line|#


;; Creates a Pascal's triangle with n rows as a list, where each element is a list
;; representing the numbers in one row of the triangle. The first item is the
;; bottom-most (longest) row of the triangle.
(definec pascal-triangle (n :nat) :llon
  (declare (xargs :measure (if (natp n) (measure-pt n) 0)))
  (cond ((zp n) '())
        (t (let ((rest-triangle (pascal-triangle (- n 1))))
                 (cons (new-row rest-triangle) rest-triangle)))))

(check= (row-helper '(1 3 3 1)) '(4 6 4 1))
(check= (row-helper '(1)) '(1))

(check= (new-row '((1 3 3 1) (1 2 1) (1 1) (1))) '(1 4 6 4 1))
(check= (new-row '((1))) '(1 1))

(check= (pascal-triangle 0) '())
(check= (pascal-triangle 1) '((1)))
(check= (pascal-triangle 2) '((1 1) (1)))
(check= (pascal-triangle 5) '((1 4 6 4 1) (1 3 3 1) (1 2 1) (1 1) (1)))


;;;;;;;;;;;;;;;;;;;;;;;;; PASCAL'S TRIANGLE WITH ACCUMULATOR ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definec pascal-triangle-acc-h (n :nat acc :llon) :llon
  (if (zp n)
    acc
    (pascal-triangle-acc-h (- n 1) (cons (new-row acc) acc))))

;; Creates a Pascal's triangle with n rows as a list, where each element is a list
;; representing the numbers in one row of the triangle. The first item is the
;; bottom-most (longest) row of the triangle.
;; Is equivalent to pascal-triangle, but uses an accumulator
(definec pascal-triangle-acc (n :nat) :llon
  (pascal-triangle-acc-h n '()))

(check= (pascal-triangle-acc 0) '())
(check= (pascal-triangle-acc 1) '((1)))
(check= (pascal-triangle-acc 2) '((1 1) (1)))
(check= (pascal-triangle-acc 5) '((1 4 6 4 1) (1 3 3 1) (1 2 1) (1 1) (1)))
(check= (pascal-triangle-acc 6) (pascal-triangle 6))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; LEMMATA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(defthm subgoal-aa
  (IMPLIES (AND (INTEGERP N) (<= 2 N))
         (EQUAL (NTH (+ -2 N)
                     (CONS 1 (triangular-seq-H (+ -1 N) 2 1)))
                (NTH 2
                     (CAR (PASCAL-TRIANGLE-ACC-H N '((1))))))))

(thm (implies (and (natp n) (<= 2 n))
              (equal (nth (- n 2) (triangular-seq (- n 1)))
                     (nth 2 (nth 0 (pascal-triangle-acc n))))))


(definec pascal-triangle-memo-h (n :nat m :memo-table) :llon
  (cond [(zp n) '()]
        [(in n m) (cons (lookup n m) (pascal-triangle-memo-h (- n 1) m))]
    



(definec pascal-triangle-memo (n :nat) :llon
  (pascal-triangle-memo-h n '()))
|#
  

;; For n<2, the output of pascal-triangle doesn't have the third row and is comprised only of 1's
;; n = 0, ((1)); n = 1,((1 1) (1))
#|
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
              (equal (triangular-seq n) (triangular-seq-h n 1 0))))

(defthm main-base
  (implies (and (natp n) (equal 2 n))
           (equal (nth 0 (triangular-seq 1))
                  (nth 2 (nth 0 (pascal-triangle 2))))))

(test? (IMPLIES (AND (INTEGERP N)
              (<= 0 N)
              (NOT (ZP N))
              (IMPLIES (AND (NATP (+ -1 N)) (<= 2 (+ -1 N)))
                       (EQUAL (NTH (+ -2 -1 N)
                                   (triangular-seq (+ -1 -1 N)))
                              (NTH 2 (NTH 0 (PASCAL-TRIANGLE (+ -1 N))))))
              (<= 2 N))
         (EQUAL (NTH (+ -2 N) (triangular-seq (+ -1 N)))
                (NTH 2 (NTH 0 (PASCAL-TRIANGLE N))))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; MAIN THEOREMS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
THEOREM: two functions that generate Pascal's triangle, one purely recursive and one
using an accumulator, are equivalent.
|#
(thm (implies (natp n)
              (equal (pascal-triangle n) (pascal-triangle-acc n))))

#|
THEOREM: the value in the third diagonal of Pascal's triangle (the triangular numbers)
of a given row is the same as the last number from the list returned by the triangular-seq function
There must be more than 2 rows in the triangle in order to have a third triangular diagonal
|#
(thm (implies (and (natp n) (> n 2))
              (equal (nth (- n 2) (triangular-seq (- n 1)))
                     (nth 2 (nth 0 (pascal-triangle-acc n))))))
