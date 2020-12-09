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

;; Creates a Pascal's triangle with n rows as a list, where each element is a list
;; representing the numbers in one row of the triangle. The first item is the
;; bottom-most (longest) row of the triangle.
(definec pascal-triangle (n :nat) :llon
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; THEOREM 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
THEOREM: two functions that generate Pascal's triangle, one purely recursive and one
using an accumulator, are equivalent.

(defthm equal-pascal
  (implies (natp n)
           (equal (pascal-triangle n) (pascal-triangle-acc n))))
|#

;; Lemma 1: Relating the accumulator to the recursive pascale triangle function
#|
(defthm equal-pascal-acc
  (implies (and (natp n) (natp c) (>= n c))
           (equal (pascal-triangle n) (pascal-triangle-acc-h c (pascal-triangle (- n c))))))

;; theorem equal-pascal as described above
(defthm equal-pascal
  (implies (natp n)
           (equal (pascal-triangle n) (pascal-triangle-acc n))))
|#



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; THEOREM 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the third diagonal of the given Pascal's triangle (the third value of every row in the triangle)
;; and returns these as a list.
;; Only triangles with more than 2 rows will have a third diagonal.
#|
THEOREM: the value in the third diagonal of Pascal's triangle (the triangular numbers)
of a given row is the same as the last number from the list returned by the triangular-seq function
There must be more than 2 rows in the triangle in order to have a third triangular diagonal

(defthm triangular-diagonal
  (implies (and (natp n) (> n 2))
           (equal (rev (triangular-seq (- n 2)))
                  (get_3rd (pascal-triangle n)))))
|#

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

(definec ts-new-h (n :nat) :nat
  (if (zp n)
    0
    (+ n (ts-new-h (- n 1)))))

(definec ts-new-list (n :nat) :lon
  (if (zp n)
    '()
    (cons (ts-new-h n) (ts-new-list (- n 1)))))

(check= (ts-new-list 0) '())
(check= (ts-new-list 1) '(1))
(check= (ts-new-list 4) '(10 6 3 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; THIRD DIAGONAL ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper for is-pascal-shape
(definec is-pascal-shape-h (tri :llon prev :nat) :bool
  (cond ((endp tri) (equal 1 prev))
        (t (and (equal (1- prev) (llen (car tri)))
                (is-pascal-shape-h (cdr tri) (llen (car tri)))))))
  
;; Determines whether the given llon is in the shape of a triangle--
;; each element in the list (each row) has length one longer then the next element
;; ending at length 0
(definec is-pascal-shape (tri :llon) :bool
  (cond ((endp tri) (equal (llen (car tri)) 0))
        (t (and (equal (llen (car tri)) (llen tri)) (is-pascal-shape (cdr tri))))))
        

(check= (is-pascal-shape (pascal-triangle 0)) t)
(check= (is-pascal-shape (pascal-triangle 4)) t)
(check= (is-pascal-shape '((1 4 1) (1 3 3 1) (1))) nil)

;;
(definec get_3rd (tri :llon) :lon
  :ic (is-pascal-shape tri)
  (cond ((< (len tri) 3) nil)
        (t (cons (nth 2 (car tri)) (get_3rd (cdr tri))))))

(check= (get_3rd (pascal-triangle 0)) '())
(check= (get_3rd (pascal-triangle 1)) '())
(check= (get_3rd (pascal-triangle 1)) '())
(check= (get_3rd (pascal-triangle 6)) '(10 6 3 1))


;; theorem triangular-diagonal as described above

#|
(defthm triangle-is-triangle
  (implies (natp n)
           (is-pascal-shape (pascal-triangle n))))
|#

; this is wrong?
#|
(defun some-induction (x)
  (or (zp x)
      (equal x 1)
      (equal x 2)
      (some-induction (- x 1))))
|#

(defun some-induction (l)
  (let ((x (len l)))
  (or (zp x)
      (equal x 1)
      (equal x 2)
      (some-induction (cdr l)))))
#|
(defthm equal-triangular-seq-ts-new-list
  (implies (natp n)
           (equal (rev (triangular-seq n)) (ts-new-list n))))
|#
#|
(defthm triangular-diagonal
  (implies (and (natp n)
                (> n 2))
           (equal (ts-new-list (- n 2))
                  (get_3rd (pascal-triangle n))))
  :hints (("Goal" :induct t)))
|#

(defthm row-helper-len
  (implies (lonp l)
           (equal (llen (row-helper l))
                  (llen l))))

(thm
  (implies (natp n)
           (let ((tri (pascal-triangle n)))
             (equal (llen (car tri)) (llen tri))))
  :hints (("Subgoal *1.1/5" :use row-helper-len)))


(defthm triangle-is-triangle
  (implies (natp n)
           (is-pascal-shape (pascal-triangle n))))

(definec last-third-diag (tri :llon) :nat
  :ic (and (> (len tri) 2) (is-pascal-shape tri))
  (nth 2 (car tri)))
#|
(defthm diag-1
  (implies (and (natp n) (not (zp n)))
           (equal (caar (pascal-triangle n)) 1)))
|#
(defthm diag-2-sum
  (implies (and (natp n) (> n 0))
           (equal (cadar (pascal-triangle (1+ n)))
                  (+ (cadar (pascal-triangle n))
                     (caar (pascal-triangle n))))))
#|
(thm
  (implies (and (natp n) (> n 0))
           (equal (cadar (pascal-triangle (1+ n)))
                  (+ (cadar (pascal-triangle n)) 1))))
|#
(defthm diag-2
  (implies (and (natp n) (> n 0))
           (equal (cadar (pascal-triangle (1+ n))) n)))

(defthm diag-3-help
  (implies (and (natp n) (> n 0))
           (equal (CAR (ROW-HELPER (CAR (PASCAL-TRIANGLE n)))) n)))

(defthm diag-3-help-2
  (implies (and (natp n) (> n 2))
           (equal (CAR (ROW-HELPER (CAR (PASCAL-TRIANGLE n)))) n)))


(defthm diag-3-pls
  (implies (and (natp n) (natp c) (> (- n c) 2))
           (equal (+ c (CAR (ROW-HELPER (CAR (PASCAL-TRIANGLE (- n c)))))) n)))
;  :hints (("Goal" :use diag-3-help-2)))

(definec triangle (n :nat) :nat
  (if (zp n)
    0
    (+ (1- n) (triangle (- n 1)))))

(check= (triangle 1) 0)
(check= (triangle 5) 10)
(check= (triangle 4) 6)
#|
(definec ind (x :nat) :bool
  :ic (> x 1)
  (or (equal x 2)
      (ind (- x 1))))
|#
(defun ind (x)
  (or (zp x)
      (equal x 1) 
      (equal x 2)
      (ind (- x 1))))#|ACL2s-ToDo-Line|#


(defthm triangular-diagonal
  (implies (and (natp n) (> n 2))
           (equal (triangle n)
                  (last-third-diag (pascal-triangle (+ 1 n)))))
  :hints (("Goal" :induct (ind n))))
 ; :hints (("Subgoal *1/5.2.3.2''" :use diag-3-pls)))
  
(defthm triangular-diagonal
  (implies (and (natp n) (> n 2))
           (equal (+ (cadar (pascal-triangle n))
                     (last-third-diag (pascal-triangle n)))
                  (last-third-diag (pascal-triangle (+ 1 n))))))

(defthm row-2-sum
  (implies (and (llonp tri) (is-pascal-shape tri) (> (llen tri) 2))
           (equal (nth 2 (new-row tri)) (+ (nth 1 (car tri)) (nth 2 (car tri))))))

(defthm test
  (implies (natp n)
           (equal (new-row (pascal-triangle n)) (car (pascal-triangle (1+ n))))))

(defthm row-2-sum-2
  (implies (and (llonp tri) (is-pascal-shape tri) (> (llen tri) 2))
           (equal (last-third-diag (cons (new-row tri) tri)) (+ (nth 1 (car tri)) (nth 2 (car tri))))))
#|
(defthm pascal
  (implies (implies (and (natp n) (> n 2))
                    (and (llonp (pascal-triangle n))
                         (is-pascal-shape (pascal-triangle n))
                         (> (llen (pascal-triangle n)) 2)))
           (equal (+ (nth 1 (car (pascal-triangle n))) (nth 2 (car (pascal-triangle n))))
                  (last-third-diag (pascal-triangle (1+ n))))))
|#

(thm
  (implies (and (natp n) (> n 3))
           (equal (+ (nth 1 (car (pascal-triangle n))) (nth 2 (car (pascal-triangle n))))
                  (nth 2 (car (pascal-triangle (1+ n))))))
  :hints (("Subgoal *1/2" :use ((:instance row-2-sum-2)))))


(defthm triangular-diagonal
  (implies (and (natp n) (not (zp n)))
           (equal (ts-new-h n)
                  (last-third-diag (pascal-triangle (+ 2 n))))))

(defthm triangular-diagonal
  (implies (and (natp n) (not (zp n)))
           (equal (ts-new-list n)
                  (get_3rd (pascal-triangle (+ 2 n))))))
 ; :hints (("Goal" :induct t)))
