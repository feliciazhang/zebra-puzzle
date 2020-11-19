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
  (* 2 n))

(definec pascal-triangle (n :nat) :llon
  (declare (xargs :measure (if (natp n) (measure-pt n) 0)))
  (cond ((zp n) '((1)))
        (t (cons (new-row (pascal-triangle (- n 1)))
                 (pascal-triangle (- n 1))))))
