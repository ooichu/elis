(= fib (func (n)
  (if (<= 2 n)
    (+ (fib (- n 1))
       (fib (- n 2))
    )
    n
  )
))

(print (fib 35))
