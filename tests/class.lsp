;
; Simple closure based OOP.
; You can extend this example to get `instanceof`, multiple inheritance and etc.
;

(= class (macro body
  (list 'func 'args
    ; declare `self` and `super`
    '(let self nil super nil)
    ; put class definition
    (cons 'let body)
    ; instance initialization
    '(do
      ; define `self` dispatcher
      (= self (func (method . args)
        (let local (eval method))
        (if local
          (apply local args)
          (apply super (cons method args))
        )
      ))
      ; call `init` constructor
      (apply init args)
      ; return `self` dispatcher
      self
    )
  )
))

;
; Example
;

(= Person (class
  :name "unknown"
  :get-name (func (name) :name)
  init (func (name)
    (= :name name)
  )
  :greet (func () 
    (print "Hello, my name is" :name)
  )
))

(= Employee (class
  :post "none"
  init (func (name post)
    (= super (Person name) :post post)
  )
  :greet (func ()
    (super':greet)
    (print (super':get-name) "is" :post)
  )
  :work (func ()
    (print (super':get-name) "working hard...")
  )
))

(= man1 (Employee "Rayan" "programmer")
   man2 (Person   "Nicolas")
)

(man1':greet)
(man1':work)

(man2':greet)
(man2':work) ; here you got an error
