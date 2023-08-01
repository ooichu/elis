# elis
Embeddable Lisp-like programming language written in ANSI C.

Basically, it's [fe](https://github.com/rxi/fe) with some improvements that conflict with original design.

What's new:
* endian independent implementation
* new builtins: `eval`, `apply`, `gensym`, `%` (modulo) and `//` (integer division)
* new library functions: `elis_apply()`, `elis_setcar()`, `elis_setcdr()` and `elis_is()`
* new type: userdata
* unpacking and multiple forms for `=` and `let`
* number of available objects can grow at runtime 
* strings now are ordinary null-terminated C strings
* implementation is fully compatible with C++
* compile-time configuration options: `ELIS_STACK_SIZE`, `ELIS_NUMBER_TYPE` and other
* some fixes and little improvements
