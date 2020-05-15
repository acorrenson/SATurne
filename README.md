![logo](planet.png)

# SATurne

**SATurne** is a simple functional style SAT solver written in [Coq](https://coq.inria.fr/). Its design is strongly inspired by [this article](http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html). It is a tiny solver. It is absolutely not designed for performances or scalability, but its minimalist functional structure makes him easy to manipulate inside Coq. The opportunity was so beautiful so I decided to provide a verified implementation of this solver.

## Why Coq ?

Coq is a powerful proof-assistant. More than a logical framework to develop proofs, it also provides a complete functional programming language (in the style of OCaml). This particularity allows to develop robust programs and their proofs at the same time.

## Project status

+ [x] core algorithm
+ [x] termination proof
+ [ ] correctness proof (this is really not trivial, any help is welcomed :) )




