# STAPPL: STAtically typed Probabilistic Programming Language

STAPPL is a compiler for the STAtically typed Probabilistic Programming Language.

## How to Use

Install the necessary OCaml packages:

```sh
opam install . --deps-only
```

You can run the program using the following command:

```sh
dune exec -- stappl <program.stp>
```

This will parse and compile the program, perform inference, and save the distribution plot of the final query variable as a PNG image file.

## Example

Here's an example program and its components:

### Input Program

```ocaml
# student.stp
fun determine_grade(difficult, smart) {
  if difficult = 1 & smart = 1 then 0.8
    else if difficult = 1 & smart = 0 then 0.3
    else if difficult = 0 & smart = 1 then 0.95
    else 0.5
}

let difficult = sample(bernoulli(0.4)) in
let smart = sample(bernoulli(0.3)) in
let grade = bernoulli(determine_grade(difficult, smart)) in
let sat = bernoulli(
  if smart = 1 then 0.95
    else 0.2
) in
observe(grade, 0);
observe(sat, 1);
smart
```

#### Pretty Print (-pp)

```scheme
((funs
  (((name determine_grade) (params (difficult smart))
    (body
     (If (And (Eq (Var difficult) (Int 1)) (Eq (Var smart) (Int 1)))
      (Real 0.8)
      (If (And (Eq (Var difficult) (Int 1)) (Eq (Var smart) (Int 0)))
       (Real 0.3)
       (If (And (Eq (Var difficult) (Int 0)) (Eq (Var smart) (Int 1)))
        (Real 0.95) (Real 0.5))))))))
 (exp
  (Assign difficult (Sample (Call bernoulli ((Real 0.4))))
   (Assign smart (Sample (Call bernoulli ((Real 0.3))))
    (Assign grade
     (Call bernoulli ((Call determine_grade ((Var difficult) (Var smart)))))
     (Assign sat
      (Call bernoulli ((If (Eq (Var smart) (Int 1)) (Real 0.95) (Real 0.2))))
      (Seq (Observe (Var grade) (Int 0))
       (Seq (Observe (Var sat) (Int 1)) (Var smart)))))))))
```

#### Graph Mode (-graph)

```scheme
((vertices (X1 X2 X3 X4)) (arcs ((X1 X3) (X2 X3) (X2 X4)))
 (pmdf_map
  ((X1 (Dist_obj (dist bernoulli) (var X1) (args ((Real 0.4)))))
   (X2 (Dist_obj (dist bernoulli) (var X2) (args ((Real 0.3)))))
   (X3
    (If_pred Empty
     (Dist_obj (dist bernoulli) (var X3)
      (args
       ((If (And (Eq (Var X1) (Int 1)) (Eq (Var X2) (Int 1))) (Real 0.8)
         (If (And (Eq (Var X1) (Int 1)) (Eq (Var X2) (Int 0))) (Real 0.3)
          (If (And (Eq (Var X1) (Int 0)) (Eq (Var X2) (Int 1))) (Real 0.95)
           (Real 0.5)))))))
     One))
   (X4
    (If_pred Empty
     (Dist_obj (dist bernoulli) (var X4)
      (args ((If (Eq (Var X2) (Int 1)) (Real 0.95) (Real 0.2)))))
     One))))
 (obs_map ((X3 (Int 0)) (X4 (Int 1)))))
```

#### Inference Mode

![student.png](./samples/student.png)

## License

STAPPL is available under the MIT license. See the [LICENSE](LICENSE) file for more info.

