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
# example.stp
fun main() {
  let z = sample(bernoulli(0.5)) in
  let mu = (if (z = 0 - 0) then ~-.1.0 else 1.0) in
  let d = normal(mu, 0.0 +. 1.0) in
  let y = 0.5 in
  observe(d, y);
  z
}
```
#### Pretty Print (-pp)
```scheme
((funs
  (((name main) (params ())
    (body
     (Assign z (Sample (Call bernoulli ((Real 0.5))))
      (Assign mu
       (If (Eq (Var z) (Minus (Int 0) (Int 0))) (Rneg (Real 1)) (Real 1))
       (Assign d (Call normal ((Var mu) (Radd (Real 0) (Real 1))))
        (Assign y (Real 0.5) (Seq (Observe (Var d) (Var y)) (Var z))))))))))
 (exp (Call main ())))
```
#### Graph Mode
```scheme
((vertices (X1 X2)) (arcs ((bernoulli X1) (X1 X2) (normal X2)))
 (det_map
  ((X1 (Dist_obj (dist bernoulli) (var X1) (args ((Real 0.5)))))
   (X2
    (If_pred Empty
     (Dist_obj (dist normal) (var X2)
      (args
       ((If (Eq (Var X1) (Minus (Int 0) (Int 0))) (Rneg (Real 1)) (Real 1))
        (Radd (Real 0) (Real 1)))))
     One))))
 (obs_map ((X2 (Real 0.5)))))
```
#### Inference Mode
The output will be the distribution of `z` and its plot saved as `example.png`.

## License
STAPPL is available under the MIT license. See the [LICENSE](LICENSE) file for more info.