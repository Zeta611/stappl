#!/bin/bash
for file in samples/*.stp; do
	dune exec -- stappl -infer $file
done
