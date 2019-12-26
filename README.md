# ml4fp2016

This repository contains 4 folders:
* baseline: the ML source code of the program synthetizer
* thesis: the LaTeX source of the thesis writeup
* test: test protocol with measured times for personal use
* Literature: contains some of the used articles and a minimal literature analysis for personal use

The baseline/zil/t folder contains tests and convenience functions to print and input terms in the new language. Some of the files are used to test if the library functions in the new language actually do what they are expected to do.

The baseline/zil/src folder contains the source code.
The files with the .tm ending are written in the new language (read thesis pdf to know more about this new language). Those are the pre-implemented library components. Parsing is done in the library.ml file. The builtin.ml is an addition to the library that uses ml addition and multiplication to increase the evaluation speed.
The actual synthetizer logic could be in program.ml. It's `compare` function lists several alternatives to guide the search using a priority queue.

