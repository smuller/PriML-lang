# PriML-lang

This is the implementation of the PriML language. PriML is a source language for
writing fine-grained parallel programs with asynchronous computation and I/O.
It is an extension of Standard ML (and, currently, compiles to Standard ML and
uses [MLton](https://www.mlton.org) as a backend).

## Getting Started

The following instructions have been tested on Linux x64.

An existing installation of [MLton](https://www.mlton.org) 
is required to build the compiler.
See [https://github.com/MLton/mlton] for other requirements for building MLton from
source.

To build, run

    make

in the top-level directory.

**Note**: Compiling with MLton requires a lot of memory and time.

This process will produce the `primlc` executable. It can be invoked as follows:

    ./primlc <input> <output>

The output will be a stand-alone Linux executable that can be invoked on `N`
processors as follows:

    ./output <command line options> @MLton number-processors <N> --

## Compiling PriML programs

The input to `primlc` can be either a single source file with the .prm extension,
or can be a MLton Basis (.mlb) file (see <http://www.mlton.org/MLBasis>).
PriML programs can freely interface with SML code using the ML Basis system.
A .mlb file input to `primlc` can provide any number of SML files on which the
PriML program depends, but must end with exactly one .prm file. PriML currently
does not support compilation of multiple .prm files.

## Examples

Several example programs are provided in the `priml-examples` directory.
Run `make` to compile all of them. Individual make targets are also provided for
each example.

### Bank

A bank simulator (after Babaoğlu, Ö., Marzullo, K. & Schneider, F.B. A formalization of priority inversion. Real-Time Syst 5, 285–303 (1993))
that is used as an example of the utility of partially ordered priorities.

### Email client

A skeleton of an email client that can display emails, sort emails and send emails
(at differing priorities).

### Fibonacci server

Takes integers `n` on the command line and computes `fib(n)` in parallel while
responsively accepting more integers.

### Fibonacci-terminal

Computes the 45th Fibonacci numbers while echoing console input.

### Web server

Opens a simple web server (serving the page in the `www` directory) on
`localhost:8000`.

## See also

For background information on the theory behind PriML and more code and syntax
examples:

My PhD thesis, [*Responsive Parallel Computation*](http://www.cs.cmu.edu/~smuller/thesis/thesis-final.pdf)

Stefan K. Muller, Umut A. Acar and Robert Harper. Competitive Parallelism: Getting Your Priorities Right. ICFP 2018.


For algorithmic and implementation details on the runtime scheduler, and a
description of the "fairness" properties of PriML:

Stefan K. Muller, Sam Westrick and Umut A. Acar. Fairness in Responsive Parallelism. ICFP 2019.
 

