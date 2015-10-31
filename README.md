SMT Verification for Graal Compiler
===================================

Installation
------------

This tool has been built/tested on Ubunt 14.04.
Prerequisites for build:

* Python 2.7
* Mercurial
* make/gcc
* Oracle JDK 1.8.0_40 (JAVA_HOME set)
* Boolector

Build
-----
The whole source download and subsequent building is managed by the build tool called `mx`.

1. Create a build directory `mkdir ~/graal; cd ~/graal`
2. Clone the mx repository: `hg clone https://lafo.ssw.uni-linz.ac.at/hg/mx/`
3. Add mx to the PATH: `export PATH=~/graal/mx/:$PATH`
4. Clone the Graal Verification repository: `hg clone https://bitbucket.org/sanzinger/graal-verify`
5. Set default configuration: `echo 'DEFAULT_VM=server' > ~/graal/graal-verify/mx.verify/env`
6. Change to graal-verify and start the build: `cd ~/graal/graal-verify; mx build`

Run the tests
-------------
Tests are currently run with the mx tool. The commandline requires the path to the boolector binary in the ~/graal/graal-verify directory:

`mx unittest -G:Btor=/path/to/boolector IntExamples`