# IEEE754-rs #

The idea of IEEE754-rs is to provide a playground for making Rust the best
language there is for floating point computation on all processors. This means
that we're trying to build up a set of traits that allows you to wield the full
power of IEEE754 in Rust.

In addition we're building up a test-suite for the compiler so that we can check
the implementation on new platforms, and find issues with LLVM. As part of this
effort we're building a reference implementation of IEEE 754-2008 in software,
to check against.

Unfortunately, it is checked against the SSE implementation right now, and does
not have its own test-suite, so it kind of defeats its purpose. But it allows
some insight into how floats work.


## soft_f32 ##

The soft_f32 part of this library is based on code by John R. Hauser, made
available under the following license. The original code is available on
http://www.jhauser.us/arithmetic/SoftFloat.html.

```
This C source file is part of the SoftFloat IEC/IEEE Floating-point Arithmetic
Package, Release 2b.

Written by John R. Hauser.  This work was made possible in part by the
International Computer Science Institute, located at Suite 600, 1947 Center
Street, Berkeley, California 94704.  Funding was partially provided by the
National Science Foundation under grant MIP-9311980.  The original version
of this code was written as part of a project to build a fixed-point vector
processor in collaboration with the University of California at Berkeley,
overseen by Profs. Nelson Morgan and John Wawrzynek.  More information
is available through the Web page `http://www.cs.berkeley.edu/~jhauser/
arithmetic/SoftFloat.html'.

THIS SOFTWARE IS DISTRIBUTED AS IS, FOR FREE.  Although reasonable effort has
been made to avoid it, THIS SOFTWARE MAY CONTAIN FAULTS THAT WILL AT TIMES
RESULT IN INCORRECT BEHAVIOR.  USE OF THIS SOFTWARE IS RESTRICTED TO PERSONS
AND ORGANIZATIONS WHO CAN AND WILL TAKE FULL RESPONSIBILITY FOR ALL LOSSES,
COSTS, OR OTHER PROBLEMS THEY INCUR DUE TO THE SOFTWARE, AND WHO FURTHERMORE
EFFECTIVELY INDEMNIFY JOHN HAUSER AND THE INTERNATIONAL COMPUTER SCIENCE
INSTITUTE (possibly via similar legal warning) AGAINST ALL LOSSES, COSTS, OR
OTHER PROBLEMS INCURRED BY THEIR CUSTOMERS AND CLIENTS DUE TO THE SOFTWARE.

Derivative works are acceptable, even for commercial purposes, so long as
(1) the source code for the derivative work includes prominent notice that
the work is derivative, and (2) the source code includes prominent notice with
these four paragraphs for those parts of this code that are retained.
```