# gosper

#### Continued Fraction Arithmetic

This library implements several methods for arbitrary precision continued
fraction arithmetic based on Bill Gosper's inspired preprint work in the 2nd
appendix of the MIT HAKMEM publication[^1], where he writes:

>> [Abstract](https://perl.plover.com/classes/cftalk/INFO/gosper.txt): Contrary
>> to everybody, [...] continued fractions are not only perfectly amenable to
>> arithmetic, they are amenable to perfect arithmetic.

He then goes on to describe an algorithm for producing a continued fraction
representing arithmetic operations (+, -, *, /) between arbitrary continued
fractions.

The main benefit of this approach is that even if the operands have **infinite
terms** (such as representations of transcendental numbers, e.g π), consuming enough
terms of the operands can bound the next term of the result to within an integer
range.

In this way, the terms of the result can be read off one at a time, and
computation can be discontinued when the desired accuracy is attained.
