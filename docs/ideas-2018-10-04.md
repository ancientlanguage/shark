# Shark Language Ideas

## Types

### Unit -- 1 possible value (unit)

Value : Type

u : U

cardinality (Unit) = 1

### Sum -- A + B
`A + B` read as "A or B" where `A` and `B` are types.

`A + B + C + D`

cardinality (A + B) = cardinality (A) + cardinality (B)


Want: Cardinality 3
Answer: U + U + U
        1 + 1 + 1 = 3

### Product -- A * B
A product is also a pair. `A * B` can be read "A and B".

cardinality of `A * B` = cardinality of `A` * cardinality of `B`

### Exponent -- A ^ B
An exponent can be thought of as an array.
`A ^ B` would be an array of cardinality `B` copies of `A` or in another notation `A[B]`.

Byte: Cardinality 256 (8 bits where a bit has cardinality 2, so 2 ^ 8)

Byte as an array:
[b, b, b, b, b, b, b, b] where b is 0 or 1

Bit = U + U

Byte = Bit ^ (U + U + U + U + U + U + U + U)

File of length cardinality (`C`) = Byte ^ C

ASCII = Bit ^ 7

Bit ^ 8 <-> Bit ^ 1 * Bit ^ 7

Bit ^ 1 * Bit ^ 7 -> Error + Bit ^ 7

AABB

Big endian
Byte[2]
AA BB
Byte[0] = AA
Byte[1] = BB

Little endian
BB AA
Byte[0] = BB
Byte[1] = AA

ASCII : 0-127
peeling off the most significant bit
Bit[8]
peel off bit Bit[7]
validate that it is always 0

Bit[8] -> Bit[1] * Bit[7]

2 * Bit[7] <-> Error + Bit[7]
256 -> Bit[7] + 128

00000000
10000000

00000001
10000001

Give me a byte.
Is it ASCII?

top bit must be 0.

No, the top bit is 1, and the lower 7 bits are: 0000000.

(Bit[8]) [1,000,000] -> Error + (Bit[7]) [1,000,000]

2 ^ 8 ^ 1,000,000 = x + 2 ^ 7 ^ 1,000,000


(Bit[8]) [1,000,000] -> (Error + Bit[7]) [1,000,000]
(x + y) ^ z -> f (x) + y ^ z
solve for f

Error : byte 96 is not ASCII, because it's top bit is set, and it's lower 7 bits are: BBBBBBB.
(Bit[7] + Bit[7]) [1,000,000] -> Bit[7] ^ 1,000,000 + Bit[7] ^ 1,000,000


## MVP1
1. Load a file from GitHub. Reason/React async call to GitHub https
2. Some visualization of byte values: Table, Graph, Bar chart

`Bit ^ 8 ^ (file length)`

## MVP2
1. Define mappings/transformation
2. Visualize the mapping
3. "Execute" the mapping

## MVP3
1. Similar to MVP2 but with a focus on validation and error message

## MVP4
1. Iterating MVP2 and MVP3, and making that convenient for our purposes (grammatical analysis)
