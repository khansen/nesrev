# NESrev

## Build it

   make

## Run it

   java -cp . NESrev prg/BalloonFight.prg > BalloonFight.asm

## Using a codepointers configuration file

A codepointers configuration file is a CSV file that defines addresses that should be
treated as code pointers (AKA "jump tables"). This can be used to help the disassembler
when it isn't able to infer that these addresses contain code pointers, via static
analysis.

Example configuration:

    start|count
    0x03AB|5

This defines a table starting at offset 0x03AB, consisting of 5 pointers.

## Assemble the disassembly again

   xasm BalloonFight.asm --pure-binary

