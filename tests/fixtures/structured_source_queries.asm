Cell .EQU $40
Alias .EQU $40
ValueMask .EQU $40
PrgCell .EQU $6000
Count .EQU (Target-Table)/2
CodeAlias .EQU ViaEquTarget
.ORG $C000
Entry:
    LDA Cell
    STA Alias
    INC Cell
    LDA Cell,X
    LDA $3F,X
    LDA $FF,X
    LDA $5FFF,Y
    LDA PrgCell
    LDA [$FF],Y
    LDA [$FE,X]
    LDX #Count
    CMP #(Target-Table)
    LDA #<Table
    LDA Table,X
    CMP #ValueMask
    BNE BranchOnly
    JSR Called
    JMP Done
BranchOnly:
    NOP
Called:
    RTS
TakenOnly:
    RTS
Unused:
    RTS
Done:
    RTS
Table:
    .DB 1,2,3,4
Target:
    .DB 5
Pointers:
    .DW TakenOnly,Cell,Cell+ValueMask,Target-Table
.ORG $C000
Overlaid:
    JSR Called
    RTS
WrapAccess:
    LDA $FFFF,X
    LDA #<ValueMask
    JSR CodeAlias
RepeatCalls:
    JSR RepeatedCallee
    JSR RepeatedCallee
RepeatedCallee:
    RTS
ViaEquTarget:
    RTS
Field .EQU 1
ComplexFieldUse:
    STA Cell+Field,X

; Header for the first routine.
    ; Continuation of its header.
HeaderOne:
    RTS
; Header for the next routine.
HeaderTwo:
    RTS
; Detached comment.

WithoutHeader:
    RTS
DisplacedCell .EQU $0400
DisplacedUse:
    LDA DisplacedCell+1
