MACRO READ_BACK target
    LDA target-1,X
ENDM
.ORG $20
RAM_Buffer .EQU $0200
Alias:
Table: .DB 1,2,3,4
Words: .DW $1234
CodeEntry:
    RTS
Reader:
    LDA Table-3,X
    LDA Alias-$03,Y
    LDA [Table-1],Y
    LDA [Alias-2,X]
    CMP Words-1,Y
    LDA RAM_Buffer-1,X
    LDA CodeEntry-1,X
    LDA Table+1,X
    LDA Table-1
    LDA Table-17,X
    LDA Table-(1+1),X
    LDA Table+(-1),X
    READ_BACK Table
    REPT 2
        LDA Table-2,X
    ENDM
    IF 0
        LDA Table-4,X
    ENDIF
First:
@@row: .DB 1,2
    LDA @@row-1,X
Second:
@@row: RTS
    LDA @@row-1,X
    LDA Table-1,X : LDX Table-2,Y
END
