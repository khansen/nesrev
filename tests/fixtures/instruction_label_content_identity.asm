MACRO READ_LOCAL condition
@@t:
 IF condition
  .DB 1,2
 ELSE
  RTS
 ENDIF
 LDA @@t-1,X
ENDM
.ORG $20
choice = 0
REPT 2
 READ_LOCAL choice
 choice = choice+1
ENDM
END
