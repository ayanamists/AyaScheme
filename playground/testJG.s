global _start   

 section   .text
_start:
  mov r8, 2
  cmp r8, 1
  jg block1
  jmp block2

block2:
  mov r9, 2
  

block1:
  mov r9, 1