.global print_int0
print_int0:
mv a6, a0
li a0, 0
li a1, 20
li a2, 3
li a3, 33
li a4, -1
li a5, 0
li a7, 222
ecall
.itoa:
mv a1, a0
li a2, 1
bge a6, zero, .skip_negative_s_routine
li t0, 45
sd t0, (a0)
addi a0, a0, 1
addi a2, a2, 1
neg a6, a6
.skip_negative_s_routine:
li t0, 19
li t2, 1000000000000000000
li t4, 10
.itoa_loop1:
beq t0, zero, .zero_case
div t3, a6, t2
div t2, t2, t4
addi t0, t0, -1
beq t3, zero, .itoa_loop1
add a2, a2, t0
addi t5, t3, 48
sd t5, (a0)
addi a0, a0, 1
.itoa_loop2:
mul t1, t2, t4
mul t5, t3, t1
sub a6, a6, t5
beq t0, zero, .print
div t3, a6, t2
div t2, t2, t4
addi t5, t3, 48
sd t5, (a0)
addi a0, a0, 1
addi t0, t0, -1
j .itoa_loop2
.zero_case:
li t3, 48
sd t3, (a0)
.print:
li a0, 1
li a7, 64
ecall
.exit:
mv a0, a1
li a1, 20
li a7, 215
ecall
ret
