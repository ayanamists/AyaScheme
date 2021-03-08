	.file	"testAnd.cpp"
	.text
	.globl	_Z1fbbb
	.type	_Z1fbbb, @function
_Z1fbbb:
.LFB0:
	.cfi_startproc
	endbr64
	testb	%sil, %dl
	je	.L7
	movl	$12312, %eax
	testb	%dil, %dil
	jne	.L1
.L7:
	cmpb	$1, %sil
	je	.L8
	movl	$12312, %eax
	testb	%dil, %dil
	jne	.L1
.L8:
	movl	$323, %eax
.L1:
	ret
	.cfi_endproc
.LFE0:
	.size	_Z1fbbb, .-_Z1fbbb
	.globl	_Z2f1ii
	.type	_Z2f1ii, @function
_Z2f1ii:
.LFB1:
	.cfi_startproc
	endbr64
	cmpl	%esi, %edi
	setge	%al
	movzbl	%al, %eax
	ret
	.cfi_endproc
.LFE1:
	.size	_Z2f1ii, .-_Z2f1ii
	.ident	"GCC: (Ubuntu 9.3.0-17ubuntu1~20.04) 9.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	 1f - 0f
	.long	 4f - 1f
	.long	 5
0:
	.string	 "GNU"
1:
	.align 8
	.long	 0xc0000002
	.long	 3f - 2f
2:
	.long	 0x3
3:
	.align 8
4:
