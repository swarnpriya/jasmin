	.text
	.p2align	5
	.globl	_ECRYPT_ivsetup
	.globl	ECRYPT_ivsetup
_ECRYPT_ivsetup:
ECRYPT_ivsetup:
	pushq	%rbp
	movq	%rsi, %rax
	movq	%rdi, %rcx
	movq	(%rax), %rax
	movq	$0, %rdx
	movq	%rax, 24(%rcx)
	movq	%rdx, 32(%rcx)
	popq	%rbp
	ret 
