	.text
	.p2align	5
	.globl	_ECRYPT_keysetup
	.globl	ECRYPT_keysetup
_ECRYPT_keysetup:
ECRYPT_keysetup:
	pushq	%rbp
	pushq	%rdi
	pushq	%rsi
	movq	%rsi, %rax
	movq	%rdx, %rcx
	movq	%rdi, %rdx
	movq	(%rax), %rsi
	movq	8(%rax), %rdi
	movq	%rsi, 4(%rdx)
	movq	%rdi, 12(%rdx)
	cmpq	$256, %rcx
	jnb 	L1
	movq	(%rax), %rcx
	movq	8(%rax), %rax
	movq	%rcx, 44(%rdx)
	movq	%rax, 52(%rdx)
	movq	$1634760805, %rax
	movq	$824206446, %rax
	movq	$2036477238, %rax
	movq	$1797285236, %rax
	jmp 	L2
L1:
	movq	16(%rax), %rcx
	movq	24(%rax), %rax
	movq	%rcx, 44(%rdx)
	movq	%rax, 52(%rdx)
	movq	$1634760805, %rax
	movq	$857760878, %rax
	movq	$2036477234, %rax
	movq	$1797285236, %rax
L2:
	popq	%rsi
	popq	%rdi
	popq	%rbp
	ret 
