	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_fe25519_add
	.globl	crypto_sign_ed25519_amd64_64_fe25519_add
_crypto_sign_ed25519_amd64_64_fe25519_add:
crypto_sign_ed25519_amd64_64_fe25519_add:
	pushq	%rbp
	pushq	%rsi
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %rsi
	addq	(%rdx), %rax
	adcq	8(%rdx), %rcx
	adcq	16(%rdx), %r8
	adcq	24(%rdx), %rsi
	movq	$0, %rdx
	movq	$38, %r9
	cmovnbq	%rdx, %r9
	addq	%r9, %rax
	adcq	%rdx, %rcx
	adcq	%rdx, %r8
	adcq	%rdx, %rsi
	cmovbq	%r9, %rdx
	addq	%rdx, %rax
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
